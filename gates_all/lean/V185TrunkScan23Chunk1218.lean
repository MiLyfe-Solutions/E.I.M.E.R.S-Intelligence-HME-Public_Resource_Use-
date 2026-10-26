import V185TrunkScan23Chunk1217

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7217488 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4]
def baseStart_7217488 : Nat := 118140960795 + 7217488 * 2 ^ 59
def prefixEnd_7217488 : Nat := 4983230072969 + 3 ^ 40 * 7217488 * 2
def baseEnd_7217488 : Nat := 3706040462057762778707383

theorem tailTrace_7217488 : CollatzResearch.WordTrace tailWord_7217488 prefixEnd_7217488 3706040462057762778707383 := by
  unfold tailWord_7217488
  simp only [CollatzResearch.WordTrace]
  refine ⟨131621706838140549829662559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175495609117520733106216745 131621706838140549829662559)
  ·
    refine ⟨197432560257210824744493839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131621706838140549829662559 197432560257210824744493839)
    ·
      refine ⟨296148840385816237116740759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197432560257210824744493839 296148840385816237116740759)
      ·
        refine ⟨444223260578724355675111139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296148840385816237116740759 444223260578724355675111139)
        ·
          refine ⟨666334890868086533512666709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444223260578724355675111139 666334890868086533512666709)
          ·
            refine ⟨7808612002360389064601563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 666334890868086533512666709 7808612002360389064601563)
            ·
              refine ⟨11712918003540583596902345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808612002360389064601563 11712918003540583596902345)
              ·
                refine ⟨8784688502655437697676759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11712918003540583596902345 8784688502655437697676759)
                ·
                  refine ⟨13177032753983156546515139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784688502655437697676759 13177032753983156546515139)
                  ·
                    refine ⟨19765549130974734819772709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13177032753983156546515139 19765549130974734819772709)
                    ·
                      refine ⟨3706040462057762778707383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19765549130974734819772709 3706040462057762778707383)
                      ·
                        rfl

theorem cell23_7217488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_7217488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217488 prefixEnd_7217488 := by exact prefixLift 7217488
  have htrace : WordTrace (prefixWord ++ tailWord_7217488) baseStart_7217488 baseEnd_7217488 := by
    simpa [prefixWord, tailWord_7217488, baseEnd_7217488] using wordTrace_append hprefix tailTrace_7217488
  have hstable : (prefixWord ++ tailWord_7217488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217488).length < 2 ^ (prefixWord ++ tailWord_7217488).sum := by decide
  have hdescent : baseEnd_7217488 < baseStart_7217488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217491 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 3]
def baseStart_7217491 : Nat := 118140960795 + 7217491 * 2 ^ 59
def prefixEnd_7217491 : Nat := 4983230072969 + 3 ^ 40 * 7217491 * 2
def baseEnd_7217491 : Nat := 3706042002499726266969869

theorem tailTrace_7217491 : CollatzResearch.WordTrace tailWord_7217491 prefixEnd_7217491 3706042002499726266969869 := by
  unfold tailWord_7217491
  simp only [CollatzResearch.WordTrace]
  refine ⟨263243523095270231171684327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175495682063513487447789551 263243523095270231171684327)
  ·
    refine ⟨394865284642905346757526491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263243523095270231171684327 394865284642905346757526491)
    ·
      refine ⟨592297926964358020136289737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394865284642905346757526491 592297926964358020136289737)
      ·
        refine ⟨444223445223268515102217303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592297926964358020136289737 444223445223268515102217303)
        ·
          refine ⟨666335167834902772653325955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444223445223268515102217303 666335167834902772653325955)
          ·
            refine ⟨999502751752354158979988933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666335167834902772653325955 999502751752354158979988933)
            ·
              refine ⟨187406765953566404808747925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 999502751752354158979988933 187406765953566404808747925)
              ·
                refine ⟨8784692154073425225410059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187406765953566404808747925 8784692154073425225410059)
                ·
                  refine ⟨13177038231110137838115089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784692154073425225410059 13177038231110137838115089)
                  ·
                    refine ⟨9882778673332603378586317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13177038231110137838115089 9882778673332603378586317)
                    ·
                      refine ⟨3706042002499726266969869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9882778673332603378586317 3706042002499726266969869)
                      ·
                        rfl

theorem cell23_7217491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_7217491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217491 prefixEnd_7217491 := by exact prefixLift 7217491
  have htrace : WordTrace (prefixWord ++ tailWord_7217491) baseStart_7217491 baseEnd_7217491 := by
    simpa [prefixWord, tailWord_7217491, baseEnd_7217491] using wordTrace_append hprefix tailTrace_7217491
  have hstable : (prefixWord ++ tailWord_7217491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217491).length < 2 ^ (prefixWord ++ tailWord_7217491).sum := by decide
  have hdescent : baseEnd_7217491 < baseStart_7217491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217522 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_7217522 : Nat := 118140960795 + 7217522 * 2 ^ 59
def prefixEnd_7217522 : Nat := 4983230072969 + 3 ^ 40 * 7217522 * 2
def baseEnd_7217522 : Nat := 3706057920400015645682227

theorem tailTrace_7217522 : CollatzResearch.WordTrace tailWord_7217522 prefixEnd_7217522 3706057920400015645682227 := by
  unfold tailWord_7217522
  simp only [CollatzResearch.WordTrace]
  refine ⟨65811163439539480866515705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175496435838771948977375213 65811163439539480866515705)
  ·
    refine ⟨49358372579654610649886779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65811163439539480866515705 49358372579654610649886779)
    ·
      refine ⟨74037558869481915974830169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49358372579654610649886779 74037558869481915974830169)
      ·
        refine ⟨55528169152111436981122627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74037558869481915974830169 55528169152111436981122627)
        ·
          refine ⟨83292253728167155471683941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55528169152111436981122627 83292253728167155471683941)
          ·
            refine ⟨15617297574031341650940739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83292253728167155471683941 15617297574031341650940739)
            ·
              refine ⟨23425946361047012476411109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15617297574031341650940739 23425946361047012476411109)
              ·
                refine ⟨4392364942696314839327083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23425946361047012476411109 4392364942696314839327083)
                ·
                  refine ⟨6588547414044472258990625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392364942696314839327083 6588547414044472258990625)
                  ·
                    refine ⟨4941410560533354194242969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588547414044472258990625 4941410560533354194242969)
                    ·
                      refine ⟨3706057920400015645682227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941410560533354194242969 3706057920400015645682227)
                      ·
                        rfl

theorem cell23_7217522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_7217522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217522 prefixEnd_7217522 := by exact prefixLift 7217522
  have htrace : WordTrace (prefixWord ++ tailWord_7217522) baseStart_7217522 baseEnd_7217522 := by
    simpa [prefixWord, tailWord_7217522, baseEnd_7217522] using wordTrace_append hprefix tailTrace_7217522
  have hstable : (prefixWord ++ tailWord_7217522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217522).length < 2 ^ (prefixWord ++ tailWord_7217522).sum := by decide
  have hdescent : baseEnd_7217522 < baseStart_7217522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217548 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 3, 3, 2]
def baseStart_7217548 : Nat := 118140960795 + 7217548 * 2 ^ 59
def prefixEnd_7217548 : Nat := 4983230072969 + 3 ^ 40 * 7217548 * 2
def baseEnd_7217548 : Nat := 3706071270897032543957107

theorem tailTrace_7217548 : CollatzResearch.WordTrace tailWord_7217548 prefixEnd_7217548 3706071270897032543957107 := by
  unfold tailWord_7217548
  simp only [CollatzResearch.WordTrace]
  refine ⟨131622801028031864953254649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175497068037375819937672865 131622801028031864953254649)
  ·
    refine ⟨98717100771023898714940987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131622801028031864953254649 98717100771023898714940987)
    ·
      refine ⟨148075651156535848072411481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98717100771023898714940987 148075651156535848072411481)
      ·
        refine ⟨111056738367401886054308611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148075651156535848072411481 111056738367401886054308611)
        ·
          refine ⟨166585107551102829081462917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111056738367401886054308611 166585107551102829081462917)
          ·
            refine ⟨31234707665831780452774297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166585107551102829081462917 31234707665831780452774297)
            ·
              refine ⟨23426030749373835339580723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31234707665831780452774297 23426030749373835339580723)
              ·
                refine ⟨35139046124060753009371085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23426030749373835339580723 35139046124060753009371085)
                ·
                  refine ⟨13177142296522782378514157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35139046124060753009371085 13177142296522782378514157)
                  ·
                    refine ⟨4941428361196043391942809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13177142296522782378514157 4941428361196043391942809)
                    ·
                      refine ⟨3706071270897032543957107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941428361196043391942809 3706071270897032543957107)
                      ·
                        rfl

theorem cell23_7217548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_7217548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217548 prefixEnd_7217548 := by exact prefixLift 7217548
  have htrace : WordTrace (prefixWord ++ tailWord_7217548) baseStart_7217548 baseEnd_7217548 := by
    simpa [prefixWord, tailWord_7217548, baseEnd_7217548] using wordTrace_append hprefix tailTrace_7217548
  have hstable : (prefixWord ++ tailWord_7217548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217548).length < 2 ^ (prefixWord ++ tailWord_7217548).sum := by decide
  have hdescent : baseEnd_7217548 < baseStart_7217548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217591 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_7217591 : Nat := 118140960795 + 7217591 * 2 ^ 59
def prefixEnd_7217591 : Nat := 4983230072969 + 3 ^ 40 * 7217591 * 2
def baseEnd_7217591 : Nat := 3706093350565175875719409

theorem tailTrace_7217591 : CollatzResearch.WordTrace tailWord_7217591 prefixEnd_7217591 3706093350565175875719409 := by
  unfold tailWord_7217591
  simp only [CollatzResearch.WordTrace]
  refine ⟨263247170394907948250324627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175498113596605298833549751 263247170394907948250324627)
  ·
    refine ⟨394870755592361922375486941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263247170394907948250324627 394870755592361922375486941)
    ·
      refine ⟨148076533347135720890807603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394870755592361922375486941 148076533347135720890807603)
      ·
        refine ⟨222114800020703581336211405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148076533347135720890807603 222114800020703581336211405)
        ·
          refine ⟨83293050007763843001079277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222114800020703581336211405 83293050007763843001079277)
          ·
            refine ⟨31234893752911441125404729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83293050007763843001079277 31234893752911441125404729)
            ·
              refine ⟨23426170314683580844053547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31234893752911441125404729 23426170314683580844053547)
              ·
                refine ⟨35139255472025371266080321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23426170314683580844053547 35139255472025371266080321)
                ·
                  refine ⟨26354441604019028449560241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35139255472025371266080321 26354441604019028449560241)
                  ·
                    refine ⟨19765831203014271337170181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26354441604019028449560241 19765831203014271337170181)
                    ·
                      refine ⟨3706093350565175875719409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19765831203014271337170181 3706093350565175875719409)
                      ·
                        rfl

theorem cell23_7217591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_7217591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217591 prefixEnd_7217591 := by exact prefixLift 7217591
  have htrace : WordTrace (prefixWord ++ tailWord_7217591) baseStart_7217591 baseEnd_7217591 := by
    simpa [prefixWord, tailWord_7217591, baseEnd_7217591] using wordTrace_append hprefix tailTrace_7217591
  have hstable : (prefixWord ++ tailWord_7217591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217591).length < 2 ^ (prefixWord ++ tailWord_7217591).sum := by decide
  have hdescent : baseEnd_7217591 < baseStart_7217591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217594 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_7217594 : Nat := 118140960795 + 7217594 * 2 ^ 59
def prefixEnd_7217594 : Nat := 4983230072969 + 3 ^ 40 * 7217594 * 2
def baseEnd_7217594 : Nat := 3706094891007139363981895

theorem tailTrace_7217594 : CollatzResearch.WordTrace tailWord_7217594 prefixEnd_7217594 3706094891007139363981895 := by
  unfold tailWord_7217594
  simp only [CollatzResearch.WordTrace]
  refine ⟨65811819953474269940670959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175498186542598053175122557 65811819953474269940670959)
  ·
    refine ⟨98717729930211404911006439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65811819953474269940670959 98717729930211404911006439)
    ·
      refine ⟨148076594895317107366509659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98717729930211404911006439 148076594895317107366509659)
      ·
        refine ⟨222114892342975661049764489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148076594895317107366509659 222114892342975661049764489)
        ·
          refine ⟨166586169257231745787323367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222114892342975661049764489 166586169257231745787323367)
          ·
            refine ⟨249879253885847618680985051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166586169257231745787323367 249879253885847618680985051)
            ·
              refine ⟨374818880828771428021477577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249879253885847618680985051 374818880828771428021477577)
              ·
                refine ⟨281114160621578571016108183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374818880828771428021477577 281114160621578571016108183)
                ·
                  refine ⟨421671240932367856524162275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281114160621578571016108183 421671240932367856524162275)
                  ·
                    refine ⟨632506861398551784786243413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 421671240932367856524162275 632506861398551784786243413)
                    ·
                      refine ⟨3706094891007139363981895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 632506861398551784786243413 3706094891007139363981895)
                      ·
                        rfl

theorem cell23_7217594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_7217594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217594 prefixEnd_7217594 := by exact prefixLift 7217594
  have htrace : WordTrace (prefixWord ++ tailWord_7217594) baseStart_7217594 baseEnd_7217594 := by
    simpa [prefixWord, tailWord_7217594, baseEnd_7217594] using wordTrace_append hprefix tailTrace_7217594
  have hstable : (prefixWord ++ tailWord_7217594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217594).length < 2 ^ (prefixWord ++ tailWord_7217594).sum := by decide
  have hdescent : baseEnd_7217594 < baseStart_7217594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217631 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 4, 5]
def baseStart_7217631 : Nat := 118140960795 + 7217631 * 2 ^ 59
def prefixEnd_7217631 : Nat := 4983230072969 + 3 ^ 40 * 7217631 * 2
def baseEnd_7217631 : Nat := 1235371296597118573073075

theorem tailTrace_7217631 : CollatzResearch.WordTrace tailWord_7217631 prefixEnd_7217631 1235371296597118573073075 := by
  unfold tailWord_7217631
  simp only [CollatzResearch.WordTrace]
  refine ⟨263248629314763035081780747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175499086209842023387853831 263248629314763035081780747)
  ·
    refine ⟨394872943972144552622671121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263248629314763035081780747 394872943972144552622671121)
    ·
      refine ⟨296154707979108414467003341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394872943972144552622671121 296154707979108414467003341)
      ·
        refine ⟨111058015492165655425126253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296154707979108414467003341 111058015492165655425126253)
        ·
          refine ⟨41646755809562120784422345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111058015492165655425126253 41646755809562120784422345)
          ·
            refine ⟨31235066857171590588316759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41646755809562120784422345 31235066857171590588316759)
            ·
              refine ⟨46852600285757385882475139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31235066857171590588316759 46852600285757385882475139)
              ·
                refine ⟨70278900428636078823712709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46852600285757385882475139 70278900428636078823712709)
                ·
                  refine ⟨13177293830369264779446133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70278900428636078823712709 13177293830369264779446133)
                  ·
                    refine ⟨1235371296597118573073075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13177293830369264779446133 1235371296597118573073075)
                    ·
                      rfl

theorem cell23_7217631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_7217631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217631 prefixEnd_7217631 := by exact prefixLift 7217631
  have htrace : WordTrace (prefixWord ++ tailWord_7217631) baseStart_7217631 baseEnd_7217631 := by
    simpa [prefixWord, tailWord_7217631, baseEnd_7217631] using wordTrace_append hprefix tailTrace_7217631
  have hstable : (prefixWord ++ tailWord_7217631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217631).length < 2 ^ (prefixWord ++ tailWord_7217631).sum := by decide
  have hdescent : baseEnd_7217631 < baseStart_7217631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217635 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 7]
def baseStart_7217635 : Nat := 118140960795 + 7217635 * 2 ^ 59
def prefixEnd_7217635 : Nat := 4983230072969 + 3 ^ 40 * 7217635 * 2
def baseEnd_7217635 : Nat := 411790660412663744841023

theorem tailTrace_7217635 : CollatzResearch.WordTrace tailWord_7217635 prefixEnd_7217635 411790660412663744841023 := by
  unfold tailWord_7217635
  simp only [CollatzResearch.WordTrace]
  refine ⟨263248775206748543764926359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175499183471165695843284239 263248775206748543764926359)
  ·
    refine ⟨394873162810122815647389539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263248775206748543764926359 394873162810122815647389539)
    ·
      refine ⟨592309744215184223471084309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394873162810122815647389539 592309744215184223471084309)
      ·
        refine ⟨27764519260086760475207077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 592309744215184223471084309 27764519260086760475207077)
        ·
          refine ⟨5205847361266267589101327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27764519260086760475207077 5205847361266267589101327)
          ·
            refine ⟨7808771041899401383651991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205847361266267589101327 7808771041899401383651991)
            ·
              refine ⟨11713156562849102075477987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808771041899401383651991 11713156562849102075477987)
              ·
                refine ⟨17569734844273653113216981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11713156562849102075477987 17569734844273653113216981)
                ·
                  refine ⟨411790660412663744841023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17569734844273653113216981 411790660412663744841023)
                  ·
                    rfl

theorem cell23_7217635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 7].length) (baseStart_7217635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217635 prefixEnd_7217635 := by exact prefixLift 7217635
  have htrace : WordTrace (prefixWord ++ tailWord_7217635) baseStart_7217635 baseEnd_7217635 := by
    simpa [prefixWord, tailWord_7217635, baseEnd_7217635] using wordTrace_append hprefix tailTrace_7217635
  have hstable : (prefixWord ++ tailWord_7217635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217635).length < 2 ^ (prefixWord ++ tailWord_7217635).sum := by decide
  have hdescent : baseEnd_7217635 < baseStart_7217635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217651 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 4]
def baseStart_7217651 : Nat := 118140960795 + 7217651 * 2 ^ 59
def prefixEnd_7217651 : Nat := 4983230072969 + 3 ^ 40 * 7217651 * 2
def baseEnd_7217651 : Nat := 3706124159404445640969133

theorem tailTrace_7217651 : CollatzResearch.WordTrace tailWord_7217651 prefixEnd_7217651 3706124159404445640969133 := by
  unfold tailWord_7217651
  simp only [CollatzResearch.WordTrace]
  refine ⟨263249358774690578497508807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175499572516460385665005871 263249358774690578497508807)
  ·
    refine ⟨394874038162035867746263211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263249358774690578497508807 394874038162035867746263211)
    ·
      refine ⟨592311057243053801619394817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394874038162035867746263211 592311057243053801619394817)
      ·
        refine ⟨444233292932290351214546113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592311057243053801619394817 444233292932290351214546113)
        ·
          refine ⟨333174969699217763410909585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444233292932290351214546113 333174969699217763410909585)
          ·
            refine ⟨249881227274413322558182189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333174969699217763410909585 249881227274413322558182189)
            ·
              refine ⟨93705460227904995959318321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249881227274413322558182189 93705460227904995959318321)
              ·
                refine ⟨70279095170928746969488741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93705460227904995959318321 70279095170928746969488741)
                ·
                  refine ⟨13177330344549140056779139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70279095170928746969488741 13177330344549140056779139)
                  ·
                    refine ⟨19765995516823710085168709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13177330344549140056779139 19765995516823710085168709)
                    ·
                      refine ⟨3706124159404445640969133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19765995516823710085168709 3706124159404445640969133)
                      ·
                        rfl

theorem cell23_7217651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_7217651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217651 prefixEnd_7217651 := by exact prefixLift 7217651
  have htrace : WordTrace (prefixWord ++ tailWord_7217651) baseStart_7217651 baseEnd_7217651 := by
    simpa [prefixWord, tailWord_7217651, baseEnd_7217651] using wordTrace_append hprefix tailTrace_7217651
  have hstable : (prefixWord ++ tailWord_7217651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217651).length < 2 ^ (prefixWord ++ tailWord_7217651).sum := by decide
  have hdescent : baseEnd_7217651 < baseStart_7217651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217752 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 1, 1, 3]
def baseStart_7217752 : Nat := 118140960795 + 7217752 * 2 ^ 59
def prefixEnd_7217752 : Nat := 4983230072969 + 3 ^ 40 * 7217752 * 2
def baseEnd_7217752 : Nat := 3706176020950549745806169

theorem tailTrace_7217752 : CollatzResearch.WordTrace tailWord_7217752 prefixEnd_7217752 3706176020950549745806169 := by
  unfold tailWord_7217752
  simp only [CollatzResearch.WordTrace]
  refine ⟨131626521273662336373467755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175502028364883115164623673 131626521273662336373467755)
  ·
    refine ⟨197439781910493504560201633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131626521273662336373467755 197439781910493504560201633)
    ·
      refine ⟨148079836432870128420151225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197439781910493504560201633 148079836432870128420151225)
      ·
        refine ⟨111059877324652596315113419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148079836432870128420151225 111059877324652596315113419)
        ·
          refine ⟨166589815986978894472670129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111059877324652596315113419 166589815986978894472670129)
          ·
            refine ⟨124942361990234170854502597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166589815986978894472670129 124942361990234170854502597)
            ·
              refine ⟨23426692873168907035219237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124942361990234170854502597 23426692873168907035219237)
              ·
                refine ⟨4392504913719170069103607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23426692873168907035219237 4392504913719170069103607)
                ·
                  refine ⟨6588757370578755103655411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392504913719170069103607 6588757370578755103655411)
                  ·
                    refine ⟨9883136055868132655483117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6588757370578755103655411 9883136055868132655483117)
                    ·
                      refine ⟨3706176020950549745806169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9883136055868132655483117 3706176020950549745806169)
                      ·
                        rfl

theorem cell23_7217752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_7217752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217752 prefixEnd_7217752 := by exact prefixLift 7217752
  have htrace : WordTrace (prefixWord ++ tailWord_7217752) baseStart_7217752 baseEnd_7217752 := by
    simpa [prefixWord, tailWord_7217752, baseEnd_7217752] using wordTrace_append hprefix tailTrace_7217752
  have hstable : (prefixWord ++ tailWord_7217752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217752).length < 2 ^ (prefixWord ++ tailWord_7217752).sum := by decide
  have hdescent : baseEnd_7217752 < baseStart_7217752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217788 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_7217788 : Nat := 118140960795 + 7217788 * 2 ^ 59
def prefixEnd_7217788 : Nat := 4983230072969 + 3 ^ 40 * 7217788 * 2
def baseEnd_7217788 : Nat := 3706194506254111604956003

theorem tailTrace_7217788 : CollatzResearch.WordTrace tailWord_7217788 prefixEnd_7217788 3706194506254111604956003 := by
  unfold tailWord_7217788
  simp only [CollatzResearch.WordTrace]
  refine ⟨131627177787597125447623009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175502903716796167263497345 131627177787597125447623009)
  ·
    refine ⟨98720383340697844085717257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131627177787597125447623009 98720383340697844085717257)
    ·
      refine ⟨74040287505523383064287943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98720383340697844085717257 74040287505523383064287943)
      ·
        refine ⟨111060431258285074596431915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74040287505523383064287943 111060431258285074596431915)
        ·
          refine ⟨166590646887427611894647873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111060431258285074596431915 166590646887427611894647873)
          ·
            refine ⟨124942985165570708920985905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166590646887427611894647873 124942985165570708920985905)
            ·
              refine ⟨93707238874178031690739429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124942985165570708920985905 93707238874178031690739429)
              ·
                refine ⟨17570107288908380942013643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93707238874178031690739429 17570107288908380942013643)
                ·
                  refine ⟨26355160933362571413020465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17570107288908380942013643 26355160933362571413020465)
                  ·
                    refine ⟨19766370700021928559765349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26355160933362571413020465 19766370700021928559765349)
                    ·
                      refine ⟨3706194506254111604956003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19766370700021928559765349 3706194506254111604956003)
                      ·
                        rfl

theorem cell23_7217788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_7217788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217788 prefixEnd_7217788 := by exact prefixLift 7217788
  have htrace : WordTrace (prefixWord ++ tailWord_7217788) baseStart_7217788 baseEnd_7217788 := by
    simpa [prefixWord, tailWord_7217788, baseEnd_7217788] using wordTrace_append hprefix tailTrace_7217788
  have hstable : (prefixWord ++ tailWord_7217788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217788).length < 2 ^ (prefixWord ++ tailWord_7217788).sum := by decide
  have hdescent : baseEnd_7217788 < baseStart_7217788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217795 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 3]
def baseStart_7217795 : Nat := 118140960795 + 7217795 * 2 ^ 59
def prefixEnd_7217795 : Nat := 4983230072969 + 3 ^ 40 * 7217795 * 2
def baseEnd_7217795 : Nat := 3706198100618693077568471

theorem tailTrace_7217795 : CollatzResearch.WordTrace tailWord_7217795 prefixEnd_7217795 3706198100618693077568471 := by
  unfold tailWord_7217795
  simp only [CollatzResearch.WordTrace]
  refine ⟨263254610886168891090750839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175503073924112594060500559 263254610886168891090750839)
  ·
    refine ⟨394881916329253336636126259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263254610886168891090750839 394881916329253336636126259)
    ·
      refine ⟨592322874493880004954189389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394881916329253336636126259 592322874493880004954189389)
      ·
        refine ⟨222121077935205001857821021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592322874493880004954189389 222121077935205001857821021)
        ·
          refine ⟨83295404225701875696682883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222121077935205001857821021 83295404225701875696682883)
          ·
            refine ⟨124943106338552813545024325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83295404225701875696682883 124943106338552813545024325)
            ·
              refine ⟨23426832438478652539692061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124943106338552813545024325 23426832438478652539692061)
              ·
                refine ⟨8785062164429494702384523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23426832438478652539692061 8785062164429494702384523)
                ·
                  refine ⟨13177593246644242053576785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785062164429494702384523 13177593246644242053576785)
                  ·
                    refine ⟨9883194934983181540182589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13177593246644242053576785 9883194934983181540182589)
                    ·
                      refine ⟨3706198100618693077568471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9883194934983181540182589 3706198100618693077568471)
                      ·
                        rfl

theorem cell23_7217795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_7217795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217795 prefixEnd_7217795 := by exact prefixLift 7217795
  have htrace : WordTrace (prefixWord ++ tailWord_7217795) baseStart_7217795 baseEnd_7217795 := by
    simpa [prefixWord, tailWord_7217795, baseEnd_7217795] using wordTrace_append hprefix tailTrace_7217795
  have hstable : (prefixWord ++ tailWord_7217795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217795).length < 2 ^ (prefixWord ++ tailWord_7217795).sum := by decide
  have hdescent : baseEnd_7217795 < baseStart_7217795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217811 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 9]
def baseStart_7217811 : Nat := 118140960795 + 7217811 * 2 ^ 59
def prefixEnd_7217811 : Nat := 4983230072969 + 3 ^ 40 * 7217811 * 2
def baseEnd_7217811 : Nat := 1235402105436388338322799

theorem tailTrace_7217811 : CollatzResearch.WordTrace tailWord_7217811 prefixEnd_7217811 1235402105436388338322799 := by
  unfold tailWord_7217811
  simp only [CollatzResearch.WordTrace]
  refine ⟨263255194454110925823333287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175503462969407283882222191 263255194454110925823333287)
  ·
    refine ⟨394882791681166388734999931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263255194454110925823333287 394882791681166388734999931)
    ·
      refine ⟨592324187521749583102499897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394882791681166388734999931 592324187521749583102499897)
      ·
        refine ⟨444243140641312187326874923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592324187521749583102499897 444243140641312187326874923)
        ·
          refine ⟨666364710961968280990312385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444243140641312187326874923 666364710961968280990312385)
          ·
            refine ⟨499773533221476210742734289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666364710961968280990312385 499773533221476210742734289)
            ·
              refine ⟨374830149916107158057050717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499773533221476210742734289 374830149916107158057050717)
              ·
                refine ⟨140561306218540184271394019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374830149916107158057050717 140561306218540184271394019)
                ·
                  refine ⟨210841959327810276407091029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140561306218540184271394019 210841959327810276407091029)
                  ·
                    refine ⟨1235402105436388338322799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210841959327810276407091029 1235402105436388338322799)
                    ·
                      rfl

theorem cell23_7217811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_7217811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217811 prefixEnd_7217811 := by exact prefixLift 7217811
  have htrace : WordTrace (prefixWord ++ tailWord_7217811) baseStart_7217811 baseEnd_7217811 := by
    simpa [prefixWord, tailWord_7217811, baseEnd_7217811] using wordTrace_append hprefix tailTrace_7217811
  have hstable : (prefixWord ++ tailWord_7217811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217811).length < 2 ^ (prefixWord ++ tailWord_7217811).sum := by decide
  have hdescent : baseEnd_7217811 < baseStart_7217811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217846 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7217846 : Nat := 118140960795 + 7217846 * 2 ^ 59
def prefixEnd_7217846 : Nat := 4983230072969 + 3 ^ 40 * 7217846 * 2
def baseEnd_7217846 : Nat := 3706224288132072378030737

theorem tailTrace_7217846 : CollatzResearch.WordTrace tailWord_7217846 prefixEnd_7217846 3706224288132072378030737 := by
  unfold tailWord_7217846
  simp only [CollatzResearch.WordTrace]
  refine ⟨16453529438061507925053587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175504314005989417867238261 16453529438061507925053587)
  ·
    refine ⟨24680294157092261887580381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16453529438061507925053587 24680294157092261887580381)
    ·
      refine ⟨9255110308909598207842643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24680294157092261887580381 9255110308909598207842643)
      ·
        refine ⟨13882665463364397311763965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255110308909598207842643 13882665463364397311763965)
        ·
          refine ⟨5205999548761648991911487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13882665463364397311763965 5205999548761648991911487)
          ·
            refine ⟨7808999323142473487867231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205999548761648991911487 7808999323142473487867231)
            ·
              refine ⟨11713498984713710231800847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808999323142473487867231 11713498984713710231800847)
              ·
                refine ⟨17570248477070565347701271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11713498984713710231800847 17570248477070565347701271)
                ·
                  refine ⟨26355372715605848021551907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17570248477070565347701271 26355372715605848021551907)
                  ·
                    refine ⟨39533059073408772032327861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26355372715605848021551907 39533059073408772032327861)
                    ·
                      refine ⟨3706224288132072378030737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39533059073408772032327861 3706224288132072378030737)
                      ·
                        rfl

theorem cell23_7217846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7217846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217846 prefixEnd_7217846 := by exact prefixLift 7217846
  have htrace : WordTrace (prefixWord ++ tailWord_7217846) baseStart_7217846 baseEnd_7217846 := by
    simpa [prefixWord, tailWord_7217846, baseEnd_7217846] using wordTrace_append hprefix tailTrace_7217846
  have hstable : (prefixWord ++ tailWord_7217846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217846).length < 2 ^ (prefixWord ++ tailWord_7217846).sum := by decide
  have hdescent : baseEnd_7217846 < baseStart_7217846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217882 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2]
def baseStart_7217882 : Nat := 118140960795 + 7217882 * 2 ^ 59
def prefixEnd_7217882 : Nat := 4983230072969 + 3 ^ 40 * 7217882 * 2
def baseEnd_7217882 : Nat := 3706242773435634237180571

theorem tailTrace_7217882 : CollatzResearch.WordTrace tailWord_7217882 prefixEnd_7217882 3706242773435634237180571 := by
  unfold tailWord_7217882
  simp only [CollatzResearch.WordTrace]
  refine ⟨65814446009213426237291975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175505189357902469966111933 65814446009213426237291975)
  ·
    refine ⟨98721669013820139355937963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65814446009213426237291975 98721669013820139355937963)
    ·
      refine ⟨148082503520730209033906945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98721669013820139355937963 148082503520730209033906945)
      ·
        refine ⟨111061877640547656775430209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148082503520730209033906945 111061877640547656775430209)
        ·
          refine ⟨83296408230410742581572657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111061877640547656775430209 83296408230410742581572657)
          ·
            refine ⟨62472306172808056936179493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83296408230410742581572657 62472306172808056936179493)
            ·
              refine ⟨11713557407401510675533655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62472306172808056936179493 11713557407401510675533655)
              ·
                refine ⟨17570336111102266013300483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11713557407401510675533655 17570336111102266013300483)
                ·
                  refine ⟨26355504166653399019950725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17570336111102266013300483 26355504166653399019950725)
                  ·
                    refine ⟨4941657031247512316240761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26355504166653399019950725 4941657031247512316240761)
                    ·
                      refine ⟨3706242773435634237180571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941657031247512316240761 3706242773435634237180571)
                      ·
                        rfl

theorem cell23_7217882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_7217882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217882 prefixEnd_7217882 := by exact prefixLift 7217882
  have htrace : WordTrace (prefixWord ++ tailWord_7217882) baseStart_7217882 baseEnd_7217882 := by
    simpa [prefixWord, tailWord_7217882, baseEnd_7217882] using wordTrace_append hprefix tailTrace_7217882
  have hstable : (prefixWord ++ tailWord_7217882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217882).length < 2 ^ (prefixWord ++ tailWord_7217882).sum := by decide
  have hdescent : baseEnd_7217882 < baseStart_7217882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217898 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_7217898 : Nat := 118140960795 + 7217898 * 2 ^ 59
def prefixEnd_7217898 : Nat := 4983230072969 + 3 ^ 40 * 7217898 * 2
def baseEnd_7217898 : Nat := 3706250989126106174580497

theorem tailTrace_7217898 : CollatzResearch.WordTrace tailWord_7217898 prefixEnd_7217898 3706250989126106174580497 := by
  unfold tailWord_7217898
  simp only [CollatzResearch.WordTrace]
  refine ⟨65814591901198934920437587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175505578403197159787833565 65814591901198934920437587)
  ·
    refine ⟨98721887851798402380656381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65814591901198934920437587 98721887851798402380656381)
    ·
      refine ⟨37020707944424400892746143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98721887851798402380656381 37020707944424400892746143)
      ·
        refine ⟨55531061916636601339119215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37020707944424400892746143 55531061916636601339119215)
        ·
          refine ⟨83296592874954902008678823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55531061916636601339119215 83296592874954902008678823)
          ·
            refine ⟨124944889312432353013018235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83296592874954902008678823 124944889312432353013018235)
            ·
              refine ⟨187417333968648529519527353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124944889312432353013018235 187417333968648529519527353)
              ·
                refine ⟨140563000476486397139645515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187417333968648529519527353 140563000476486397139645515)
                ·
                  refine ⟨210844500714729595709468273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140563000476486397139645515 210844500714729595709468273)
                  ·
                    refine ⟨158133375536047196782101205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210844500714729595709468273 158133375536047196782101205)
                    ·
                      refine ⟨3706250989126106174580497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158133375536047196782101205 3706250989126106174580497)
                      ·
                        rfl

theorem cell23_7217898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_7217898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217898 prefixEnd_7217898 := by exact prefixLift 7217898
  have htrace : WordTrace (prefixWord ++ tailWord_7217898) baseStart_7217898 baseEnd_7217898 := by
    simpa [prefixWord, tailWord_7217898, baseEnd_7217898] using wordTrace_append hprefix tailTrace_7217898
  have hstable : (prefixWord ++ tailWord_7217898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217898).length < 2 ^ (prefixWord ++ tailWord_7217898).sum := by decide
  have hdescent : baseEnd_7217898 < baseStart_7217898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217916 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_7217916 : Nat := 118140960795 + 7217916 * 2 ^ 59
def prefixEnd_7217916 : Nat := 4983230072969 + 3 ^ 40 * 7217916 * 2
def baseEnd_7217916 : Nat := 3706260231777887104155415

theorem tailTrace_7217916 : CollatzResearch.WordTrace tailWord_7217916 prefixEnd_7217916 3706260231777887104155415 := by
  unfold tailWord_7217916
  simp only [CollatzResearch.WordTrace]
  refine ⟨131629512059365264377952801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175506016079153685837270401 131629512059365264377952801)
  ·
    refine ⟨98722134044523948283464601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131629512059365264377952801 98722134044523948283464601)
    ·
      refine ⟨74041600533392961212598451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98722134044523948283464601 74041600533392961212598451)
      ·
        refine ⟨111062400800089441818897677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74041600533392961212598451 111062400800089441818897677)
        ·
          refine ⟨41648400300033540682086629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111062400800089441818897677 41648400300033540682086629)
          ·
            refine ⟨7809075056256288877891243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41648400300033540682086629 7809075056256288877891243)
            ·
              refine ⟨11713612584384433316836865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809075056256288877891243 11713612584384433316836865)
              ·
                refine ⟨8785209438288324987627649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11713612584384433316836865 8785209438288324987627649)
                ·
                  refine ⟨6588907078716243740720737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8785209438288324987627649 6588907078716243740720737)
                  ·
                    refine ⟨4941680309037182805540553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588907078716243740720737 4941680309037182805540553)
                    ·
                      refine ⟨3706260231777887104155415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941680309037182805540553 3706260231777887104155415)
                      ·
                        rfl

theorem cell23_7217916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_7217916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217916 prefixEnd_7217916 := by exact prefixLift 7217916
  have htrace : WordTrace (prefixWord ++ tailWord_7217916) baseStart_7217916 baseEnd_7217916 := by
    simpa [prefixWord, tailWord_7217916, baseEnd_7217916] using wordTrace_append hprefix tailTrace_7217916
  have hstable : (prefixWord ++ tailWord_7217916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217916).length < 2 ^ (prefixWord ++ tailWord_7217916).sum := by decide
  have hdescent : baseEnd_7217916 < baseStart_7217916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217922 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_7217922 : Nat := 118140960795 + 7217922 * 2 ^ 59
def prefixEnd_7217922 : Nat := 4983230072969 + 3 ^ 40 * 7217922 * 2
def baseEnd_7217922 : Nat := 411807034740201564520043

theorem tailTrace_7217922 : CollatzResearch.WordTrace tailWord_7217922 prefixEnd_7217922 411807034740201564520043 := by
  unfold tailWord_7217922
  simp only [CollatzResearch.WordTrace]
  refine ⟨65814810739177197945156005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175506161971139194520416013 65814810739177197945156005)
  ·
    refine ⟨12340277013595724614716751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65814810739177197945156005 12340277013595724614716751)
    ·
      refine ⟨18510415520393586922075127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12340277013595724614716751 18510415520393586922075127)
      ·
        refine ⟨27765623280590380383112691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18510415520393586922075127 27765623280590380383112691)
        ·
          refine ⟨41648434920885570574669037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27765623280590380383112691 41648434920885570574669037)
          ·
            refine ⟨15618163095332088965500889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41648434920885570574669037 15618163095332088965500889)
            ·
              refine ⟨11713622321499066724125667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15618163095332088965500889 11713622321499066724125667)
              ·
                refine ⟨17570433482248600086188501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11713622321499066724125667 17570433482248600086188501)
                ·
                  refine ⟨411807034740201564520043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17570433482248600086188501 411807034740201564520043)
                  ·
                    rfl

theorem cell23_7217922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_7217922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217922 prefixEnd_7217922 := by exact prefixLift 7217922
  have htrace : WordTrace (prefixWord ++ tailWord_7217922) baseStart_7217922 baseEnd_7217922 := by
    simpa [prefixWord, tailWord_7217922, baseEnd_7217922] using wordTrace_append hprefix tailTrace_7217922
  have hstable : (prefixWord ++ tailWord_7217922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217922).length < 2 ^ (prefixWord ++ tailWord_7217922).sum := by decide
  have hdescent : baseEnd_7217922 < baseStart_7217922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217925 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 7, 2]
def baseStart_7217925 : Nat := 118140960795 + 7217925 * 2 ^ 59
def prefixEnd_7217925 : Nat := 4983230072969 + 3 ^ 40 * 7217925 * 2
def baseEnd_7217925 : Nat := 3706264853103777568942873

theorem tailTrace_7217925 : CollatzResearch.WordTrace tailWord_7217925 prefixEnd_7217925 3706264853103777568942873 := by
  unfold tailWord_7217925
  simp only [CollatzResearch.WordTrace]
  refine ⟨263259352375697923292983229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175506234917131948861988819 263259352375697923292983229)
  ·
    refine ⟨98722257140886721234868711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263259352375697923292983229 98722257140886721234868711)
    ·
      refine ⟨148083385711330081852303067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98722257140886721234868711 148083385711330081852303067)
      ·
        refine ⟨222125078566995122778454601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148083385711330081852303067 222125078566995122778454601)
        ·
          refine ⟨166593808925246342083840951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222125078566995122778454601 166593808925246342083840951)
          ·
            refine ⟨249890713387869513125761427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166593808925246342083840951 249890713387869513125761427)
            ·
              refine ⟨374836070081804269688642141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249890713387869513125761427 374836070081804269688642141)
              ·
                refine ⟨140563526280676601133240803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374836070081804269688642141 140563526280676601133240803)
                ·
                  refine ⟨210845289421014901699861205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140563526280676601133240803 210845289421014901699861205)
                  ·
                    refine ⟨4941686470805036758590497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 210845289421014901699861205 4941686470805036758590497)
                    ·
                      refine ⟨3706264853103777568942873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941686470805036758590497 3706264853103777568942873)
                      ·
                        rfl

theorem cell23_7217925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_7217925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217925 prefixEnd_7217925 := by exact prefixLift 7217925
  have htrace : WordTrace (prefixWord ++ tailWord_7217925) baseStart_7217925 baseEnd_7217925 := by
    simpa [prefixWord, tailWord_7217925, baseEnd_7217925] using wordTrace_append hprefix tailTrace_7217925
  have hstable : (prefixWord ++ tailWord_7217925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217925).length < 2 ^ (prefixWord ++ tailWord_7217925).sum := by decide
  have hdescent : baseEnd_7217925 < baseStart_7217925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217955 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 4]
def baseStart_7217955 : Nat := 118140960795 + 7217955 * 2 ^ 59
def prefixEnd_7217955 : Nat := 4983230072969 + 3 ^ 40 * 7217955 * 2
def baseEnd_7217955 : Nat := 3706280257523412451567735

theorem tailTrace_7217955 : CollatzResearch.WordTrace tailWord_7217955 prefixEnd_7217955 3706280257523412451567735 := by
  unfold tailWord_7217955
  simp only [CollatzResearch.WordTrace]
  refine ⟨263260446565589238416575319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175506964377059492277716879 263260446565589238416575319)
  ·
    refine ⟨394890669848383857624862979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263260446565589238416575319 394890669848383857624862979)
    ·
      refine ⟨592336004772575786437294469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394890669848383857624862979 592336004772575786437294469)
      ·
        refine ⟨111063000894857959956992713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 592336004772575786437294469 111063000894857959956992713)
        ·
          refine ⟨83297250671143469967744535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111063000894857959956992713 83297250671143469967744535)
          ·
            refine ⟨124945876006715204951616803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83297250671143469967744535 124945876006715204951616803)
            ·
              refine ⟨187418814010072807427425205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124945876006715204951616803 187418814010072807427425205)
              ·
                refine ⟨17570513813444325696321113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187418814010072807427425205 17570513813444325696321113)
                ·
                  refine ⟨13177885360083244272240835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17570513813444325696321113 13177885360083244272240835)
                  ·
                    refine ⟨19766828040124866408361253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13177885360083244272240835 19766828040124866408361253)
                    ·
                      refine ⟨3706280257523412451567735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19766828040124866408361253 3706280257523412451567735)
                      ·
                        rfl

theorem cell23_7217955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_7217955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217955 prefixEnd_7217955 := by exact prefixLift 7217955
  have htrace : WordTrace (prefixWord ++ tailWord_7217955) baseStart_7217955 baseEnd_7217955 := by
    simpa [prefixWord, tailWord_7217955, baseEnd_7217955] using wordTrace_append hprefix tailTrace_7217955
  have hstable : (prefixWord ++ tailWord_7217955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217955).length < 2 ^ (prefixWord ++ tailWord_7217955).sum := by decide
  have hdescent : baseEnd_7217955 < baseStart_7217955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217956 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 5]
def baseStart_7217956 : Nat := 118140960795 + 7217956 * 2 ^ 59
def prefixEnd_7217956 : Nat := 4983230072969 + 3 ^ 40 * 7217956 * 2
def baseEnd_7217956 : Nat := 411808974556007438628359

theorem tailTrace_7217956 : CollatzResearch.WordTrace tailWord_7217956 prefixEnd_7217956 411808974556007438628359 := by
  unfold tailWord_7217956
  simp only [CollatzResearch.WordTrace]
  refine ⟨131630241519292807793680861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175506988692390410391574481 131630241519292807793680861)
  ·
    refine ⟨49361340569734802922630323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131630241519292807793680861 49361340569734802922630323)
    ·
      refine ⟨74042010854602204383945485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49361340569734802922630323 74042010854602204383945485)
      ·
        refine ⟨27765754070475826643979557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74042010854602204383945485 27765754070475826643979557)
        ·
          refine ⟨5206078888214217495746167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27765754070475826643979557 5206078888214217495746167)
          ·
            refine ⟨7809118332321326243619251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206078888214217495746167 7809118332321326243619251)
            ·
              refine ⟨11713677498481989365428877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809118332321326243619251 11713677498481989365428877)
              ·
                refine ⟨4392629061930746012035829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11713677498481989365428877 4392629061930746012035829)
                ·
                  refine ⟨411808974556007438628359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4392629061930746012035829 411808974556007438628359)
                  ·
                    rfl

theorem cell23_7217956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_7217956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217956 prefixEnd_7217956 := by exact prefixLift 7217956
  have htrace : WordTrace (prefixWord ++ tailWord_7217956) baseStart_7217956 baseEnd_7217956 := by
    simpa [prefixWord, tailWord_7217956, baseEnd_7217956] using wordTrace_append hprefix tailTrace_7217956
  have hstable : (prefixWord ++ tailWord_7217956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217956).length < 2 ^ (prefixWord ++ tailWord_7217956).sum := by decide
  have hdescent : baseEnd_7217956 < baseStart_7217956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217968 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_7217968 : Nat := 118140960795 + 7217968 * 2 ^ 59
def prefixEnd_7217968 : Nat := 4983230072969 + 3 ^ 40 * 7217968 * 2
def baseEnd_7217968 : Nat := 3706286932771920900705175

theorem tailTrace_7217968 : CollatzResearch.WordTrace tailWord_7217968 prefixEnd_7217968 3706286932771920900705175 := by
  unfold tailWord_7217968
  simp only [CollatzResearch.WordTrace]
  refine ⟨131630460357271070818399279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175507280476361427757865705 131630460357271070818399279)
  ·
    refine ⟨197445690535906606227598919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131630460357271070818399279 197445690535906606227598919)
    ·
      refine ⟨296168535803859909341398379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197445690535906606227598919 296168535803859909341398379)
      ·
        refine ⟨444252803705789864012097569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296168535803859909341398379 444252803705789864012097569)
        ·
          refine ⟨333189602779342398009073177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444252803705789864012097569 333189602779342398009073177)
          ·
            refine ⟨249892202084506798506804883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333189602779342398009073177 249892202084506798506804883)
            ·
              refine ⟨374838303126760197760207325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249892202084506798506804883 374838303126760197760207325)
              ·
                refine ⟨140564363672535074160077747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374838303126760197760207325 140564363672535074160077747)
                ·
                  refine ⟨210846545508802611240116621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140564363672535074160077747 210846545508802611240116621)
                  ·
                    refine ⟨79067454565800979215043733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210846545508802611240116621 79067454565800979215043733)
                    ·
                      refine ⟨3706286932771920900705175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79067454565800979215043733 3706286932771920900705175)
                      ·
                        rfl

theorem cell23_7217968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_7217968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217968 prefixEnd_7217968 := by exact prefixLift 7217968
  have htrace : WordTrace (prefixWord ++ tailWord_7217968) baseStart_7217968 baseEnd_7217968 := by
    simpa [prefixWord, tailWord_7217968, baseEnd_7217968] using wordTrace_append hprefix tailTrace_7217968
  have hstable : (prefixWord ++ tailWord_7217968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217968).length < 2 ^ (prefixWord ++ tailWord_7217968).sum := by decide
  have hdescent : baseEnd_7217968 < baseStart_7217968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218066 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7218066 : Nat := 118140960795 + 7218066 * 2 ^ 59
def prefixEnd_7218066 : Nat := 4983230072969 + 3 ^ 40 * 7218066 * 2
def baseEnd_7218066 : Nat := 3706337253876061517279725

theorem tailTrace_7218066 : CollatzResearch.WordTrace tailWord_7218066 prefixEnd_7218066 3706337253876061517279725 := by
  unfold tailWord_7218066
  simp only [CollatzResearch.WordTrace]
  refine ⟨65816123767046776093466513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175509663378791402915910701 65816123767046776093466513)
  ·
    refine ⟨49362092825285082070099885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65816123767046776093466513 49362092825285082070099885)
    ·
      refine ⟨18510784809481905776287457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49362092825285082070099885 18510784809481905776287457)
      ·
        refine ⟨13883088607111429332215593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18510784809481905776287457 13883088607111429332215593)
        ·
          refine ⟨10412316455333571999161695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13883088607111429332215593 10412316455333571999161695)
          ·
            refine ⟨15618474683000357998742543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10412316455333571999161695 15618474683000357998742543)
            ·
              refine ⟨23427712024500536998113815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15618474683000357998742543 23427712024500536998113815)
              ·
                refine ⟨35141568036750805497170723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23427712024500536998113815 35141568036750805497170723)
                ·
                  refine ⟨52712352055126208245756085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35141568036750805497170723 52712352055126208245756085)
                  ·
                    refine ⟨4941783005168082023039633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52712352055126208245756085 4941783005168082023039633)
                    ·
                      refine ⟨3706337253876061517279725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941783005168082023039633 3706337253876061517279725)
                      ·
                        rfl

theorem cell23_7218066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7218066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218066 prefixEnd_7218066 := by exact prefixLift 7218066
  have htrace : WordTrace (prefixWord ++ tailWord_7218066) baseStart_7218066 baseEnd_7218066 := by
    simpa [prefixWord, tailWord_7218066, baseEnd_7218066] using wordTrace_append hprefix tailTrace_7218066
  have hstable : (prefixWord ++ tailWord_7218066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218066).length < 2 ^ (prefixWord ++ tailWord_7218066).sum := by decide
  have hdescent : baseEnd_7218066 < baseStart_7218066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218079 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 4]
def baseStart_7218079 : Nat := 118140960795 + 7218079 * 2 ^ 59
def prefixEnd_7218079 : Nat := 4983230072969 + 3 ^ 40 * 7218079 * 2
def baseEnd_7218079 : Nat := 3706343929124569966417165

theorem tailTrace_7218079 : CollatzResearch.WordTrace tailWord_7218079 prefixEnd_7218079 3706343929124569966417165 := by
  unfold tailWord_7218079
  simp only [CollatzResearch.WordTrace]
  refine ⟨263264969217140007594089291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175509979478093338396059527 263264969217140007594089291)
  ·
    refine ⟨394897453825710011391133937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263264969217140007594089291 394897453825710011391133937)
    ·
      refine ⟨296173090369282508543350453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394897453825710011391133937 296173090369282508543350453)
      ·
        refine ⟨27766227222120235175939105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296173090369282508543350453 27766227222120235175939105)
        ·
          refine ⟨20824670416590176381954329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27766227222120235175939105 20824670416590176381954329)
          ·
            refine ⟨15618502812442632286465747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20824670416590176381954329 15618502812442632286465747)
            ·
              refine ⟨23427754218663948429698621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15618502812442632286465747 23427754218663948429698621)
              ·
                refine ⟨8785407831998980661136983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23427754218663948429698621 8785407831998980661136983)
                ·
                  refine ⟨13178111747998470991705475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785407831998980661136983 13178111747998470991705475)
                  ·
                    refine ⟨19767167621997706487558213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13178111747998470991705475 19767167621997706487558213)
                    ·
                      refine ⟨3706343929124569966417165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19767167621997706487558213 3706343929124569966417165)
                      ·
                        rfl

theorem cell23_7218079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_7218079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218079 prefixEnd_7218079 := by exact prefixLift 7218079
  have htrace : WordTrace (prefixWord ++ tailWord_7218079) baseStart_7218079 baseEnd_7218079 := by
    simpa [prefixWord, tailWord_7218079, baseEnd_7218079] using wordTrace_append hprefix tailTrace_7218079
  have hstable : (prefixWord ++ tailWord_7218079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218079).length < 2 ^ (prefixWord ++ tailWord_7218079).sum := by decide
  have hdescent : baseEnd_7218079 < baseStart_7218079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218130 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7218130 : Nat := 118140960795 + 7218130 * 2 ^ 59
def prefixEnd_7218130 : Nat := 4983230072969 + 3 ^ 40 * 7218130 * 2
def baseEnd_7218130 : Nat := 3706370116637949266879431

theorem tailTrace_7218130 : CollatzResearch.WordTrace tailWord_7218130 prefixEnd_7218130 3706370116637949266879431 := by
  unfold tailWord_7218130
  simp only [CollatzResearch.WordTrace]
  refine ⟨65816707334988810826048961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175511219559970162202797229 65816707334988810826048961)
  ·
    refine ⟨49362530501241608119536721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65816707334988810826048961 49362530501241608119536721)
    ·
      refine ⟨37021897875931206089652541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49362530501241608119536721 37021897875931206089652541)
      ·
        refine ⟨13883211703474202283619703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37021897875931206089652541 13883211703474202283619703)
        ·
          refine ⟨20824817555211303425429555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13883211703474202283619703 20824817555211303425429555)
          ·
            refine ⟨31237226332816955138144333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20824817555211303425429555 31237226332816955138144333)
            ·
              refine ⟨11713959874806358176804125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31237226332816955138144333 11713959874806358176804125)
              ·
                refine ⟨4392734953052384316301547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11713959874806358176804125 4392734953052384316301547)
                ·
                  refine ⟨6589102429578576474452321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392734953052384316301547 6589102429578576474452321)
                  ·
                    refine ⟨4941826822183932355839241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6589102429578576474452321 4941826822183932355839241)
                    ·
                      refine ⟨3706370116637949266879431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941826822183932355839241 3706370116637949266879431)
                      ·
                        rfl

theorem cell23_7218130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7218130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218130 prefixEnd_7218130 := by exact prefixLift 7218130
  have htrace : WordTrace (prefixWord ++ tailWord_7218130) baseStart_7218130 baseEnd_7218130 := by
    simpa [prefixWord, tailWord_7218130, baseEnd_7218130] using wordTrace_append hprefix tailTrace_7218130
  have hstable : (prefixWord ++ tailWord_7218130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218130).length < 2 ^ (prefixWord ++ tailWord_7218130).sum := by decide
  have hdescent : baseEnd_7218130 < baseStart_7218130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218164 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7218164 : Nat := 118140960795 + 7218164 * 2 ^ 59
def prefixEnd_7218164 : Nat := 4983230072969 + 3 ^ 40 * 7218164 * 2
def baseEnd_7218164 : Nat := 3706387574980202133854275

theorem tailTrace_7218164 : CollatzResearch.WordTrace tailWord_7218164 prefixEnd_7218164 3706387574980202133854275 := by
  unfold tailWord_7218164
  simp only [CollatzResearch.WordTrace]
  refine ⟨131634034710916033555466773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175512046281221378073955697 131634034710916033555466773)
  ·
    refine ⟨6170345377074189072912505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131634034710916033555466773 6170345377074189072912505)
    ·
      refine ⟨4627759032805641804684379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6170345377074189072912505 4627759032805641804684379)
      ·
        refine ⟨6941638549208462707026569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627759032805641804684379 6941638549208462707026569)
        ·
          refine ⟨5206228911906347030269927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6941638549208462707026569 5206228911906347030269927)
          ·
            refine ⟨7809343367859520545404891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206228911906347030269927 7809343367859520545404891)
            ·
              refine ⟨11714015051789280818107337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809343367859520545404891 11714015051789280818107337)
              ·
                refine ⟨8785511288841960613580503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11714015051789280818107337 8785511288841960613580503)
                ·
                  refine ⟨13178266933262940920370755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785511288841960613580503 13178266933262940920370755)
                  ·
                    refine ⟨19767400399894411380556133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13178266933262940920370755 19767400399894411380556133)
                    ·
                      refine ⟨3706387574980202133854275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19767400399894411380556133 3706387574980202133854275)
                      ·
                        rfl

theorem cell23_7218164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7218164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218164 prefixEnd_7218164 := by exact prefixLift 7218164
  have htrace : WordTrace (prefixWord ++ tailWord_7218164) baseStart_7218164 baseEnd_7218164 := by
    simpa [prefixWord, tailWord_7218164, baseEnd_7218164] using wordTrace_append hprefix tailTrace_7218164
  have hstable : (prefixWord ++ tailWord_7218164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218164).length < 2 ^ (prefixWord ++ tailWord_7218164).sum := by decide
  have hdescent : baseEnd_7218164 < baseStart_7218164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218169 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 1, 4, 2]
def baseStart_7218169 : Nat := 118140960795 + 7218169 * 2 ^ 59
def prefixEnd_7218169 : Nat := 4983230072969 + 3 ^ 40 * 7218169 * 2
def baseEnd_7218169 : Nat := 3706390142383474614291751

theorem tailTrace_7218169 : CollatzResearch.WordTrace tailWord_7218169 prefixEnd_7218169 3706390142383474614291751 := by
  unfold tailWord_7218169
  simp only [CollatzResearch.WordTrace]
  refine ⟨263268251786813952964865561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175512167857875968643243707 263268251786813952964865561)
  ·
    refine ⟨197451188840110464723649171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263268251786813952964865561 197451188840110464723649171)
    ·
      refine ⟨296176783260165697085473757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197451188840110464723649171 296176783260165697085473757)
      ·
        refine ⟨111066293722562136407052659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296176783260165697085473757 111066293722562136407052659)
        ·
          refine ⟨166599440583843204610578989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111066293722562136407052659 166599440583843204610578989)
          ·
            refine ⟨62474790218941201728967121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166599440583843204610578989 62474790218941201728967121)
            ·
              refine ⟨46856092664205901296725341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62474790218941201728967121 46856092664205901296725341)
              ·
                refine ⟨17571034749077212986272003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46856092664205901296725341 17571034749077212986272003)
                ·
                  refine ⟨26356552123615819479408005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17571034749077212986272003 26356552123615819479408005)
                  ·
                    refine ⟨4941853523177966152389001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26356552123615819479408005 4941853523177966152389001)
                    ·
                      refine ⟨3706390142383474614291751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941853523177966152389001 3706390142383474614291751)
                      ·
                        rfl

theorem cell23_7218169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_7218169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218169 prefixEnd_7218169 := by exact prefixLift 7218169
  have htrace : WordTrace (prefixWord ++ tailWord_7218169) baseStart_7218169 baseEnd_7218169 := by
    simpa [prefixWord, tailWord_7218169, baseEnd_7218169] using wordTrace_append hprefix tailTrace_7218169
  have hstable : (prefixWord ++ tailWord_7218169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218169).length < 2 ^ (prefixWord ++ tailWord_7218169).sum := by decide
  have hdescent : baseEnd_7218169 < baseStart_7218169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218172 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_7218172 : Nat := 118140960795 + 7218172 * 2 ^ 59
def prefixEnd_7218172 : Nat := 4983230072969 + 3 ^ 40 * 7218172 * 2
def baseEnd_7218172 : Nat := 3706391682825438102554237

theorem tailTrace_7218172 : CollatzResearch.WordTrace tailWord_7218172 prefixEnd_7218172 3706391682825438102554237 := by
  unfold tailWord_7218172
  simp only [CollatzResearch.WordTrace]
  refine ⟨131634180602901542238612385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175512240803868722984816513 131634180602901542238612385)
  ·
    refine ⟨98725635452176156678959289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131634180602901542238612385 98725635452176156678959289)
    ·
      refine ⟨74044226589132117509219467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98725635452176156678959289 74044226589132117509219467)
      ·
        refine ⟨111066339883698176263829201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74044226589132117509219467 111066339883698176263829201)
        ·
          refine ⟨83299754912773632197871901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111066339883698176263829201 83299754912773632197871901)
          ·
            refine ⟨31237408092290112074201963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83299754912773632197871901 31237408092290112074201963)
            ·
              refine ⟨46856112138435168111302945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31237408092290112074201963 46856112138435168111302945)
              ·
                refine ⟨35142084103826376083477209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46856112138435168111302945 35142084103826376083477209)
                ·
                  refine ⟨26356563077869782062607907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35142084103826376083477209 26356563077869782062607907)
                  ·
                    refine ⟨39534844616804673093911861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26356563077869782062607907 39534844616804673093911861)
                    ·
                      refine ⟨3706391682825438102554237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39534844616804673093911861 3706391682825438102554237)
                      ·
                        rfl

theorem cell23_7218172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_7218172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218172 prefixEnd_7218172 := by exact prefixLift 7218172
  have htrace : WordTrace (prefixWord ++ tailWord_7218172) baseStart_7218172 baseEnd_7218172 := by
    simpa [prefixWord, tailWord_7218172, baseEnd_7218172] using wordTrace_append hprefix tailTrace_7218172
  have hstable : (prefixWord ++ tailWord_7218172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218172).length < 2 ^ (prefixWord ++ tailWord_7218172).sum := by decide
  have hdescent : baseEnd_7218172 < baseStart_7218172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218186 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_7218186 : Nat := 118140960795 + 7218186 * 2 ^ 59
def prefixEnd_7218186 : Nat := 4983230072969 + 3 ^ 40 * 7218186 * 2
def baseEnd_7218186 : Nat := 3706398871554601047779173

theorem tailTrace_7218186 : CollatzResearch.WordTrace tailWord_7218186 prefixEnd_7218186 3706398871554601047779173 := by
  unfold tailWord_7218186
  simp only [CollatzResearch.WordTrace]
  refine ⟨65817217956938091217058603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175512581218501576578822941 65817217956938091217058603)
  ·
    refine ⟨98725826935407136825587905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65817217956938091217058603 98725826935407136825587905)
    ·
      refine ⟨74044370201555352619190929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98725826935407136825587905 74044370201555352619190929)
      ·
        refine ⟨55533277651166514464393197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74044370201555352619190929 55533277651166514464393197)
        ·
          refine ⟨20824979119187442924147449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55533277651166514464393197 20824979119187442924147449)
          ·
            refine ⟨15618734339390582193110587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20824979119187442924147449 15618734339390582193110587)
            ·
              refine ⟨23428101509085873289665881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15618734339390582193110587 23428101509085873289665881)
              ·
                refine ⟨17571076131814404967249411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23428101509085873289665881 17571076131814404967249411)
                ·
                  refine ⟨26356614197721607450874117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17571076131814404967249411 26356614197721607450874117)
                  ·
                    refine ⟨4941865162072801397038897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26356614197721607450874117 4941865162072801397038897)
                    ·
                      refine ⟨3706398871554601047779173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941865162072801397038897 3706398871554601047779173)
                      ·
                        rfl

theorem cell23_7218186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_7218186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218186 prefixEnd_7218186 := by exact prefixLift 7218186
  have htrace : WordTrace (prefixWord ++ tailWord_7218186) baseStart_7218186 baseEnd_7218186 := by
    simpa [prefixWord, tailWord_7218186, baseEnd_7218186] using wordTrace_append hprefix tailTrace_7218186
  have hstable : (prefixWord ++ tailWord_7218186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218186).length < 2 ^ (prefixWord ++ tailWord_7218186).sum := by decide
  have hdescent : baseEnd_7218186 < baseStart_7218186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218229 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_7218229 : Nat := 118140960795 + 7218229 * 2 ^ 59
def prefixEnd_7218229 : Nat := 4983230072969 + 3 ^ 40 * 7218229 * 2
def baseEnd_7218229 : Nat := 3706420951222744379541475

theorem tailTrace_7218229 : CollatzResearch.WordTrace tailWord_7218229 prefixEnd_7218229 3706420951222744379541475 := by
  unfold tailWord_7218229
  simp only [CollatzResearch.WordTrace]
  refine ⟨263270440166596583212049741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175513626777731055474699827 263270440166596583212049741)
  ·
    refine ⟨98726415062473718704518653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263270440166596583212049741 98726415062473718704518653)
    ·
      refine ⟨37022405648427644514194495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98726415062473718704518653 37022405648427644514194495)
      ·
        refine ⟨55533608472641466771291743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37022405648427644514194495 55533608472641466771291743)
        ·
          refine ⟨83300412708962200156937615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55533608472641466771291743 83300412708962200156937615)
          ·
            refine ⟨124950619063443300235406423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83300412708962200156937615 124950619063443300235406423)
            ·
              refine ⟨187425928595164950353109635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124950619063443300235406423 187425928595164950353109635)
              ·
                refine ⟨281138892892747425529664453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187425928595164950353109635 281138892892747425529664453)
                ·
                  refine ⟨52713542417390142286812085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281138892892747425529664453 52713542417390142286812085)
                  ·
                    refine ⟨4941894601630325839388633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52713542417390142286812085 4941894601630325839388633)
                    ·
                      refine ⟨3706420951222744379541475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941894601630325839388633 3706420951222744379541475)
                      ·
                        rfl

theorem cell23_7218229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_7218229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218229 prefixEnd_7218229 := by exact prefixLift 7218229
  have htrace : WordTrace (prefixWord ++ tailWord_7218229) baseStart_7218229 baseEnd_7218229 := by
    simpa [prefixWord, tailWord_7218229, baseEnd_7218229] using wordTrace_append hprefix tailTrace_7218229
  have hstable : (prefixWord ++ tailWord_7218229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218229).length < 2 ^ (prefixWord ++ tailWord_7218229).sum := by decide
  have hdescent : baseEnd_7218229 < baseStart_7218229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218259 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 2, 4, 2]
def baseStart_7218259 : Nat := 118140960795 + 7218259 * 2 ^ 59
def prefixEnd_7218259 : Nat := 4983230072969 + 3 ^ 40 * 7218259 * 2
def baseEnd_7218259 : Nat := 3706436355642379262166337

theorem tailTrace_7218259 : CollatzResearch.WordTrace tailWord_7218259 prefixEnd_7218259 3706436355642379262166337 := by
  unfold tailWord_7218259
  simp only [CollatzResearch.WordTrace]
  refine ⟨263271534356487898335641831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175514356237658598890427887 263271534356487898335641831)
  ·
    refine ⟨394907301534731847503462747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263271534356487898335641831 394907301534731847503462747)
    ·
      refine ⟨592360952302097771255194121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394907301534731847503462747 592360952302097771255194121)
      ·
        refine ⟨444270714226573328441395591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592360952302097771255194121 444270714226573328441395591)
        ·
          refine ⟨666406071339859992662093387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444270714226573328441395591 666406071339859992662093387)
          ·
            refine ⟨999609107009789988993140081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666406071339859992662093387 999609107009789988993140081)
            ·
              refine ⟨749706830257342491744855061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999609107009789988993140081 749706830257342491744855061)
              ·
                refine ⟨35142507668312929300540081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 749706830257342491744855061 35142507668312929300540081)
                ·
                  refine ⟨26356880751234696975405061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35142507668312929300540081 26356880751234696975405061)
                  ·
                    refine ⟨4941915140856505682888449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26356880751234696975405061 4941915140856505682888449)
                    ·
                      refine ⟨3706436355642379262166337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941915140856505682888449 3706436355642379262166337)
                      ·
                        rfl

theorem cell23_7218259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4, 2].length) (baseStart_7218259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218259 prefixEnd_7218259 := by exact prefixLift 7218259
  have htrace : WordTrace (prefixWord ++ tailWord_7218259) baseStart_7218259 baseEnd_7218259 := by
    simpa [prefixWord, tailWord_7218259, baseEnd_7218259] using wordTrace_append hprefix tailTrace_7218259
  have hstable : (prefixWord ++ tailWord_7218259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218259).length < 2 ^ (prefixWord ++ tailWord_7218259).sum := by decide
  have hdescent : baseEnd_7218259 < baseStart_7218259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218272 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_7218272 : Nat := 118140960795 + 7218272 * 2 ^ 59
def prefixEnd_7218272 : Nat := 4983230072969 + 3 ^ 40 * 7218272 * 2
def baseEnd_7218272 : Nat := 3706443030890887711303777

theorem tailTrace_7218272 : CollatzResearch.WordTrace tailWord_7218272 prefixEnd_7218272 3706443030890887711303777 := by
  unfold tailWord_7218272
  simp only [CollatzResearch.WordTrace]
  refine ⟨131636004252720400777932535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175514672336960534370576713 131636004252720400777932535)
  ·
    refine ⟨197454006379080601166898803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131636004252720400777932535 197454006379080601166898803)
    ·
      refine ⟨296181009568620901750348205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197454006379080601166898803 296181009568620901750348205)
      ·
        refine ⟨111067878588232838156380577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296181009568620901750348205 111067878588232838156380577)
        ·
          refine ⟨83300908941174628617285433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111067878588232838156380577 83300908941174628617285433)
          ·
            refine ⟨62475681705880971462964075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83300908941174628617285433 62475681705880971462964075)
            ·
              refine ⟨93713522558821457194446113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62475681705880971462964075 93713522558821457194446113)
              ·
                refine ⟨70285141919116092895834585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93713522558821457194446113 70285141919116092895834585)
                ·
                  refine ⟨52713856439337069671875939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70285141919116092895834585 52713856439337069671875939)
                  ·
                    refine ⟨79070784659005604507813909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52713856439337069671875939 79070784659005604507813909)
                    ·
                      refine ⟨3706443030890887711303777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79070784659005604507813909 3706443030890887711303777)
                      ·
                        rfl

theorem cell23_7218272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_7218272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218272 prefixEnd_7218272 := by exact prefixLift 7218272
  have htrace : WordTrace (prefixWord ++ tailWord_7218272) baseStart_7218272 baseEnd_7218272 := by
    simpa [prefixWord, tailWord_7218272, baseEnd_7218272] using wordTrace_append hprefix tailTrace_7218272
  have hstable : (prefixWord ++ tailWord_7218272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218272).length < 2 ^ (prefixWord ++ tailWord_7218272).sum := by decide
  have hdescent : baseEnd_7218272 < baseStart_7218272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218279 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_7218279 : Nat := 118140960795 + 7218279 * 2 ^ 59
def prefixEnd_7218279 : Nat := 4983230072969 + 3 ^ 40 * 7218279 * 2
def baseEnd_7218279 : Nat := 3706446625255469183916245

theorem tailTrace_7218279 : CollatzResearch.WordTrace tailWord_7218279 prefixEnd_7218279 3706446625255469183916245 := by
  unfold tailWord_7218279
  simp only [CollatzResearch.WordTrace]
  refine ⟨263272263816415441751369891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175514842544276961167579927 263272263816415441751369891)
  ·
    refine ⟨394908395724623162627054837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263272263816415441751369891 394908395724623162627054837)
    ·
      refine ⟨37022662099183421496286391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 394908395724623162627054837 37022662099183421496286391)
      ·
        refine ⟨55533993148775132244429587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37022662099183421496286391 55533993148775132244429587)
        ·
          refine ⟨83300989723162698366644381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55533993148775132244429587 83300989723162698366644381)
          ·
            refine ⟨31237871146186011887491643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83300989723162698366644381 31237871146186011887491643)
            ·
              refine ⟨46856806719279017831237465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31237871146186011887491643 46856806719279017831237465)
              ·
                refine ⟨35142605039459263373428099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46856806719279017831237465 35142605039459263373428099)
                ·
                  refine ⟨52713907559188895060142149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35142605039459263373428099 52713907559188895060142149)
                  ·
                    refine ⟨9883857667347917823776653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52713907559188895060142149 9883857667347917823776653)
                    ·
                      refine ⟨3706446625255469183916245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9883857667347917823776653 3706446625255469183916245)
                      ·
                        rfl

theorem cell23_7218279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_7218279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218279 prefixEnd_7218279 := by exact prefixLift 7218279
  have htrace : WordTrace (prefixWord ++ tailWord_7218279) baseStart_7218279 baseEnd_7218279 := by
    simpa [prefixWord, tailWord_7218279, baseEnd_7218279] using wordTrace_append hprefix tailTrace_7218279
  have hstable : (prefixWord ++ tailWord_7218279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218279).length < 2 ^ (prefixWord ++ tailWord_7218279).sum := by decide
  have hdescent : baseEnd_7218279 < baseStart_7218279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218286 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7218286 : Nat := 118140960795 + 7218286 * 2 ^ 59
def prefixEnd_7218286 : Nat := 4983230072969 + 3 ^ 40 * 7218286 * 2
def baseEnd_7218286 : Nat := 1235483406540016885509571

theorem tailTrace_7218286 : CollatzResearch.WordTrace tailWord_7218286 prefixEnd_7218286 1235483406540016885509571 := by
  unfold tailWord_7218286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32909064890923760243359339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175515012751593387964583141 32909064890923760243359339)
  ·
    refine ⟨49363597336385640365039009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32909064890923760243359339 49363597336385640365039009)
    ·
      refine ⟨37022698002289230273779257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49363597336385640365039009 37022698002289230273779257)
      ·
        refine ⟨27767023501716922705334443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37022698002289230273779257 27767023501716922705334443)
        ·
          refine ⟨41650535252575384058001665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27767023501716922705334443 41650535252575384058001665)
          ·
            refine ⟨31237901439431538043501249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41650535252575384058001665 31237901439431538043501249)
            ·
              refine ⟨23428426079573653532625937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31237901439431538043501249 23428426079573653532625937)
              ·
                refine ⟨17571319559680240149469453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23428426079573653532625937 17571319559680240149469453)
                ·
                  refine ⟨6589244834880090056051045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17571319559680240149469453 6589244834880090056051045)
                  ·
                    refine ⟨1235483406540016885509571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6589244834880090056051045 1235483406540016885509571)
                    ·
                      rfl

theorem cell23_7218286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7218286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218286 prefixEnd_7218286 := by exact prefixLift 7218286
  have htrace : WordTrace (prefixWord ++ tailWord_7218286) baseStart_7218286 baseEnd_7218286 := by
    simpa [prefixWord, tailWord_7218286, baseEnd_7218286] using wordTrace_append hprefix tailTrace_7218286
  have hstable : (prefixWord ++ tailWord_7218286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218286).length < 2 ^ (prefixWord ++ tailWord_7218286).sum := by decide
  have hdescent : baseEnd_7218286 < baseStart_7218286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218336 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 4, 3, 2]
def baseStart_7218336 : Nat := 118140960795 + 7218336 * 2 ^ 59
def prefixEnd_7218336 : Nat := 4983230072969 + 3 ^ 40 * 7218336 * 2
def baseEnd_7218336 : Nat := 3706475893652775460903483

theorem tailTrace_7218336 : CollatzResearch.WordTrace tailWord_7218336 prefixEnd_7218336 3706475893652775460903483 := by
  unfold tailWord_7218336
  simp only [CollatzResearch.WordTrace]
  refine ⟨131637171388604470243097431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175516228518139293657463241 131637171388604470243097431)
  ·
    refine ⟨197455757082906705364646147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131637171388604470243097431 197455757082906705364646147)
    ·
      refine ⟨296183635624360058046969221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197455757082906705364646147 296183635624360058046969221)
      ·
        refine ⟨55534431679567510883806729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296183635624360058046969221 55534431679567510883806729)
        ·
          refine ⟨41650823759675633162855047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55534431679567510883806729 41650823759675633162855047)
          ·
            refine ⟨62476235639513449744282571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41650823759675633162855047 62476235639513449744282571)
            ·
              refine ⟨93714353459270174616423857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62476235639513449744282571 93714353459270174616423857)
              ·
                refine ⟨70285765094452630962317893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93714353459270174616423857 70285765094452630962317893)
                ·
                  refine ⟨13178580955209868305434605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70285765094452630962317893 13178580955209868305434605)
                  ·
                    refine ⟨4941967858203700614537977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13178580955209868305434605 4941967858203700614537977)
                    ·
                      refine ⟨3706475893652775460903483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941967858203700614537977 3706475893652775460903483)
                      ·
                        rfl

theorem cell23_7218336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_7218336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218336 prefixEnd_7218336 := by exact prefixLift 7218336
  have htrace : WordTrace (prefixWord ++ tailWord_7218336) baseStart_7218336 baseEnd_7218336 := by
    simpa [prefixWord, tailWord_7218336, baseEnd_7218336] using wordTrace_append hprefix tailTrace_7218336
  have hstable : (prefixWord ++ tailWord_7218336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218336).length < 2 ^ (prefixWord ++ tailWord_7218336).sum := by decide
  have hdescent : baseEnd_7218336 < baseStart_7218336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218353 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7218353 : Nat := 118140960795 + 7218353 * 2 ^ 59
def prefixEnd_7218353 : Nat := 4983230072969 + 3 ^ 40 * 7218353 * 2
def baseEnd_7218353 : Nat := 3706484622823901894390905

theorem tailTrace_7218353 : CollatzResearch.WordTrace tailWord_7218353 prefixEnd_7218353 3706484622823901894390905 := by
  unfold tailWord_7218353
  simp only [CollatzResearch.WordTrace]
  refine ⟨263274962818147352389563713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175516641878764901593042475 263274962818147352389563713)
  ·
    refine ⟨197456222113610514292172785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263274962818147352389563713 197456222113610514292172785)
    ·
      refine ⟨148092166585207885719129589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197456222113610514292172785 148092166585207885719129589)
      ·
        refine ⟨13883640617363239286168399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148092166585207885719129589 13883640617363239286168399)
        ·
          refine ⟨20825460926044858929252599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13883640617363239286168399 20825460926044858929252599)
          ·
            refine ⟨31238191389067288393878899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20825460926044858929252599 31238191389067288393878899)
            ·
              refine ⟨46857287083600932590818349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31238191389067288393878899 46857287083600932590818349)
              ·
                refine ⟨17571482656350349721556881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46857287083600932590818349 17571482656350349721556881)
                ·
                  refine ⟨13178611992262762291167661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17571482656350349721556881 13178611992262762291167661)
                  ·
                    refine ⟨4941979497098535859187873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13178611992262762291167661 4941979497098535859187873)
                    ·
                      refine ⟨3706484622823901894390905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941979497098535859187873 3706484622823901894390905)
                      ·
                        rfl

theorem cell23_7218353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7218353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218353 prefixEnd_7218353 := by exact prefixLift 7218353
  have htrace : WordTrace (prefixWord ++ tailWord_7218353) baseStart_7218353 baseEnd_7218353 := by
    simpa [prefixWord, tailWord_7218353, baseEnd_7218353] using wordTrace_append hprefix tailTrace_7218353
  have hstable : (prefixWord ++ tailWord_7218353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218353).length < 2 ^ (prefixWord ++ tailWord_7218353).sum := by decide
  have hdescent : baseEnd_7218353 < baseStart_7218353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218359 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 1, 6]
def baseStart_7218359 : Nat := 118140960795 + 7218359 * 2 ^ 59
def prefixEnd_7218359 : Nat := 4983230072969 + 3 ^ 40 * 7218359 * 2
def baseEnd_7218359 : Nat := 1235495901235942956971959

theorem tailTrace_7218359 : CollatzResearch.WordTrace tailWord_7218359 prefixEnd_7218359 1235495901235942956971959 := by
  unfold tailWord_7218359
  simp only [CollatzResearch.WordTrace]
  refine ⟨263275181656125615414282131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175516787770750410276188087 263275181656125615414282131)
  ·
    refine ⟨394912772484188423121423197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263275181656125615414282131 394912772484188423121423197)
    ·
      refine ⟨148092289681570658670533699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394912772484188423121423197 148092289681570658670533699)
      ·
        refine ⟨222138434522355988005800549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148092289681570658670533699 222138434522355988005800549)
        ·
          refine ⟨41650956472941747751087603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222138434522355988005800549 41650956472941747751087603)
          ·
            refine ⟨62476434709412621626631405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41650956472941747751087603 62476434709412621626631405)
            ·
              refine ⟨23428663016029733109986777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62476434709412621626631405 23428663016029733109986777)
              ·
                refine ⟨17571497262022299832490083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23428663016029733109986777 17571497262022299832490083)
                ·
                  refine ⟨26357245893033449748735125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17571497262022299832490083 26357245893033449748735125)
                  ·
                    refine ⟨1235495901235942956971959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26357245893033449748735125 1235495901235942956971959)
                    ·
                      rfl

theorem cell23_7218359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_7218359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218359 prefixEnd_7218359 := by exact prefixLift 7218359
  have htrace : WordTrace (prefixWord ++ tailWord_7218359) baseStart_7218359 baseEnd_7218359 := by
    simpa [prefixWord, tailWord_7218359, baseEnd_7218359] using wordTrace_append hprefix tailTrace_7218359
  have hstable : (prefixWord ++ tailWord_7218359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218359).length < 2 ^ (prefixWord ++ tailWord_7218359).sum := by decide
  have hdescent : baseEnd_7218359 < baseStart_7218359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218376 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 2, 4]
def baseStart_7218376 : Nat := 118140960795 + 7218376 * 2 ^ 59
def prefixEnd_7218376 : Nat := 4983230072969 + 3 ^ 40 * 7218376 * 2
def baseEnd_7218376 : Nat := 1235498810959651768134433

theorem tailTrace_7218376 : CollatzResearch.WordTrace tailWord_7218376 prefixEnd_7218376 1235498810959651768134433 := by
  unfold tailWord_7218376
  simp only [CollatzResearch.WordTrace]
  refine ⟨131637900848532013658825491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175517201131376018211767321 131637900848532013658825491)
  ·
    refine ⟨197456851272798020488238237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131637900848532013658825491 197456851272798020488238237)
    ·
      refine ⟨74046319227299257683089339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197456851272798020488238237 74046319227299257683089339)
      ·
        refine ⟨111069478840948886524634009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74046319227299257683089339 111069478840948886524634009)
        ·
          refine ⟨83302109130711664893475507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111069478840948886524634009 83302109130711664893475507)
          ·
            refine ⟨124953163696067497340213261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83302109130711664893475507 124953163696067497340213261)
            ·
              refine ⟨46857436386025311502579973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124953163696067497340213261 46857436386025311502579973)
              ·
                refine ⟨8785769322379745906733745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46857436386025311502579973 8785769322379745906733745)
                ·
                  refine ⟨6589326991784809430050309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8785769322379745906733745 6589326991784809430050309)
                  ·
                    refine ⟨1235498810959651768134433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6589326991784809430050309 1235498810959651768134433)
                    ·
                      rfl

theorem cell23_7218376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_7218376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218376 prefixEnd_7218376 := by exact prefixLift 7218376
  have htrace : WordTrace (prefixWord ++ tailWord_7218376) baseStart_7218376 baseEnd_7218376 := by
    simpa [prefixWord, tailWord_7218376, baseEnd_7218376] using wordTrace_append hprefix tailTrace_7218376
  have hstable : (prefixWord ++ tailWord_7218376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218376).length < 2 ^ (prefixWord ++ tailWord_7218376).sum := by decide
  have hdescent : baseEnd_7218376 < baseStart_7218376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218386 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7218386 : Nat := 118140960795 + 7218386 * 2 ^ 59
def prefixEnd_7218386 : Nat := 4983230072969 + 3 ^ 40 * 7218386 * 2
def baseEnd_7218386 : Nat := 3706501567685500265278253

theorem tailTrace_7218386 : CollatzResearch.WordTrace tailWord_7218386 prefixEnd_7218386 3706501567685500265278253 := by
  unfold tailWord_7218386
  simp only [CollatzResearch.WordTrace]
  refine ⟨65819041606756949756378753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175517444284685199350343341 65819041606756949756378753)
  ·
    refine ⟨49364281205067712317284065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65819041606756949756378753 49364281205067712317284065)
    ·
      refine ⟨37023210903800784237963049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49364281205067712317284065 37023210903800784237963049)
      ·
        refine ⟨27767408177850588178472287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37023210903800784237963049 27767408177850588178472287)
        ·
          refine ⟨41651112266775882267708431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27767408177850588178472287 41651112266775882267708431)
          ·
            refine ⟨62476668400163823401562647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41651112266775882267708431 62476668400163823401562647)
            ·
              refine ⟨93715002600245735102343971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62476668400163823401562647 93715002600245735102343971)
              ·
                refine ⟨140572503900368602653515957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93715002600245735102343971 140572503900368602653515957)
                ·
                  refine ⟨13178672240659556498767121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140572503900368602653515957 13178672240659556498767121)
                  ·
                    refine ⟨9884004180494667374075341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13178672240659556498767121 9884004180494667374075341)
                    ·
                      refine ⟨3706501567685500265278253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884004180494667374075341 3706501567685500265278253)
                      ·
                        rfl

theorem cell23_7218386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7218386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218386 prefixEnd_7218386 := by exact prefixLift 7218386
  have htrace : WordTrace (prefixWord ++ tailWord_7218386) baseStart_7218386 baseEnd_7218386 := by
    simpa [prefixWord, tailWord_7218386, baseEnd_7218386] using wordTrace_append hprefix tailTrace_7218386
  have hstable : (prefixWord ++ tailWord_7218386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218386).length < 2 ^ (prefixWord ++ tailWord_7218386).sum := by decide
  have hdescent : baseEnd_7218386 < baseStart_7218386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218433 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_7218433 : Nat := 118140960795 + 7218433 * 2 ^ 59
def prefixEnd_7218433 : Nat := 4983230072969 + 3 ^ 40 * 7218433 * 2
def baseEnd_7218433 : Nat := 3706525701276261581390537

theorem tailTrace_7218433 : CollatzResearch.WordTrace tailWord_7218433 prefixEnd_7218433 3706525701276261581390537 := by
  unfold tailWord_7218433
  simp only [CollatzResearch.WordTrace]
  refine ⟨263277880657857526052475953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175518587105238350701650635 263277880657857526052475953)
  ·
    refine ⟨197458410493393144539356965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263277880657857526052475953 197458410493393144539356965)
    ·
      refine ⟨37023451967511214601129431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197458410493393144539356965 37023451967511214601129431)
      ·
        refine ⟨55535177951266821901694147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37023451967511214601129431 55535177951266821901694147)
        ·
          refine ⟨83302766926900232852541221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55535177951266821901694147 83302766926900232852541221)
          ·
            refine ⟨15619268798793793659851479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83302766926900232852541221 15619268798793793659851479)
            ·
              refine ⟨23428903198190690489777219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15619268798793793659851479 23428903198190690489777219)
              ·
                refine ⟨35143354797286035734665829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23428903198190690489777219 35143354797286035734665829)
                ·
                  refine ⟨6589379024491131700249843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35143354797286035734665829 6589379024491131700249843)
                  ·
                    refine ⟨9884068536736697550374765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6589379024491131700249843 9884068536736697550374765)
                    ·
                      refine ⟨3706525701276261581390537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884068536736697550374765 3706525701276261581390537)
                      ·
                        rfl

theorem cell23_7218433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_7218433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218433 prefixEnd_7218433 := by exact prefixLift 7218433
  have htrace : WordTrace (prefixWord ++ tailWord_7218433) baseStart_7218433 baseEnd_7218433 := by
    simpa [prefixWord, tailWord_7218433, baseEnd_7218433] using wordTrace_append hprefix tailTrace_7218433
  have hstable : (prefixWord ++ tailWord_7218433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218433).length < 2 ^ (prefixWord ++ tailWord_7218433).sum := by decide
  have hdescent : baseEnd_7218433 < baseStart_7218433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218449 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_7218449 : Nat := 118140960795 + 7218449 * 2 ^ 59
def prefixEnd_7218449 : Nat := 4983230072969 + 3 ^ 40 * 7218449 * 2
def baseEnd_7218449 : Nat := 1235511305655577839596821

theorem tailTrace_7218449 : CollatzResearch.WordTrace tailWord_7218449 prefixEnd_7218449 1235511305655577839596821 := by
  unfold tailWord_7218449
  simp only [CollatzResearch.WordTrace]
  refine ⟨263278464225799560785058401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175518976150533040523372267 263278464225799560785058401)
  ·
    refine ⟨197458848169349670588793801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263278464225799560785058401 197458848169349670588793801)
    ·
      refine ⟨148094136127012252941595351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197458848169349670588793801 148094136127012252941595351)
      ·
        refine ⟨222141204190518379412393027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148094136127012252941595351 222141204190518379412393027)
        ·
          refine ⟨333211806285777569118589541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222141204190518379412393027 333211806285777569118589541)
          ·
            refine ⟨62477213678583294209735539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333211806285777569118589541 62477213678583294209735539)
            ·
              refine ⟨93715820517874941314603309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62477213678583294209735539 93715820517874941314603309)
              ·
                refine ⟨35143432694203102992976241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93715820517874941314603309 35143432694203102992976241)
                ·
                  refine ⟨26357574520652327244732181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35143432694203102992976241 26357574520652327244732181)
                  ·
                    refine ⟨1235511305655577839596821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26357574520652327244732181 1235511305655577839596821)
                    ·
                      rfl

theorem cell23_7218449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_7218449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218449 prefixEnd_7218449 := by exact prefixLift 7218449
  have htrace : WordTrace (prefixWord ++ tailWord_7218449) baseStart_7218449 baseEnd_7218449 := by
    simpa [prefixWord, tailWord_7218449, baseEnd_7218449] using wordTrace_append hprefix tailTrace_7218449
  have hstable : (prefixWord ++ tailWord_7218449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218449).length < 2 ^ (prefixWord ++ tailWord_7218449).sum := by decide
  have hdescent : baseEnd_7218449 < baseStart_7218449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218459 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5]
def baseStart_7218459 : Nat := 118140960795 + 7218459 * 2 ^ 59
def prefixEnd_7218459 : Nat := 4983230072969 + 3 ^ 40 * 7218459 * 2
def baseEnd_7218459 : Nat := 3706539051773278479665417

theorem tailTrace_7218459 : CollatzResearch.WordTrace tailWord_7218459 prefixEnd_7218459 3706539051773278479665417 := by
  unfold tailWord_7218459
  simp only [CollatzResearch.WordTrace]
  refine ⟨263278828955763332492922431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175519219303842221661948287 263278828955763332492922431)
  ·
    refine ⟨394918243433644998739383647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263278828955763332492922431 394918243433644998739383647)
    ·
      refine ⟨592377365150467498109075471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394918243433644998739383647 592377365150467498109075471)
      ·
        refine ⟨888566047725701247163613207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592377365150467498109075471 888566047725701247163613207)
        ·
          refine ⟨1332849071588551870745419811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888566047725701247163613207 1332849071588551870745419811)
          ·
            refine ⟨1999273607382827806118129717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332849071588551870745419811 1999273607382827806118129717)
            ·
              refine ⟨187431900692140106823574661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1999273607382827806118129717 187431900692140106823574661)
              ·
                refine ⟨35143481379776270029420249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187431900692140106823574661 35143481379776270029420249)
                ·
                  refine ⟨26357611034832202522065187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35143481379776270029420249 26357611034832202522065187)
                  ·
                    refine ⟨39536416552248303783097781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26357611034832202522065187 39536416552248303783097781)
                    ·
                      refine ⟨3706539051773278479665417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39536416552248303783097781 3706539051773278479665417)
                      ·
                        rfl

theorem cell23_7218459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_7218459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218459 prefixEnd_7218459 := by exact prefixLift 7218459
  have htrace : WordTrace (prefixWord ++ tailWord_7218459) baseStart_7218459 baseEnd_7218459 := by
    simpa [prefixWord, tailWord_7218459, baseEnd_7218459] using wordTrace_append hprefix tailTrace_7218459
  have hstable : (prefixWord ++ tailWord_7218459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218459).length < 2 ^ (prefixWord ++ tailWord_7218459).sum := by decide
  have hdescent : baseEnd_7218459 < baseStart_7218459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218477 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7218477 : Nat := 118140960795 + 7218477 * 2 ^ 59
def prefixEnd_7218477 : Nat := 4983230072969 + 3 ^ 40 * 7218477 * 2
def baseEnd_7218477 : Nat := 3706548294425059409240335

theorem tailTrace_7218477 : CollatzResearch.WordTrace tailWord_7218477 prefixEnd_7218477 3706548294425059409240335 := by
  unfold tailWord_7218477
  simp only [CollatzResearch.WordTrace]
  refine ⟨263279485469698121567077685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175519656979798747711385123 263279485469698121567077685)
  ·
    refine ⟨24682451762784198896913533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263279485469698121567077685 24682451762784198896913533)
    ·
      refine ⟨9255919411044074586342575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24682451762784198896913533 9255919411044074586342575)
      ·
        refine ⟨13883879116566111879513863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255919411044074586342575 13883879116566111879513863)
        ·
          refine ⟨20825818674849167819270795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13883879116566111879513863 20825818674849167819270795)
          ·
            refine ⟨31238728012273751728906193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20825818674849167819270795 31238728012273751728906193)
            ·
              refine ⟨23429046009205313796679645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31238728012273751728906193 23429046009205313796679645)
              ·
                refine ⟨8785892253451992673754867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23429046009205313796679645 8785892253451992673754867)
                ·
                  refine ⟨13178838380177989010632301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785892253451992673754867 13178838380177989010632301)
                  ·
                    refine ⟨4942064392566745878987113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13178838380177989010632301 4942064392566745878987113)
                    ·
                      refine ⟨3706548294425059409240335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942064392566745878987113 3706548294425059409240335)
                      ·
                        rfl

theorem cell23_7218477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7218477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218477 prefixEnd_7218477 := by exact prefixLift 7218477
  have htrace : WordTrace (prefixWord ++ tailWord_7218477) baseStart_7218477 baseEnd_7218477 := by
    simpa [prefixWord, tailWord_7218477, baseEnd_7218477] using wordTrace_append hprefix tailTrace_7218477
  have hstable : (prefixWord ++ tailWord_7218477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218477).length < 2 ^ (prefixWord ++ tailWord_7218477).sum := by decide
  have hdescent : baseEnd_7218477 < baseStart_7218477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218490 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2]
def baseStart_7218490 : Nat := 118140960795 + 7218490 * 2 ^ 59
def prefixEnd_7218490 : Nat := 4983230072969 + 3 ^ 40 * 7218490 * 2
def baseEnd_7218490 : Nat := 3706554969673567858377775

theorem tailTrace_7218490 : CollatzResearch.WordTrace tailWord_7218490 prefixEnd_7218490 3706554969673567858377775 := by
  unfold tailWord_7218490
  simp only [CollatzResearch.WordTrace]
  refine ⟨65819989904662756196825231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175519973079100683191533949 65819989904662756196825231)
  ·
    refine ⟨98729984856994134295237847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65819989904662756196825231 98729984856994134295237847)
    ·
      refine ⟨148094977285491201442856771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98729984856994134295237847 148094977285491201442856771)
      ·
        refine ⟨222142465928236802164285157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148094977285491201442856771 222142465928236802164285157)
        ·
          refine ⟨41651712361544400405803467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222142465928236802164285157 41651712361544400405803467)
          ·
            refine ⟨62477568542316600608705201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41651712361544400405803467 62477568542316600608705201)
            ·
              refine ⟨46858176406737450456528901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62477568542316600608705201 46858176406737450456528901)
              ·
                refine ⟨8785908076263271960599169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46858176406737450456528901 8785908076263271960599169)
                ·
                  refine ⟨6589431057197453970449377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8785908076263271960599169 6589431057197453970449377)
                  ·
                    refine ⟨4942073292898090477837033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6589431057197453970449377 4942073292898090477837033)
                    ·
                      refine ⟨3706554969673567858377775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942073292898090477837033 3706554969673567858377775)
                      ·
                        rfl

theorem cell23_7218490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_7218490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218490 prefixEnd_7218490 := by exact prefixLift 7218490
  have htrace : WordTrace (prefixWord ++ tailWord_7218490) baseStart_7218490 baseEnd_7218490 := by
    simpa [prefixWord, tailWord_7218490, baseEnd_7218490] using wordTrace_append hprefix tailTrace_7218490
  have hstable : (prefixWord ++ tailWord_7218490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218490).length < 2 ^ (prefixWord ++ tailWord_7218490).sum := by decide
  have hdescent : baseEnd_7218490 < baseStart_7218490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218506 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_7218506 : Nat := 118140960795 + 7218506 * 2 ^ 59
def prefixEnd_7218506 : Nat := 4983230072969 + 3 ^ 40 * 7218506 * 2
def baseEnd_7218506 : Nat := 3706563185364039795777701

theorem tailTrace_7218506 : CollatzResearch.WordTrace tailWord_7218506 prefixEnd_7218506 3706563185364039795777701 := by
  unfold tailWord_7218506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820135796648264879970843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175520362124395373013255581 65820135796648264879970843)
  ·
    refine ⟨98730203694972397319956265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65820135796648264879970843 98730203694972397319956265)
    ·
      refine ⟨74047652771229297989967199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98730203694972397319956265 74047652771229297989967199)
      ·
        refine ⟨111071479156843946984950799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74047652771229297989967199 111071479156843946984950799)
        ·
          refine ⟨166607218735265920477426199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111071479156843946984950799 166607218735265920477426199)
          ·
            refine ⟨249910828102898880716139299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166607218735265920477426199 249910828102898880716139299)
            ·
              refine ⟨374866242154348321074208949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249910828102898880716139299 374866242154348321074208949)
              ·
                refine ⟨35143710201970155100707089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374866242154348321074208949 35143710201970155100707089)
                ·
                  refine ⟨26357782651477616325530317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35143710201970155100707089 26357782651477616325530317)
                  ·
                    refine ⟨9884168494304106122073869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26357782651477616325530317 9884168494304106122073869)
                    ·
                      refine ⟨3706563185364039795777701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884168494304106122073869 3706563185364039795777701)
                      ·
                        rfl

theorem cell23_7218506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_7218506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218506 prefixEnd_7218506 := by exact prefixLift 7218506
  have htrace : WordTrace (prefixWord ++ tailWord_7218506) baseStart_7218506 baseEnd_7218506 := by
    simpa [prefixWord, tailWord_7218506, baseEnd_7218506] using wordTrace_append hprefix tailTrace_7218506
  have hstable : (prefixWord ++ tailWord_7218506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218506).length < 2 ^ (prefixWord ++ tailWord_7218506).sum := by decide
  have hdescent : baseEnd_7218506 < baseStart_7218506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218563 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 6, 2]
def baseStart_7218563 : Nat := 118140960795 + 7218563 * 2 ^ 59
def prefixEnd_7218563 : Nat := 4983230072969 + 3 ^ 40 * 7218563 * 2
def baseEnd_7218563 : Nat := 3706592453761346072764939

theorem tailTrace_7218563 : CollatzResearch.WordTrace tailWord_7218563 prefixEnd_7218563 3706592453761346072764939 := by
  unfold tailWord_7218563
  simp only [CollatzResearch.WordTrace]
  refine ⟨263282622147386558254708343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175521748098257705503138895 263282622147386558254708343)
  ·
    refine ⟨394923933221079837382062515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263282622147386558254708343 394923933221079837382062515)
    ·
      refine ⟨592385899831619756073093773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394923933221079837382062515 592385899831619756073093773)
      ·
        refine ⟨222144712436857408527410165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592385899831619756073093773 222144712436857408527410165)
        ·
          refine ⟨20826066790955382049444703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222144712436857408527410165 20826066790955382049444703)
          ·
            refine ⟨31239100186433073074167055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20826066790955382049444703 31239100186433073074167055)
            ·
              refine ⟨46858650279649609611250583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31239100186433073074167055 46858650279649609611250583)
              ·
                refine ⟨70287975419474414416875875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46858650279649609611250583 70287975419474414416875875)
                ·
                  refine ⟨105431963129211621625313813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70287975419474414416875875 105431963129211621625313813)
                  ·
                    refine ⟨4942123271681794763686585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105431963129211621625313813 4942123271681794763686585)
                    ·
                      refine ⟨3706592453761346072764939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942123271681794763686585 3706592453761346072764939)
                      ·
                        rfl

theorem cell23_7218563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_7218563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218563 prefixEnd_7218563 := by exact prefixLift 7218563
  have htrace : WordTrace (prefixWord ++ tailWord_7218563) baseStart_7218563 baseEnd_7218563 := by
    simpa [prefixWord, tailWord_7218563, baseEnd_7218563] using wordTrace_append hprefix tailTrace_7218563
  have hstable : (prefixWord ++ tailWord_7218563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218563).length < 2 ^ (prefixWord ++ tailWord_7218563).sum := by decide
  have hdescent : baseEnd_7218563 < baseStart_7218563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218580 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_7218580 : Nat := 118140960795 + 7218580 * 2 ^ 59
def prefixEnd_7218580 : Nat := 4983230072969 + 3 ^ 40 * 7218580 * 2
def baseEnd_7218580 : Nat := 3706601182932472506252361

theorem tailTrace_7218580 : CollatzResearch.WordTrace tailWord_7218580 prefixEnd_7218580 3706601182932472506252361 := by
  unfold tailWord_7218580
  simp only [CollatzResearch.WordTrace]
  refine ⟨131641621094162485079038597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175522161458883313438718129 131641621094162485079038597)
  ·
    refine ⟨24682803955155465952319737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131641621094162485079038597 24682803955155465952319737)
    ·
      refine ⟨18512102966366599464239803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24682803955155465952319737 18512102966366599464239803)
      ·
        refine ⟨27768154449549899196359705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18512102966366599464239803 27768154449549899196359705)
        ·
          refine ⟨20826115837162424397269779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27768154449549899196359705 20826115837162424397269779)
          ·
            refine ⟨31239173755743636595904669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20826115837162424397269779 31239173755743636595904669)
            ·
              refine ⟨11714690158403863723464251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31239173755743636595904669 11714690158403863723464251)
              ·
                refine ⟨17572035237605795585196377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11714690158403863723464251 17572035237605795585196377)
                ·
                  refine ⟨13179026428204346688897283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17572035237605795585196377 13179026428204346688897283)
                  ·
                    refine ⟨19768539642306520033345925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13179026428204346688897283 19768539642306520033345925)
                    ·
                      refine ⟨3706601182932472506252361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19768539642306520033345925 3706601182932472506252361)
                      ·
                        rfl

theorem cell23_7218580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_7218580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218580 prefixEnd_7218580 := by exact prefixLift 7218580
  have htrace : WordTrace (prefixWord ++ tailWord_7218580) baseStart_7218580 baseEnd_7218580 := by
    simpa [prefixWord, tailWord_7218580, baseEnd_7218580] using wordTrace_append hprefix tailTrace_7218580
  have hstable : (prefixWord ++ tailWord_7218580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218580).length < 2 ^ (prefixWord ++ tailWord_7218580).sum := by decide
  have hdescent : baseEnd_7218580 < baseStart_7218580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218586 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_7218586 : Nat := 118140960795 + 7218586 * 2 ^ 59
def prefixEnd_7218586 : Nat := 4983230072969 + 3 ^ 40 * 7218586 * 2
def baseEnd_7218586 : Nat := 411844918201822164753037

theorem tailTrace_7218586 : CollatzResearch.WordTrace tailWord_7218586 prefixEnd_7218586 411844918201822164753037 := by
  unfold tailWord_7218586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820865256575808295698903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175522307350868822121863741 65820865256575808295698903)
  ·
    refine ⟨98731297884863712443548355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65820865256575808295698903 98731297884863712443548355)
    ·
      refine ⟨148096946827295568665322533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98731297884863712443548355 148096946827295568665322533)
      ·
        refine ⟨27768177530117919124747975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148096946827295568665322533 27768177530117919124747975)
        ·
          refine ⟨41652266295176878687121963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27768177530117919124747975 41652266295176878687121963)
          ·
            refine ⟨62478399442765318030682945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41652266295176878687121963 62478399442765318030682945)
            ·
              refine ⟨46858799582073988523012209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62478399442765318030682945 46858799582073988523012209)
              ·
                refine ⟨35144099686555491392259157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46858799582073988523012209 35144099686555491392259157)
                ·
                  refine ⟨411844918201822164753037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35144099686555491392259157 411844918201822164753037)
                  ·
                    rfl

theorem cell23_7218586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_7218586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218586 prefixEnd_7218586 := by exact prefixLift 7218586
  have htrace : WordTrace (prefixWord ++ tailWord_7218586) baseStart_7218586 baseEnd_7218586 := by
    simpa [prefixWord, tailWord_7218586, baseEnd_7218586] using wordTrace_append hprefix tailTrace_7218586
  have hstable : (prefixWord ++ tailWord_7218586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218586).length < 2 ^ (prefixWord ++ tailWord_7218586).sum := by decide
  have hdescent : baseEnd_7218586 < baseStart_7218586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218616 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_7218616 : Nat := 118140960795 + 7218616 * 2 ^ 59
def prefixEnd_7218616 : Nat := 4983230072969 + 3 ^ 40 * 7218616 * 2
def baseEnd_7218616 : Nat := 1235539889412011455134065

theorem tailTrace_7218616 : CollatzResearch.WordTrace tailWord_7218616 prefixEnd_7218616 1235539889412011455134065 := by
  unfold tailWord_7218616
  simp only [CollatzResearch.WordTrace]
  refine ⟨131642277608097274153193851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175523036810796365537591801 131642277608097274153193851)
  ·
    refine ⟨197463416412145911229790777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131642277608097274153193851 197463416412145911229790777)
    ·
      refine ⟨148097562309109433422343083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197463416412145911229790777 148097562309109433422343083)
      ·
        refine ⟨222146343463664150133514625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148097562309109433422343083 222146343463664150133514625)
        ·
          refine ⟨166609757597748112600135969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222146343463664150133514625 166609757597748112600135969)
          ·
            refine ⟨124957318198311084450101977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166609757597748112600135969 124957318198311084450101977)
            ·
              refine ⟨93717988648733313337576483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124957318198311084450101977 93717988648733313337576483)
              ·
                refine ⟨140576982973099970006364725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93717988648733313337576483 140576982973099970006364725)
                ·
                  refine ⟨13179092153728122188096693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140576982973099970006364725 13179092153728122188096693)
                  ·
                    refine ⟨1235539889412011455134065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13179092153728122188096693 1235539889412011455134065)
                    ·
                      rfl

theorem cell23_7218616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_7218616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218616 prefixEnd_7218616 := by exact prefixLift 7218616
  have htrace : WordTrace (prefixWord ++ tailWord_7218616) baseStart_7218616 baseEnd_7218616 := by
    simpa [prefixWord, tailWord_7218616, baseEnd_7218616] using wordTrace_append hprefix tailTrace_7218616
  have hstable : (prefixWord ++ tailWord_7218616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218616).length < 2 ^ (prefixWord ++ tailWord_7218616).sum := by decide
  have hdescent : baseEnd_7218616 < baseStart_7218616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218664 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_7218664 : Nat := 118140960795 + 7218664 * 2 ^ 59
def prefixEnd_7218664 : Nat := 4983230072969 + 3 ^ 40 * 7218664 * 2
def baseEnd_7218664 : Nat := 3706644315307450177601975

theorem tailTrace_7218664 : CollatzResearch.WordTrace tailWord_7218664 prefixEnd_7218664 3706644315307450177601975 := by
  unfold tailWord_7218664
  simp only [CollatzResearch.WordTrace]
  refine ⟨131643152960010326252067523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175524203946680435002756697 131643152960010326252067523)
  ·
    refine ⟨197464729440015489378101285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131643152960010326252067523 197464729440015489378101285)
    ·
      refine ⟨37024636770002904258393991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197464729440015489378101285 37024636770002904258393991)
      ·
        refine ⟨55536955155004356387590987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37024636770002904258393991 55536955155004356387590987)
        ·
          refine ⟨83305432732506534581386481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55536955155004356387590987 83305432732506534581386481)
          ·
            refine ⟨62479074549379900936039861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83305432732506534581386481 62479074549379900936039861)
            ·
              refine ⟨5857413239004365712753737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62479074549379900936039861 5857413239004365712753737)
              ·
                refine ⟨4393059929253274284565303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5857413239004365712753737 4393059929253274284565303)
                ·
                  refine ⟨6589589893879911426847955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393059929253274284565303 6589589893879911426847955)
                  ·
                    refine ⟨9884384840819867140271933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6589589893879911426847955 9884384840819867140271933)
                    ·
                      refine ⟨3706644315307450177601975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884384840819867140271933 3706644315307450177601975)
                      ·
                        rfl

theorem cell23_7218664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_7218664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218664 prefixEnd_7218664 := by exact prefixLift 7218664
  have htrace : WordTrace (prefixWord ++ tailWord_7218664) baseStart_7218664 baseEnd_7218664 := by
    simpa [prefixWord, tailWord_7218664, baseEnd_7218664] using wordTrace_append hprefix tailTrace_7218664
  have hstable : (prefixWord ++ tailWord_7218664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218664).length < 2 ^ (prefixWord ++ tailWord_7218664).sum := by decide
  have hdescent : baseEnd_7218664 < baseStart_7218664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218673 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_7218673 : Nat := 118140960795 + 7218673 * 2 ^ 59
def prefixEnd_7218673 : Nat := 4983230072969 + 3 ^ 40 * 7218673 * 2
def baseEnd_7218673 : Nat := 3706648936633340642389433

theorem tailTrace_7218673 : CollatzResearch.WordTrace tailWord_7218673 prefixEnd_7218673 3706648936633340642389433 := by
  unfold tailWord_7218673
  simp only [CollatzResearch.WordTrace]
  refine ⟨263286634176988047041212673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175524422784658698027475115 263286634176988047041212673)
  ·
    refine ⟨197464975632741035280909505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263286634176988047041212673 197464975632741035280909505)
    ·
      refine ⟨148098731724555776460682129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197464975632741035280909505 148098731724555776460682129)
      ·
        refine ⟨111074048793416832345511597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148098731724555776460682129 111074048793416832345511597)
        ·
          refine ⟨41652768297531312129566849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111074048793416832345511597 41652768297531312129566849)
          ·
            refine ⟨31239576223148484097175137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41652768297531312129566849 31239576223148484097175137)
            ·
              refine ⟨23429682167361363072881353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31239576223148484097175137 23429682167361363072881353)
              ·
                refine ⟨17572261625521022304661015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23429682167361363072881353 17572261625521022304661015)
                ·
                  refine ⟨26358392438281533456991523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17572261625521022304661015 26358392438281533456991523)
                  ·
                    refine ⟨39537588657422300185487285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26358392438281533456991523 39537588657422300185487285)
                    ·
                      refine ⟨3706648936633340642389433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39537588657422300185487285 3706648936633340642389433)
                      ·
                        rfl

theorem cell23_7218673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_7218673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218673 prefixEnd_7218673 := by exact prefixLift 7218673
  have htrace : WordTrace (prefixWord ++ tailWord_7218673) baseStart_7218673 baseEnd_7218673 := by
    simpa [prefixWord, tailWord_7218673, baseEnd_7218673] using wordTrace_append hprefix tailTrace_7218673
  have hstable : (prefixWord ++ tailWord_7218673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218673).length < 2 ^ (prefixWord ++ tailWord_7218673).sum := by decide
  have hdescent : baseEnd_7218673 < baseStart_7218673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218680 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 2, 4]
def baseStart_7218680 : Nat := 118140960795 + 7218680 * 2 ^ 59
def prefixEnd_7218680 : Nat := 4983230072969 + 3 ^ 40 * 7218680 * 2
def baseEnd_7218680 : Nat := 1235550843665974038333967

theorem tailTrace_7218680 : CollatzResearch.WordTrace tailWord_7218680 prefixEnd_7218680 1235550843665974038333967 := by
  unfold tailWord_7218680
  simp only [CollatzResearch.WordTrace]
  refine ⟨131643444743981343618358747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175524592991975124824478329 131643444743981343618358747)
  ·
    refine ⟨197465167115972015427538121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131643444743981343618358747 197465167115972015427538121)
    ·
      refine ⟨148098875336979011570653591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197465167115972015427538121 148098875336979011570653591)
      ·
        refine ⟨222148313005468517355980387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148098875336979011570653591 222148313005468517355980387)
        ·
          refine ⟨333222469508202776033970581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222148313005468517355980387 333222469508202776033970581)
          ·
            refine ⟨15619803258197005126592371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 333222469508202776033970581 15619803258197005126592371)
            ·
              refine ⟨23429704887295507689888557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15619803258197005126592371 23429704887295507689888557)
              ·
                refine ⟨8786139332735815383708209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23429704887295507689888557 8786139332735815383708209)
                ·
                  refine ⟨6589604499551861537781157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8786139332735815383708209 6589604499551861537781157)
                  ·
                    refine ⟨1235550843665974038333967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6589604499551861537781157 1235550843665974038333967)
                    ·
                      rfl

theorem cell23_7218680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_7218680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218680 prefixEnd_7218680 := by exact prefixLift 7218680
  have htrace : WordTrace (prefixWord ++ tailWord_7218680) baseStart_7218680 baseEnd_7218680 := by
    simpa [prefixWord, tailWord_7218680, baseEnd_7218680] using wordTrace_append hprefix tailTrace_7218680
  have hstable : (prefixWord ++ tailWord_7218680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218680).length < 2 ^ (prefixWord ++ tailWord_7218680).sum := by decide
  have hdescent : baseEnd_7218680 < baseStart_7218680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218700 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_7218700 : Nat := 118140960795 + 7218700 * 2 ^ 59
def prefixEnd_7218700 : Nat := 4983230072969 + 3 ^ 40 * 7218700 * 2
def baseEnd_7218700 : Nat := 3706662800611012036751809

theorem tailTrace_7218700 : CollatzResearch.WordTrace tailWord_7218700 prefixEnd_7218700 3706662800611012036751809 := by
  unfold tailWord_7218700
  simp only [CollatzResearch.WordTrace]
  refine ⟨131643809473945115326222777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175525079298593487101630369 131643809473945115326222777)
  ·
    refine ⟨98732857105458836494667083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131643809473945115326222777 98732857105458836494667083)
    ·
      refine ⟨148099285658188254742000625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98732857105458836494667083 148099285658188254742000625)
      ·
        refine ⟨111074464243641191056500469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148099285658188254742000625 111074464243641191056500469)
        ·
          refine ⟨10413231022841361661546919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111074464243641191056500469 10413231022841361661546919)
          ·
            refine ⟨15619846534262042492320379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413231022841361661546919 15619846534262042492320379)
            ·
              refine ⟨23429769801393063738480569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15619846534262042492320379 23429769801393063738480569)
              ·
                refine ⟨17572327351044797803860427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23429769801393063738480569 17572327351044797803860427)
                ·
                  refine ⟨26358491026567196705790641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17572327351044797803860427 26358491026567196705790641)
                  ·
                    refine ⟨19768868269925397529342981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26358491026567196705790641 19768868269925397529342981)
                    ·
                      refine ⟨3706662800611012036751809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19768868269925397529342981 3706662800611012036751809)
                      ·
                        rfl

theorem cell23_7218700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_7218700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218700 prefixEnd_7218700 := by exact prefixLift 7218700
  have htrace : WordTrace (prefixWord ++ tailWord_7218700) baseStart_7218700 baseEnd_7218700 := by
    simpa [prefixWord, tailWord_7218700, baseEnd_7218700] using wordTrace_append hprefix tailTrace_7218700
  have hstable : (prefixWord ++ tailWord_7218700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218700).length < 2 ^ (prefixWord ++ tailWord_7218700).sum := by decide
  have hdescent : baseEnd_7218700 < baseStart_7218700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218701 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7218701 : Nat := 118140960795 + 7218701 * 2 ^ 59
def prefixEnd_7218701 : Nat := 4983230072969 + 3 ^ 40 * 7218701 * 2
def baseEnd_7218701 : Nat := 1235554438030555510946435

theorem tailTrace_7218701 : CollatzResearch.WordTrace tailWord_7218701 prefixEnd_7218701 1235554438030555510946435 := by
  unfold tailWord_7218701
  simp only [CollatzResearch.WordTrace]
  refine ⟨263287655420886607823231957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175525103613924405215487971 263287655420886607823231957)
  ·
    refine ⟨6170804423927029870856999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 263287655420886607823231957 6170804423927029870856999)
    ·
      refine ⟨9256206635890544806285499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6170804423927029870856999 9256206635890544806285499)
      ·
        refine ⟨13884309953835817209428249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256206635890544806285499 13884309953835817209428249)
        ·
          refine ⟨10413232465376862907071187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13884309953835817209428249 10413232465376862907071187)
          ·
            refine ⟨15619848698065294360606781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413232465376862907071187 15619848698065294360606781)
            ·
              refine ⟨5857443261774485385227543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15619848698065294360606781 5857443261774485385227543)
              ·
                refine ⟨8786164892661728077841315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857443261774485385227543 8786164892661728077841315)
                ·
                  refine ⟨13179247338992592116761973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786164892661728077841315 13179247338992592116761973)
                  ·
                    refine ⟨1235554438030555510946435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13179247338992592116761973 1235554438030555510946435)
                    ·
                      rfl

theorem cell23_7218701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7218701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218701 prefixEnd_7218701 := by exact prefixLift 7218701
  have htrace : WordTrace (prefixWord ++ tailWord_7218701) baseStart_7218701 baseEnd_7218701 := by
    simpa [prefixWord, tailWord_7218701, baseEnd_7218701] using wordTrace_append hprefix tailTrace_7218701
  have hstable : (prefixWord ++ tailWord_7218701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218701).length < 2 ^ (prefixWord ++ tailWord_7218701).sum := by decide
  have hdescent : baseEnd_7218701 < baseStart_7218701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218707 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 1, 2, 3]
def baseStart_7218707 : Nat := 118140960795 + 7218707 * 2 ^ 59
def prefixEnd_7218707 : Nat := 4983230072969 + 3 ^ 40 * 7218707 * 2
def baseEnd_7218707 : Nat := 3706666394975593509364277

theorem tailTrace_7218707 : CollatzResearch.WordTrace tailWord_7218707 prefixEnd_7218707 3706666394975593509364277 := by
  unfold tailWord_7218707
  simp only [CollatzResearch.WordTrace]
  refine ⟨263287874258864870847950375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175525249505909913898633583 263287874258864870847950375)
  ·
    refine ⟨394931811388297306271925563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263287874258864870847950375 394931811388297306271925563)
    ·
      refine ⟨592397717082445959407888345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394931811388297306271925563 592397717082445959407888345)
      ·
        refine ⟨444298287811834469555916259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592397717082445959407888345 444298287811834469555916259)
        ·
          refine ⟨666447431717751704333874389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444298287811834469555916259 666447431717751704333874389)
          ·
            refine ⟨15619861680884805570325181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 666447431717751704333874389 15619861680884805570325181)
            ·
              refine ⟨5857448130331802088871943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15619861680884805570325181 5857448130331802088871943)
              ·
                refine ⟨8786172195497703133307915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857448130331802088871943 8786172195497703133307915)
                ·
                  refine ⟨13179258293246554699961873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786172195497703133307915 13179258293246554699961873)
                  ·
                    refine ⟨9884443719934916024971405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13179258293246554699961873 9884443719934916024971405)
                    ·
                      refine ⟨3706666394975593509364277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884443719934916024971405 3706666394975593509364277)
                      ·
                        rfl

theorem cell23_7218707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 2, 3].length) (baseStart_7218707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218707 prefixEnd_7218707 := by exact prefixLift 7218707
  have htrace : WordTrace (prefixWord ++ tailWord_7218707) baseStart_7218707 baseEnd_7218707 := by
    simpa [prefixWord, tailWord_7218707, baseEnd_7218707] using wordTrace_append hprefix tailTrace_7218707
  have hstable : (prefixWord ++ tailWord_7218707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218707).length < 2 ^ (prefixWord ++ tailWord_7218707).sum := by decide
  have hdescent : baseEnd_7218707 < baseStart_7218707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218721 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_7218721 : Nat := 118140960795 + 7218721 * 2 ^ 59
def prefixEnd_7218721 : Nat := 4983230072969 + 3 ^ 40 * 7218721 * 2
def baseEnd_7218721 : Nat := 3706673583704756454589213

theorem tailTrace_7218721 : CollatzResearch.WordTrace tailWord_7218721 prefixEnd_7218721 3706673583704756454589213 := by
  unfold tailWord_7218721
  simp only [CollatzResearch.WordTrace]
  refine ⟨263288384880814151238960017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175525589920542767492640011 263288384880814151238960017)
  ·
    refine ⟨197466288660610613429220013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263288384880814151238960017 197466288660610613429220013)
    ·
      refine ⟨74049858247728980035957505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197466288660610613429220013 74049858247728980035957505)
      ·
        refine ⟨55537393685796735026968129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74049858247728980035957505 55537393685796735026968129)
        ·
          refine ⟨41653045264347551270226097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55537393685796735026968129 41653045264347551270226097)
          ·
            refine ⟨31239783948260663452669573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41653045264347551270226097 31239783948260663452669573)
            ·
              refine ⟨5857459490298874397375545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31239783948260663452669573 5857459490298874397375545)
              ·
                refine ⟨4393094617724155798031659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5857459490298874397375545 4393094617724155798031659)
                ·
                  refine ⟨6589641926586233697047489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393094617724155798031659 6589641926586233697047489)
                  ·
                    refine ⟨4942231444939675272785617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6589641926586233697047489 4942231444939675272785617)
                    ·
                      refine ⟨3706673583704756454589213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942231444939675272785617 3706673583704756454589213)
                      ·
                        rfl

theorem cell23_7218721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_7218721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218721 prefixEnd_7218721 := by exact prefixLift 7218721
  have htrace : WordTrace (prefixWord ++ tailWord_7218721) baseStart_7218721 baseEnd_7218721 := by
    simpa [prefixWord, tailWord_7218721, baseEnd_7218721] using wordTrace_append hprefix tailTrace_7218721
  have hstable : (prefixWord ++ tailWord_7218721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218721).length < 2 ^ (prefixWord ++ tailWord_7218721).sum := by decide
  have hdescent : baseEnd_7218721 < baseStart_7218721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218753 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7218753 : Nat := 118140960795 + 7218753 * 2 ^ 59
def prefixEnd_7218753 : Nat := 4983230072969 + 3 ^ 40 * 7218753 * 2
def baseEnd_7218753 : Nat := 1235563338361900109796355

theorem tailTrace_7218753 : CollatzResearch.WordTrace tailWord_7218753 prefixEnd_7218753 1235563338361900109796355 := by
  unfold tailWord_7218753
  simp only [CollatzResearch.WordTrace]
  refine ⟨263289552016698220704124913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175526368011132147136083275 263289552016698220704124913)
  ·
    refine ⟨197467164012523665528093685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263289552016698220704124913 197467164012523665528093685)
    ·
      refine ⟨18512546626174093643258783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197467164012523665528093685 18512546626174093643258783)
      ·
        refine ⟨27768819939261140464888175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18512546626174093643258783 27768819939261140464888175)
        ·
          refine ⟨41653229908891710697332263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27768819939261140464888175 41653229908891710697332263)
          ·
            refine ⟨62479844863337566045998395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41653229908891710697332263 62479844863337566045998395)
            ·
              refine ⟨93719767295006349068997593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62479844863337566045998395 93719767295006349068997593)
              ·
                refine ⟨70289825471254761801748195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93719767295006349068997593 70289825471254761801748195)
                ·
                  refine ⟨105434738206882142702622293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70289825471254761801748195 105434738206882142702622293)
                  ·
                    refine ⟨1235563338361900109796355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105434738206882142702622293 1235563338361900109796355)
                    ·
                      rfl

theorem cell23_7218753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7218753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218753 prefixEnd_7218753 := by exact prefixLift 7218753
  have htrace : WordTrace (prefixWord ++ tailWord_7218753) baseStart_7218753 baseEnd_7218753 := by
    simpa [prefixWord, tailWord_7218753, baseEnd_7218753] using wordTrace_append hprefix tailTrace_7218753
  have hstable : (prefixWord ++ tailWord_7218753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218753).length < 2 ^ (prefixWord ++ tailWord_7218753).sum := by decide
  have hdescent : baseEnd_7218753 < baseStart_7218753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218758 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7218758 : Nat := 118140960795 + 7218758 * 2 ^ 59
def prefixEnd_7218758 : Nat := 4983230072969 + 3 ^ 40 * 7218758 * 2
def baseEnd_7218758 : Nat := 3706692582488972809826543

theorem tailTrace_7218758 : CollatzResearch.WordTrace tailWord_7218758 prefixEnd_7218758 3706692582488972809826543 := by
  unfold tailWord_7218758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227804199427503329939279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175526489587786737705371285 8227804199427503329939279)
  ·
    refine ⟨12341706299141254994908919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8227804199427503329939279 12341706299141254994908919)
    ·
      refine ⟨18512559448711882492363379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12341706299141254994908919 18512559448711882492363379)
      ·
        refine ⟨27768839173067823738545069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18512559448711882492363379 27768839173067823738545069)
        ·
          refine ⟨10413314689900433901954401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27768839173067823738545069 10413314689900433901954401)
          ·
            refine ⟨7809986017425325426465801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10413314689900433901954401 7809986017425325426465801)
            ·
              refine ⟨5857489513068994069849351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7809986017425325426465801 5857489513068994069849351)
              ·
                refine ⟨8786234269603491104774027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857489513068994069849351 8786234269603491104774027)
                ·
                  refine ⟨13179351404405236657161041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786234269603491104774027 13179351404405236657161041)
                  ·
                    refine ⟨9884513553303927492870781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13179351404405236657161041 9884513553303927492870781)
                    ·
                      refine ⟨3706692582488972809826543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884513553303927492870781 3706692582488972809826543)
                      ·
                        rfl

theorem cell23_7218758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7218758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218758 prefixEnd_7218758 := by exact prefixLift 7218758
  have htrace : WordTrace (prefixWord ++ tailWord_7218758) baseStart_7218758 baseEnd_7218758 := by
    simpa [prefixWord, tailWord_7218758, baseEnd_7218758] using wordTrace_append hprefix tailTrace_7218758
  have hstable : (prefixWord ++ tailWord_7218758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218758).length < 2 ^ (prefixWord ++ tailWord_7218758).sum := by decide
  have hdescent : baseEnd_7218758 < baseStart_7218758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218764 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7218764 : Nat := 118140960795 + 7218764 * 2 ^ 59
def prefixEnd_7218764 : Nat := 4983230072969 + 3 ^ 40 * 7218764 * 2
def baseEnd_7218764 : Nat := 3706695663372899786351515

theorem tailTrace_7218764 : CollatzResearch.WordTrace tailWord_7218764 prefixEnd_7218764 3706695663372899786351515 := by
  unfold tailWord_7218764
  simp only [CollatzResearch.WordTrace]
  refine ⟨131644976609829184791387673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175526635479772246388516897 131644976609829184791387673)
  ·
    refine ⟨98733732457371888593540755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131644976609829184791387673 98733732457371888593540755)
    ·
      refine ⟨148100598686057832890311133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98733732457371888593540755 148100598686057832890311133)
      ·
        refine ⟨55537724507271687333866675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148100598686057832890311133 55537724507271687333866675)
        ·
          refine ⟨83306586760907531000800013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55537724507271687333866675 83306586760907531000800013)
          ·
            refine ⟨31239970035340324125300005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83306586760907531000800013 31239970035340324125300005)
            ·
              refine ⟨5857494381626310773493751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31239970035340324125300005 5857494381626310773493751)
              ·
                refine ⟨8786241572439466160240627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857494381626310773493751 8786241572439466160240627)
                ·
                  refine ⟨13179362358659199240360941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786241572439466160240627 13179362358659199240360941)
                  ·
                    refine ⟨4942260884497199715135353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13179362358659199240360941 4942260884497199715135353)
                    ·
                      refine ⟨3706695663372899786351515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942260884497199715135353 3706695663372899786351515)
                      ·
                        rfl

theorem cell23_7218764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7218764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218764 prefixEnd_7218764 := by exact prefixLift 7218764
  have htrace : WordTrace (prefixWord ++ tailWord_7218764) baseStart_7218764 baseEnd_7218764 := by
    simpa [prefixWord, tailWord_7218764, baseEnd_7218764] using wordTrace_append hprefix tailTrace_7218764
  have hstable : (prefixWord ++ tailWord_7218764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218764).length < 2 ^ (prefixWord ++ tailWord_7218764).sum := by decide
  have hdescent : baseEnd_7218764 < baseStart_7218764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218794 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7218794 : Nat := 118140960795 + 7218794 * 2 ^ 59
def prefixEnd_7218794 : Nat := 4983230072969 + 3 ^ 40 * 7218794 * 2
def baseEnd_7218794 : Nat := 3706711067792534668976377

theorem tailTrace_7218794 : CollatzResearch.WordTrace tailWord_7218794 prefixEnd_7218794 3706711067792534668976377 := by
  unfold tailWord_7218794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65822761852387421176591859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175527364939699789804244957 65822761852387421176591859)
  ·
    refine ⟨98734142778581131764887789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65822761852387421176591859 98734142778581131764887789)
    ·
      refine ⟨37025303541967924411832921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98734142778581131764887789 37025303541967924411832921)
      ·
        refine ⟨27768977656475943308874691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37025303541967924411832921 27768977656475943308874691)
        ·
          refine ⟨41653466484713914963312037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27768977656475943308874691 41653466484713914963312037)
          ·
            refine ⟨7810024965883859055621007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41653466484713914963312037 7810024965883859055621007)
            ·
              refine ⟨11715037448825788583431511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810024965883859055621007 11715037448825788583431511)
              ·
                refine ⟨17572556173238682875147267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11715037448825788583431511 17572556173238682875147267)
                ·
                  refine ⟨26358834259858024312720901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17572556173238682875147267 26358834259858024312720901)
                  ·
                    refine ⟨4942281423723379558635169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26358834259858024312720901 4942281423723379558635169)
                    ·
                      refine ⟨3706711067792534668976377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942281423723379558635169 3706711067792534668976377)
                      ·
                        rfl

theorem cell23_7218794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7218794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218794 prefixEnd_7218794 := by exact prefixLift 7218794
  have htrace : WordTrace (prefixWord ++ tailWord_7218794) baseStart_7218794 baseEnd_7218794 := by
    simpa [prefixWord, tailWord_7218794, baseEnd_7218794] using wordTrace_append hprefix tailTrace_7218794
  have hstable : (prefixWord ++ tailWord_7218794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218794).length < 2 ^ (prefixWord ++ tailWord_7218794).sum := by decide
  have hdescent : baseEnd_7218794 < baseStart_7218794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218817 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 5]
def baseStart_7218817 : Nat := 118140960795 + 7218817 * 2 ^ 59
def prefixEnd_7218817 : Nat := 4983230072969 + 3 ^ 40 * 7218817 * 2
def baseEnd_7218817 : Nat := 411858097538620897665419

theorem tailTrace_7218817 : CollatzResearch.WordTrace tailWord_7218817 prefixEnd_7218817 411858097538620897665419 := by
  unfold tailWord_7218817
  simp only [CollatzResearch.WordTrace]
  refine ⟨263291886288466359634454705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175527924192310906422969803 263291886288466359634454705)
  ·
    refine ⟨197468914716349769725841029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263291886288466359634454705 197468914716349769725841029)
    ·
      refine ⟨37025421509315581823595193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197468914716349769725841029 37025421509315581823595193)
      ·
        refine ⟨27769066131986686367696395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37025421509315581823595193 27769066131986686367696395)
        ·
          refine ⟨41653599197980029551544593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27769066131986686367696395 41653599197980029551544593)
          ·
            refine ⟨31240199398485022163658445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41653599197980029551544593 31240199398485022163658445)
            ·
              refine ⟨11715074774431883311371917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31240199398485022163658445 11715074774431883311371917)
              ·
                refine ⟨4393153040411956241764469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11715074774431883311371917 4393153040411956241764469)
                ·
                  refine ⟨411858097538620897665419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393153040411956241764469 411858097538620897665419)
                  ·
                    rfl

theorem cell23_7218817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 5].length) (baseStart_7218817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218817 prefixEnd_7218817 := by exact prefixLift 7218817
  have htrace : WordTrace (prefixWord ++ tailWord_7218817) baseStart_7218817 baseEnd_7218817 := by
    simpa [prefixWord, tailWord_7218817, baseEnd_7218817] using wordTrace_append hprefix tailTrace_7218817
  have hstable : (prefixWord ++ tailWord_7218817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218817).length < 2 ^ (prefixWord ++ tailWord_7218817).sum := by decide
  have hdescent : baseEnd_7218817 < baseStart_7218817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218830 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_7218830 : Nat := 118140960795 + 7218830 * 2 ^ 59
def prefixEnd_7218830 : Nat := 4983230072969 + 3 ^ 40 * 7218830 * 2
def baseEnd_7218830 : Nat := 1235576517698698842708737

theorem tailTrace_7218830 : CollatzResearch.WordTrace tailWord_7218830 prefixEnd_7218830 1235576517698698842708737 := by
  unfold tailWord_7218830
  simp only [CollatzResearch.WordTrace]
  refine ⟨32911545054677407856834743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175528240291612841903118629 32911545054677407856834743)
  ·
    refine ⟨49367317582016111785252115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32911545054677407856834743 49367317582016111785252115)
    ·
      refine ⟨74050976373024167677878173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49367317582016111785252115 74050976373024167677878173)
      ·
        refine ⟨27769116139884062879204315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74050976373024167677878173 27769116139884062879204315)
        ·
          refine ⟨41653674209826094318806473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27769116139884062879204315 41653674209826094318806473)
          ·
            refine ⟨31240255657369570739104855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41653674209826094318806473 31240255657369570739104855)
            ·
              refine ⟨46860383486054356108657283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31240255657369570739104855 46860383486054356108657283)
              ·
                refine ⟨70290575229081534162985925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46860383486054356108657283 70290575229081534162985925)
                ·
                  refine ⟨13179482855452787655559861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70290575229081534162985925 13179482855452787655559861)
                  ·
                    refine ⟨1235576517698698842708737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13179482855452787655559861 1235576517698698842708737)
                    ·
                      rfl

theorem cell23_7218830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_7218830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218830 prefixEnd_7218830 := by exact prefixLift 7218830
  have htrace : WordTrace (prefixWord ++ tailWord_7218830) baseStart_7218830 baseEnd_7218830 := by
    simpa [prefixWord, tailWord_7218830, baseEnd_7218830] using wordTrace_append hprefix tailTrace_7218830
  have hstable : (prefixWord ++ tailWord_7218830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218830).length < 2 ^ (prefixWord ++ tailWord_7218830).sum := by decide
  have hdescent : baseEnd_7218830 < baseStart_7218830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218833 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_7218833 : Nat := 118140960795 + 7218833 * 2 ^ 59
def prefixEnd_7218833 : Nat := 4983230072969 + 3 ^ 40 * 7218833 * 2
def baseEnd_7218833 : Nat := 3706731093538060016388697

theorem tailTrace_7218833 : CollatzResearch.WordTrace tailWord_7218833 prefixEnd_7218833 3706731093538060016388697 := by
  unfold tailWord_7218833
  simp only [CollatzResearch.WordTrace]
  refine ⟨263292469856408394367037153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175528313237605596244691435 263292469856408394367037153)
  ·
    refine ⟨197469352392306295775277865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263292469856408394367037153 197469352392306295775277865)
    ·
      refine ⟨148102014294229721831458399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197469352392306295775277865 148102014294229721831458399)
      ·
        refine ⟨222153021441344582747187599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148102014294229721831458399 222153021441344582747187599)
        ·
          refine ⟨333229532162016874120781399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222153021441344582747187599 333229532162016874120781399)
          ·
            refine ⟨499844298243025311181172099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333229532162016874120781399 499844298243025311181172099)
            ·
              refine ⟨749766447364537966771758149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499844298243025311181172099 749766447364537966771758149)
              ·
                refine ⟨140581208880850868769704653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749766447364537966771758149 140581208880850868769704653)
                ·
                  refine ⟨52717953330319075788639245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140581208880850868769704653 52717953330319075788639245)
                  ·
                    refine ⟨19769232498869653420739717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52717953330319075788639245 19769232498869653420739717)
                    ·
                      refine ⟨3706731093538060016388697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19769232498869653420739717 3706731093538060016388697)
                      ·
                        rfl

theorem cell23_7218833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_7218833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218833 prefixEnd_7218833 := by exact prefixLift 7218833
  have htrace : WordTrace (prefixWord ++ tailWord_7218833) baseStart_7218833 baseEnd_7218833 := by
    simpa [prefixWord, tailWord_7218833, baseEnd_7218833] using wordTrace_append hprefix tailTrace_7218833
  have hstable : (prefixWord ++ tailWord_7218833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218833).length < 2 ^ (prefixWord ++ tailWord_7218833).sum := by decide
  have hdescent : baseEnd_7218833 < baseStart_7218833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218834 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_7218834 : Nat := 118140960795 + 7218834 * 2 ^ 59
def prefixEnd_7218834 : Nat := 4983230072969 + 3 ^ 40 * 7218834 * 2
def baseEnd_7218834 : Nat := 411859067446523834719577

theorem tailTrace_7218834 : CollatzResearch.WordTrace tailWord_7218834 prefixEnd_7218834 411859067446523834719577 := by
  unfold tailWord_7218834
  simp only [CollatzResearch.WordTrace]
  refine ⟨65823126582351192884455889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175528337552936514358549037 65823126582351192884455889)
  ·
    refine ⟨49367344936763394663341917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65823126582351192884455889 49367344936763394663341917)
    ·
      refine ⟨18512754351286272998753219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49367344936763394663341917 18512754351286272998753219)
      ·
        refine ⟨27769131526929409498129829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18512754351286272998753219 27769131526929409498129829)
        ·
          refine ⟨5206712161299264280899343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27769131526929409498129829 5206712161299264280899343)
          ·
            refine ⟨7810068241948896421349015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206712161299264280899343 7810068241948896421349015)
            ·
              refine ⟨11715102362923344632023523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810068241948896421349015 11715102362923344632023523)
              ·
                refine ⟨17572653544385016948035285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11715102362923344632023523 17572653544385016948035285)
                ·
                  refine ⟨411859067446523834719577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17572653544385016948035285 411859067446523834719577)
                  ·
                    rfl

theorem cell23_7218834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_7218834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218834 prefixEnd_7218834 := by exact prefixLift 7218834
  have htrace : WordTrace (prefixWord ++ tailWord_7218834) baseStart_7218834 baseEnd_7218834 := by
    simpa [prefixWord, tailWord_7218834, baseEnd_7218834] using wordTrace_append hprefix tailTrace_7218834
  have hstable : (prefixWord ++ tailWord_7218834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218834).length < 2 ^ (prefixWord ++ tailWord_7218834).sum := by decide
  have hdescent : baseEnd_7218834 < baseStart_7218834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218840 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7218840 : Nat := 118140960795 + 7218840 * 2 ^ 59
def prefixEnd_7218840 : Nat := 4983230072969 + 3 ^ 40 * 7218840 * 2
def baseEnd_7218840 : Nat := 3706734687902641489001165

theorem tailTrace_7218840 : CollatzResearch.WordTrace tailWord_7218840 prefixEnd_7218840 3706734687902641489001165 := by
  unfold tailWord_7218840
  simp only [CollatzResearch.WordTrace]
  refine ⟨131646362583691517281270987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175528483444922023041694649 131646362583691517281270987)
  ·
    refine ⟨197469543875537275921906481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131646362583691517281270987 197469543875537275921906481)
    ·
      refine ⟨148102157906652956941429861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197469543875537275921906481 148102157906652956941429861)
      ·
        refine ⟨27769154607497429426518099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148102157906652956941429861 27769154607497429426518099)
        ·
          refine ⟨41653731911246144139777149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27769154607497429426518099 41653731911246144139777149)
          ·
            refine ⟨15620149466717304052416431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41653731911246144139777149 15620149466717304052416431)
            ·
              refine ⟨23430224200075956078624647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15620149466717304052416431 23430224200075956078624647)
              ·
                refine ⟨35145336300113934117936971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23430224200075956078624647 35145336300113934117936971)
                ·
                  refine ⟨52718004450170901176905457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35145336300113934117936971 52718004450170901176905457)
                  ·
                    refine ⟨39538503337628175882679093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52718004450170901176905457 39538503337628175882679093)
                    ·
                      refine ⟨3706734687902641489001165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39538503337628175882679093 3706734687902641489001165)
                      ·
                        rfl

theorem cell23_7218840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7218840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218840 prefixEnd_7218840 := by exact prefixLift 7218840
  have htrace : WordTrace (prefixWord ++ tailWord_7218840) baseStart_7218840 baseEnd_7218840 := by
    simpa [prefixWord, tailWord_7218840, baseEnd_7218840] using wordTrace_append hprefix tailTrace_7218840
  have hstable : (prefixWord ++ tailWord_7218840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218840).length < 2 ^ (prefixWord ++ tailWord_7218840).sum := by decide
  have hdescent : baseEnd_7218840 < baseStart_7218840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218873 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 10]
def baseStart_7218873 : Nat := 118140960795 + 7218873 * 2 ^ 59
def prefixEnd_7218873 : Nat := 4983230072969 + 3 ^ 40 * 7218873 * 2
def baseEnd_7218873 : Nat := 411861292529359984432057

theorem tailTrace_7218873 : CollatzResearch.WordTrace tailWord_7218873 prefixEnd_7218873 411861292529359984432057 := by
  unfold tailWord_7218873
  simp only [CollatzResearch.WordTrace]
  refine ⟨263293928776263481198493273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175529285850842320798995515 263293928776263481198493273)
  ·
    refine ⟨197470446582197610898869955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263293928776263481198493273 197470446582197610898869955)
    ·
      refine ⟨296205669873296416348304933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197470446582197610898869955 296205669873296416348304933)
      ·
        refine ⟨55538563101243078065307175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296205669873296416348304933 55538563101243078065307175)
        ·
          refine ⟨83307844651864617097960763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55538563101243078065307175 83307844651864617097960763)
          ·
            refine ⟨124961766977796925646941145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83307844651864617097960763 124961766977796925646941145)
            ·
              refine ⟨93721325233347694235205859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124961766977796925646941145 93721325233347694235205859)
              ·
                refine ⟨140581987850021541352808789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93721325233347694235205859 140581987850021541352808789)
                ·
                  refine ⟨411861292529359984432057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140581987850021541352808789 411861292529359984432057)
                  ·
                    rfl

theorem cell23_7218873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_7218873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218873 prefixEnd_7218873 := by exact prefixLift 7218873
  have htrace : WordTrace (prefixWord ++ tailWord_7218873) baseStart_7218873 baseEnd_7218873 := by
    simpa [prefixWord, tailWord_7218873, baseEnd_7218873] using wordTrace_append hprefix tailTrace_7218873
  have hstable : (prefixWord ++ tailWord_7218873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218873).length < 2 ^ (prefixWord ++ tailWord_7218873).sum := by decide
  have hdescent : baseEnd_7218873 < baseStart_7218873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218894 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_7218894 : Nat := 118140960795 + 7218894 * 2 ^ 59
def prefixEnd_7218894 : Nat := 4983230072969 + 3 ^ 40 * 7218894 * 2
def baseEnd_7218894 : Nat := 1235587471952661425908639

theorem tailTrace_7218894 : CollatzResearch.WordTrace tailWord_7218894 prefixEnd_7218894 1235587471952661425908639 := by
  unfold tailWord_7218894
  simp only [CollatzResearch.WordTrace]
  refine ⟨32911836838648425223125967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175529796472791601190005157 32911836838648425223125967)
  ·
    refine ⟨49367755257972637834688951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32911836838648425223125967 49367755257972637834688951)
    ·
      refine ⟨74051632886958956752033427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49367755257972637834688951 74051632886958956752033427)
      ·
        refine ⟨111077449330438435128050141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74051632886958956752033427 111077449330438435128050141)
        ·
          refine ⟨41654043498914413173018803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111077449330438435128050141 41654043498914413173018803)
          ·
            refine ⟨62481065248371619759528205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41654043498914413173018803 62481065248371619759528205)
            ·
              refine ⟨23430399468139357409823077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62481065248371619759528205 23430399468139357409823077)
              ·
                refine ⟨4393199900276129514341827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23430399468139357409823077 4393199900276129514341827)
                ·
                  refine ⟨6589799850414194271512741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393199900276129514341827 6589799850414194271512741)
                  ·
                    refine ⟨1235587471952661425908639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6589799850414194271512741 1235587471952661425908639)
                    ·
                      rfl

theorem cell23_7218894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_7218894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218894 prefixEnd_7218894 := by exact prefixLift 7218894
  have htrace : WordTrace (prefixWord ++ tailWord_7218894) baseStart_7218894 baseEnd_7218894 := by
    simpa [prefixWord, tailWord_7218894, baseEnd_7218894] using wordTrace_append hprefix tailTrace_7218894
  have hstable : (prefixWord ++ tailWord_7218894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218894).length < 2 ^ (prefixWord ++ tailWord_7218894).sum := by decide
  have hdescent : baseEnd_7218894 < baseStart_7218894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218927 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 1, 5, 2]
def baseStart_7218927 : Nat := 118140960795 + 7218927 * 2 ^ 59
def prefixEnd_7218927 : Nat := 4983230072969 + 3 ^ 40 * 7218927 * 2
def baseEnd_7218927 : Nat := 3706779360719582648613265

theorem tailTrace_7218927 : CollatzResearch.WordTrace tailWord_7218927 prefixEnd_7218927 3706779360719582648613265 := by
  unfold tailWord_7218927
  simp only [CollatzResearch.WordTrace]
  refine ⟨263295898318067848420959035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175530598878711898947306023 263295898318067848420959035)
  ·
    refine ⟨394943847477101772631438553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263295898318067848420959035 394943847477101772631438553)
    ·
      refine ⟨296207885607826329473578915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394943847477101772631438553 296207885607826329473578915)
      ·
        refine ⟨444311828411739494210368373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296207885607826329473578915 444311828411739494210368373)
        ·
          refine ⟨41654233913600577582222035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444311828411739494210368373 41654233913600577582222035)
          ·
            refine ⟨62481350870400866373333053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41654233913600577582222035 62481350870400866373333053)
            ·
              refine ⟨23430506576400324889999895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62481350870400866373333053 23430506576400324889999895)
              ·
                refine ⟨35145759864600487334999843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23430506576400324889999895 35145759864600487334999843)
                ·
                  refine ⟨52718639796900731002499765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35145759864600487334999843 52718639796900731002499765)
                  ·
                    refine ⟨4942372480959443531484353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52718639796900731002499765 4942372480959443531484353)
                    ·
                      refine ⟨3706779360719582648613265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942372480959443531484353 3706779360719582648613265)
                      ·
                        rfl

theorem cell23_7218927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5, 2].length) (baseStart_7218927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218927 prefixEnd_7218927 := by exact prefixLift 7218927
  have htrace : WordTrace (prefixWord ++ tailWord_7218927) baseStart_7218927 baseEnd_7218927 := by
    simpa [prefixWord, tailWord_7218927, baseEnd_7218927] using wordTrace_append hprefix tailTrace_7218927
  have hstable : (prefixWord ++ tailWord_7218927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218927).length < 2 ^ (prefixWord ++ tailWord_7218927).sum := by decide
  have hdescent : baseEnd_7218927 < baseStart_7218927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218951 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7218951 : Nat := 118140960795 + 7218951 * 2 ^ 59
def prefixEnd_7218951 : Nat := 4983230072969 + 3 ^ 40 * 7218951 * 2
def baseEnd_7218951 : Nat := 3706791684255290554713155

theorem tailTrace_7218951 : CollatzResearch.WordTrace tailWord_7218951 prefixEnd_7218951 3706791684255290554713155 := by
  unfold tailWord_7218951
  simp only [CollatzResearch.WordTrace]
  refine ⟨263296773669980900519832707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175531182446653933679888471 263296773669980900519832707)
  ·
    refine ⟨394945160504971350779749061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263296773669980900519832707 394945160504971350779749061)
    ·
      refine ⟨74052217594682128271202949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394945160504971350779749061 74052217594682128271202949)
      ·
        refine ⟨13884790799002899050850553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74052217594682128271202949 13884790799002899050850553)
        ·
          refine ⟨10413593099252174288137915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13884790799002899050850553 10413593099252174288137915)
          ·
            refine ⟨15620389648878261432206873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413593099252174288137915 15620389648878261432206873)
            ·
              refine ⟨11715292236658696074155155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15620389648878261432206873 11715292236658696074155155)
              ·
                refine ⟨17572938354988044111232733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11715292236658696074155155 17572938354988044111232733)
                ·
                  refine ⟨6589851883120516541712275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17572938354988044111232733 6589851883120516541712275)
                  ·
                    refine ⟨9884777824680774812568413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6589851883120516541712275 9884777824680774812568413)
                    ·
                      refine ⟨3706791684255290554713155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884777824680774812568413 3706791684255290554713155)
                      ·
                        rfl

theorem cell23_7218951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7218951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218951 prefixEnd_7218951 := by exact prefixLift 7218951
  have htrace : WordTrace (prefixWord ++ tailWord_7218951) baseStart_7218951 baseEnd_7218951 := by
    simpa [prefixWord, tailWord_7218951, baseEnd_7218951] using wordTrace_append hprefix tailTrace_7218951
  have hstable : (prefixWord ++ tailWord_7218951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218951).length < 2 ^ (prefixWord ++ tailWord_7218951).sum := by decide
  have hdescent : baseEnd_7218951 < baseStart_7218951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218967 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 1, 6]
def baseStart_7218967 : Nat := 118140960795 + 7218967 * 2 ^ 59
def prefixEnd_7218967 : Nat := 4983230072969 + 3 ^ 40 * 7218967 * 2
def baseEnd_7218967 : Nat := 1235599966648587497371027

theorem tailTrace_7218967 : CollatzResearch.WordTrace tailWord_7218967 prefixEnd_7218967 1235599966648587497371027 := by
  unfold tailWord_7218967
  simp only [CollatzResearch.WordTrace]
  refine ⟨263297357237922935252415155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175531571491948623501610103 263297357237922935252415155)
  ·
    refine ⟨394946035856884402878622733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263297357237922935252415155 394946035856884402878622733)
    ·
      refine ⟨148104763446331651079483525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394946035856884402878622733 148104763446331651079483525)
      ·
        refine ⟨27769643146187184577403161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148104763446331651079483525 27769643146187184577403161)
        ·
          refine ⟨20827232359640388433052371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27769643146187184577403161 20827232359640388433052371)
          ·
            refine ⟨31240848539460582649578557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20827232359640388433052371 31240848539460582649578557)
            ·
              refine ⟨11715318202297718493591959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31240848539460582649578557 11715318202297718493591959)
              ·
                refine ⟨17572977303446577740387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11715318202297718493591959 17572977303446577740387939)
                ·
                  refine ⟨26359465955169866610581909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17572977303446577740387939 26359465955169866610581909)
                  ·
                    refine ⟨1235599966648587497371027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26359465955169866610581909 1235599966648587497371027)
                    ·
                      rfl

theorem cell23_7218967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_7218967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218967 prefixEnd_7218967 := by exact prefixLift 7218967
  have htrace : WordTrace (prefixWord ++ tailWord_7218967) baseStart_7218967 baseEnd_7218967 := by
    simpa [prefixWord, tailWord_7218967, baseEnd_7218967] using wordTrace_append hprefix tailTrace_7218967
  have hstable : (prefixWord ++ tailWord_7218967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218967).length < 2 ^ (prefixWord ++ tailWord_7218967).sum := by decide
  have hdescent : baseEnd_7218967 < baseStart_7218967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218994 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_7218994 : Nat := 118140960795 + 7218994 * 2 ^ 59
def prefixEnd_7218994 : Nat := 4983230072969 + 3 ^ 40 * 7218994 * 2
def baseEnd_7218994 : Nat := 3706813763923433886475457

theorem tailTrace_7218994 : CollatzResearch.WordTrace tailWord_7218994 prefixEnd_7218994 3706813763923433886475457 := by
  unfold tailWord_7218994
  simp only [CollatzResearch.WordTrace]
  refine ⟨65824585502206279715912009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175532228005883412575765357 65824585502206279715912009)
  ·
    refine ⟨49368439126654709786934007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65824585502206279715912009 49368439126654709786934007)
    ·
      refine ⟨74052658689982064680401011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49368439126654709786934007 74052658689982064680401011)
      ·
        refine ⟨111078988034973097020601517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74052658689982064680401011 111078988034973097020601517)
        ·
          refine ⟨41654620513114911382725569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111078988034973097020601517 41654620513114911382725569)
          ·
            refine ⟨31240965384836183537044177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41654620513114911382725569 31240965384836183537044177)
            ·
              refine ⟨23430724038627137652783133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31240965384836183537044177 23430724038627137652783133)
              ·
                refine ⟨8786521514485176619793675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23430724038627137652783133 8786521514485176619793675)
                ·
                  refine ⟨13179782271727764929690513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786521514485176619793675 13179782271727764929690513)
                  ·
                    refine ⟨9884836703795823697267885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13179782271727764929690513 9884836703795823697267885)
                    ·
                      refine ⟨3706813763923433886475457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9884836703795823697267885 3706813763923433886475457)
                      ·
                        rfl

theorem cell23_7218994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_7218994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218994 prefixEnd_7218994 := by exact prefixLift 7218994
  have htrace : WordTrace (prefixWord ++ tailWord_7218994) baseStart_7218994 baseEnd_7218994 := by
    simpa [prefixWord, tailWord_7218994, baseEnd_7218994] using wordTrace_append hprefix tailTrace_7218994
  have hstable : (prefixWord ++ tailWord_7218994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218994).length < 2 ^ (prefixWord ++ tailWord_7218994).sum := by decide
  have hdescent : baseEnd_7218994 < baseStart_7218994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7218997 : List Nat := [1, 3, 3, 1, 4, 2, 9]
def baseStart_7218997 : Nat := 118140960795 + 7218997 * 2 ^ 59
def prefixEnd_7218997 : Nat := 4983230072969 + 3 ^ 40 * 7218997 * 2
def baseEnd_7218997 : Nat := 45763151905745646601703

theorem tailTrace_7218997 : CollatzResearch.WordTrace tailWord_7218997 prefixEnd_7218997 45763151905745646601703 := by
  unfold tailWord_7218997
  simp only [CollatzResearch.WordTrace]
  refine ⟨263298451427814250376007245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175532300951876166917338163 263298451427814250376007245)
  ·
    refine ⟨98736919285430343891002717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263298451427814250376007245 98736919285430343891002717)
    ·
      refine ⟨37026344732036378959126019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98736919285430343891002717 37026344732036378959126019)
      ·
        refine ⟨55539517098054568438689029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37026344732036378959126019 55539517098054568438689029)
        ·
          refine ⟨10413659455885231582254193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55539517098054568438689029 10413659455885231582254193)
          ·
            refine ⟨7810244591913923686690645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10413659455885231582254193 7810244591913923686690645)
            ·
              refine ⟨45763151905745646601703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7810244591913923686690645 45763151905745646601703)
              ·
                rfl

theorem cell23_7218997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 9].length) (baseStart_7218997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7218997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7218997 prefixEnd_7218997 := by exact prefixLift 7218997
  have htrace : WordTrace (prefixWord ++ tailWord_7218997) baseStart_7218997 baseEnd_7218997 := by
    simpa [prefixWord, tailWord_7218997, baseEnd_7218997] using wordTrace_append hprefix tailTrace_7218997
  have hstable : (prefixWord ++ tailWord_7218997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7218997).length < 2 ^ (prefixWord ++ tailWord_7218997).sum := by decide
  have hdescent : baseEnd_7218997 < baseStart_7218997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7218997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219014 : List Nat := [6, 1, 1, 2, 1, 1, 1, 10]
def baseStart_7219014 : Nat := 118140960795 + 7219014 * 2 ^ 59
def prefixEnd_7219014 : Nat := 4983230072969 + 3 ^ 40 * 7219014 * 2
def baseEnd_7219014 : Nat := 137289779019871252156495

theorem tailTrace_7219014 : CollatzResearch.WordTrace tailWord_7219014 prefixEnd_7219014 137289779019871252156495 := by
  unfold tailWord_7219014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8228095983398520696230503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175532714312501774852917397 8228095983398520696230503)
  ·
    refine ⟨12342143975097781044345755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8228095983398520696230503 12342143975097781044345755)
    ·
      refine ⟨18513215962646671566518633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12342143975097781044345755 18513215962646671566518633)
      ·
        refine ⟨13884911971985003674888975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18513215962646671566518633 13884911971985003674888975)
        ·
          refine ⟨20827367957977505512333463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13884911971985003674888975 20827367957977505512333463)
          ·
            refine ⟨31241051936966258268500195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20827367957977505512333463 31241051936966258268500195)
            ·
              refine ⟨46861577905449387402750293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31241051936966258268500195 46861577905449387402750293)
              ·
                refine ⟨137289779019871252156495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46861577905449387402750293 137289779019871252156495)
                ·
                  rfl

theorem cell23_7219014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_7219014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219014 prefixEnd_7219014 := by exact prefixLift 7219014
  have htrace : WordTrace (prefixWord ++ tailWord_7219014) baseStart_7219014 baseEnd_7219014 := by
    simpa [prefixWord, tailWord_7219014, baseEnd_7219014] using wordTrace_append hprefix tailTrace_7219014
  have hstable : (prefixWord ++ tailWord_7219014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219014).length < 2 ^ (prefixWord ++ tailWord_7219014).sum := by decide
  have hdescent : baseEnd_7219014 < baseStart_7219014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219034 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2]
def baseStart_7219034 : Nat := 118140960795 + 7219034 * 2 ^ 59
def prefixEnd_7219034 : Nat := 4983230072969 + 3 ^ 40 * 7219034 * 2
def baseEnd_7219034 : Nat := 3706834303149613729975273

theorem tailTrace_7219034 : CollatzResearch.WordTrace tailWord_7219034 prefixEnd_7219034 3706834303149613729975273 := by
  unfold tailWord_7219034
  simp only [CollatzResearch.WordTrace]
  refine ⟨65824950232170051423776039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175533200619120137130069437 65824950232170051423776039)
  ·
    refine ⟨98737425348255077135664059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65824950232170051423776039 98737425348255077135664059)
    ·
      refine ⟨148106138022382615703496089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98737425348255077135664059 148106138022382615703496089)
      ·
        refine ⟨111079603516786961777622067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148106138022382615703496089 111079603516786961777622067)
        ·
          refine ⟨166619405275180442666433101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111079603516786961777622067 166619405275180442666433101)
          ·
            refine ⟨62482276978192665999912413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166619405275180442666433101 62482276978192665999912413)
            ·
              refine ⟨23430853866822249749967155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62482276978192665999912413 23430853866822249749967155)
              ·
                refine ⟨35146280800233374624950733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23430853866822249749967155 35146280800233374624950733)
                ·
                  refine ⟨13179855300087515484356525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35146280800233374624950733 13179855300087515484356525)
                  ·
                    refine ⟨4942445737532818306633697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13179855300087515484356525 4942445737532818306633697)
                    ·
                      refine ⟨3706834303149613729975273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942445737532818306633697 3706834303149613729975273)
                      ·
                        rfl

theorem cell23_7219034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_7219034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219034 prefixEnd_7219034 := by exact prefixLift 7219034
  have htrace : WordTrace (prefixWord ++ tailWord_7219034) baseStart_7219034 baseEnd_7219034 := by
    simpa [prefixWord, tailWord_7219034, baseEnd_7219034] using wordTrace_append hprefix tailTrace_7219034
  have hstable : (prefixWord ++ tailWord_7219034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219034).length < 2 ^ (prefixWord ++ tailWord_7219034).sum := by decide
  have hdescent : baseEnd_7219034 < baseStart_7219034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219064 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 8, 2, 2]
def baseStart_7219064 : Nat := 118140960795 + 7219064 * 2 ^ 59
def prefixEnd_7219064 : Nat := 4983230072969 + 3 ^ 40 * 7219064 * 2
def baseEnd_7219064 : Nat := 3706849707569248612600135

theorem tailTrace_7219064 : CollatzResearch.WordTrace tailWord_7219064 prefixEnd_7219064 3706849707569248612600135 := by
  unfold tailWord_7219064
  simp only [CollatzResearch.WordTrace]
  refine ⟨131650447559285760409348123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175533930079047680545797497 131650447559285760409348123)
  ·
    refine ⟨197475671338928640614022185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131650447559285760409348123 197475671338928640614022185)
    ·
      refine ⟨148106753504196480460516639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197475671338928640614022185 148106753504196480460516639)
      ·
        refine ⟨222160130256294720690774959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148106753504196480460516639 222160130256294720690774959)
        ·
          refine ⟨333240195384442081036162439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222160130256294720690774959 333240195384442081036162439)
          ·
            refine ⟨499860293076663121554243659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333240195384442081036162439 499860293076663121554243659)
            ·
              refine ⟨749790439614994682331365489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499860293076663121554243659 749790439614994682331365489)
              ·
                refine ⟨562342829711246011748524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749790439614994682331365489 562342829711246011748524117)
                ·
                  refine ⟨6589955035678664200178017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 562342829711246011748524117 6589955035678664200178017)
                  ·
                    refine ⟨4942466276758998150133513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6589955035678664200178017 4942466276758998150133513)
                    ·
                      refine ⟨3706849707569248612600135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942466276758998150133513 3706849707569248612600135)
                      ·
                        rfl

theorem cell23_7219064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_7219064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219064 prefixEnd_7219064 := by exact prefixLift 7219064
  have htrace : WordTrace (prefixWord ++ tailWord_7219064) baseStart_7219064 baseEnd_7219064 := by
    simpa [prefixWord, tailWord_7219064, baseEnd_7219064] using wordTrace_append hprefix tailTrace_7219064
  have hstable : (prefixWord ++ tailWord_7219064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219064).length < 2 ^ (prefixWord ++ tailWord_7219064).sum := by decide
  have hdescent : baseEnd_7219064 < baseStart_7219064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219077 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_7219077 : Nat := 118140960795 + 7219077 * 2 ^ 59
def prefixEnd_7219077 : Nat := 4983230072969 + 3 ^ 40 * 7219077 * 2
def baseEnd_7219077 : Nat := 3706856382817757061737575

theorem tailTrace_7219077 : CollatzResearch.WordTrace tailWord_7219077 prefixEnd_7219077 3706856382817757061737575 := by
  unfold tailWord_7219077
  simp only [CollatzResearch.WordTrace]
  refine ⟨263301369267524424038919485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175534246178349616025946323 263301369267524424038919485)
  ·
    refine ⟨98738013475321659014594807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263301369267524424038919485 98738013475321659014594807)
    ·
      refine ⟨148107020212982488521892211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98738013475321659014594807 148107020212982488521892211)
      ·
        refine ⟨222160530319473732782838317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148107020212982488521892211 222160530319473732782838317)
        ·
          refine ⟨83310198869802649793564369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222160530319473732782838317 83310198869802649793564369)
          ·
            refine ⟨62482649152351987345173277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83310198869802649793564369 62482649152351987345173277)
            ·
              refine ⟨23430993432131995254439979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62482649152351987345173277 23430993432131995254439979)
              ·
                refine ⟨35146490148197992881659969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23430993432131995254439979 35146490148197992881659969)
                ·
                  refine ⟨26359867611148494661244977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35146490148197992881659969 26359867611148494661244977)
                  ·
                    refine ⟨19769900708361370995933733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26359867611148494661244977 19769900708361370995933733)
                    ·
                      refine ⟨3706856382817757061737575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19769900708361370995933733 3706856382817757061737575)
                      ·
                        rfl

theorem cell23_7219077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_7219077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219077 prefixEnd_7219077 := by exact prefixLift 7219077
  have htrace : WordTrace (prefixWord ++ tailWord_7219077) baseStart_7219077 baseEnd_7219077 := by
    simpa [prefixWord, tailWord_7219077, baseEnd_7219077] using wordTrace_append hprefix tailTrace_7219077
  have hstable : (prefixWord ++ tailWord_7219077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219077).length < 2 ^ (prefixWord ++ tailWord_7219077).sum := by decide
  have hdescent : baseEnd_7219077 < baseStart_7219077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219081 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 2, 2, 2]
def baseStart_7219081 : Nat := 118140960795 + 7219081 * 2 ^ 59
def prefixEnd_7219081 : Nat := 4983230072969 + 3 ^ 40 * 7219081 * 2
def baseEnd_7219081 : Nat := 3706858436740375046087557

theorem tailTrace_7219081 : CollatzResearch.WordTrace tailWord_7219081 prefixEnd_7219081 3706858436740375046087557 := by
  unfold tailWord_7219081
  simp only [CollatzResearch.WordTrace]
  refine ⟨263301515159509932722065097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175534343439673288481376731 263301515159509932722065097)
  ·
    refine ⟨197476136369632449541548823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263301515159509932722065097 197476136369632449541548823)
    ·
      refine ⟨296214204554448674312323235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197476136369632449541548823 296214204554448674312323235)
      ·
        refine ⟨444321306831673011468484853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296214204554448674312323235 444321306831673011468484853)
        ·
          refine ⟨41655122515469344825170455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444321306831673011468484853 41655122515469344825170455)
          ·
            refine ⟨62482683773204017237755683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41655122515469344825170455 62482683773204017237755683)
            ·
              refine ⟨93724025659806025856633525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62482683773204017237755683 93724025659806025856633525)
              ·
                refine ⟨8786627405606814924059393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93724025659806025856633525 8786627405606814924059393)
                ·
                  refine ⟨6589970554205111193044545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8786627405606814924059393 6589970554205111193044545)
                  ·
                    refine ⟨4942477915653833394783409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6589970554205111193044545 4942477915653833394783409)
                    ·
                      refine ⟨3706858436740375046087557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942477915653833394783409 3706858436740375046087557)
                      ·
                        rfl

theorem cell23_7219081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 2, 2].length) (baseStart_7219081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219081 prefixEnd_7219081 := by exact prefixLift 7219081
  have htrace : WordTrace (prefixWord ++ tailWord_7219081) baseStart_7219081 baseEnd_7219081 := by
    simpa [prefixWord, tailWord_7219081, baseEnd_7219081] using wordTrace_append hprefix tailTrace_7219081
  have hstable : (prefixWord ++ tailWord_7219081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219081).length < 2 ^ (prefixWord ++ tailWord_7219081).sum := by decide
  have hdescent : baseEnd_7219081 < baseStart_7219081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219132 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7219132 : Nat := 118140960795 + 7219132 * 2 ^ 59
def prefixEnd_7219132 : Nat := 4983230072969 + 3 ^ 40 * 7219132 * 2
def baseEnd_7219132 : Nat := 3706884624253754346549823

theorem tailTrace_7219132 : CollatzResearch.WordTrace tailWord_7219132 prefixEnd_7219132 3706884624253754346549823 := by
  unfold tailWord_7219132
  simp only [CollatzResearch.WordTrace]
  refine ⟨131651687641162584216085825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175535583521550112288114433 131651687641162584216085825)
  ·
    refine ⟨98738765730871938162064369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131651687641162584216085825 98738765730871938162064369)
    ·
      refine ⟨74054074298153953621548277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98738765730871938162064369 74054074298153953621548277)
      ·
        refine ⟨6942569465451933152020151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74054074298153953621548277 6942569465451933152020151)
        ·
          refine ⟨10413854198177899728030227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942569465451933152020151 10413854198177899728030227)
          ·
            refine ⟨15620781297266849592045341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413854198177899728030227 15620781297266849592045341)
            ·
              refine ⟨5857792986475068597017003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15620781297266849592045341 5857792986475068597017003)
              ·
                refine ⟨8786689479712602895525505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857792986475068597017003 8786689479712602895525505)
                ·
                  refine ⟨6590017109784452171644129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8786689479712602895525505 6590017109784452171644129)
                  ·
                    refine ⟨4942512832338339128733097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6590017109784452171644129 4942512832338339128733097)
                    ·
                      refine ⟨3706884624253754346549823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942512832338339128733097 3706884624253754346549823)
                      ·
                        rfl

theorem cell23_7219132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7219132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219132 prefixEnd_7219132 := by exact prefixLift 7219132
  have htrace : WordTrace (prefixWord ++ tailWord_7219132) baseStart_7219132 baseEnd_7219132 := by
    simpa [prefixWord, tailWord_7219132, baseEnd_7219132] using wordTrace_append hprefix tailTrace_7219132
  have hstable : (prefixWord ++ tailWord_7219132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219132).length < 2 ^ (prefixWord ++ tailWord_7219132).sum := by decide
  have hdescent : baseEnd_7219132 < baseStart_7219132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219197 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_7219197 : Nat := 118140960795 + 7219197 * 2 ^ 59
def prefixEnd_7219197 : Nat := 4983230072969 + 3 ^ 40 * 7219197 * 2
def baseEnd_7219197 : Nat := 3706918000496296592237023

theorem tailTrace_7219197 : CollatzResearch.WordTrace tailWord_7219197 prefixEnd_7219197 3706918000496296592237023 := by
  unfold tailWord_7219197
  simp only [CollatzResearch.WordTrace]
  refine ⟨263305746027089684533287845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175537164018059789688858563 263305746027089684533287845)
  ·
    refine ⟨49369827380079315849991471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263305746027089684533287845 49369827380079315849991471)
    ·
      refine ⟨74054741070118973774987207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49369827380079315849991471 74054741070118973774987207)
      ·
        refine ⟨111082111605178460662480811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74054741070118973774987207 111082111605178460662480811)
        ·
          refine ⟨166623167407767690993721217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111082111605178460662480811 166623167407767690993721217)
          ·
            refine ⟨124967375555825768245290913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166623167407767690993721217 124967375555825768245290913)
            ·
              refine ⟨93725531666869326183968185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124967375555825768245290913 93725531666869326183968185)
              ·
                refine ⟨70294148750151994637976139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93725531666869326183968185 70294148750151994637976139)
                ·
                  refine ⟨105441223125227991956964209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70294148750151994637976139 105441223125227991956964209)
                  ·
                    refine ⟨79080917343920993967723157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105441223125227991956964209 79080917343920993967723157)
                    ·
                      refine ⟨3706918000496296592237023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79080917343920993967723157 3706918000496296592237023)
                      ·
                        rfl

theorem cell23_7219197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_7219197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219197 prefixEnd_7219197 := by exact prefixLift 7219197
  have htrace : WordTrace (prefixWord ++ tailWord_7219197) baseStart_7219197 baseEnd_7219197 := by
    simpa [prefixWord, tailWord_7219197, baseEnd_7219197] using wordTrace_append hprefix tailTrace_7219197
  have hstable : (prefixWord ++ tailWord_7219197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219197).length < 2 ^ (prefixWord ++ tailWord_7219197).sum := by decide
  have hdescent : baseEnd_7219197 < baseStart_7219197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219231 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 2, 3, 2]
def baseStart_7219231 : Nat := 118140960795 + 7219231 * 2 ^ 59
def prefixEnd_7219231 : Nat := 4983230072969 + 3 ^ 40 * 7219231 * 2
def baseEnd_7219231 : Nat := 3706935458838549459211867

theorem tailTrace_7219231 : CollatzResearch.WordTrace tailWord_7219231 prefixEnd_7219231 3706935458838549459211867 := by
  unfold tailWord_7219231
  simp only [CollatzResearch.WordTrace]
  refine ⟨263306986108966508340025547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175537990739311005560017031 263306986108966508340025547)
  ·
    refine ⟨394960479163449762510038321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263306986108966508340025547 394960479163449762510038321)
    ·
      refine ⟨296220359372587321882528741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394960479163449762510038321 296220359372587321882528741)
      ·
        refine ⟨55541317382360122852974139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296220359372587321882528741 55541317382360122852974139)
        ·
          refine ⟨83311976073540184279461209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55541317382360122852974139 83311976073540184279461209)
          ·
            refine ⟨62483982055155138209595907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83311976073540184279461209 62483982055155138209595907)
            ·
              refine ⟨93725973082732707314393861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62483982055155138209595907 93725973082732707314393861)
              ·
                refine ⟨17573619953012382621448849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93725973082732707314393861 17573619953012382621448849)
                ·
                  refine ⟨13180214964759286966086637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17573619953012382621448849 13180214964759286966086637)
                  ·
                    refine ⟨4942580611784732612282489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13180214964759286966086637 4942580611784732612282489)
                    ·
                      refine ⟨3706935458838549459211867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942580611784732612282489 3706935458838549459211867)
                      ·
                        rfl

theorem cell23_7219231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_7219231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219231 prefixEnd_7219231 := by exact prefixLift 7219231
  have htrace : WordTrace (prefixWord ++ tailWord_7219231) baseStart_7219231 baseEnd_7219231 := by
    simpa [prefixWord, tailWord_7219231, baseEnd_7219231] using wordTrace_append hprefix tailTrace_7219231
  have hstable : (prefixWord ++ tailWord_7219231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219231).length < 2 ^ (prefixWord ++ tailWord_7219231).sum := by decide
  have hdescent : baseEnd_7219231 < baseStart_7219231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219261 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_7219261 : Nat := 118140960795 + 7219261 * 2 ^ 59
def prefixEnd_7219261 : Nat := 4983230072969 + 3 ^ 40 * 7219261 * 2
def baseEnd_7219261 : Nat := 3706950863258184341836729

theorem tailTrace_7219261 : CollatzResearch.WordTrace tailWord_7219261 prefixEnd_7219261 3706950863258184341836729 := by
  unfold tailWord_7219261
  simp only [CollatzResearch.WordTrace]
  refine ⟨263308080298857823463617637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175538720199238548975745091 263308080298857823463617637)
  ·
    refine ⟨49370265056035841899428307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263308080298857823463617637 49370265056035841899428307)
    ·
      refine ⟨74055397584053762849142461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49370265056035841899428307 74055397584053762849142461)
      ·
        refine ⟨27770774094020161068428423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74055397584053762849142461 27770774094020161068428423)
        ·
          refine ⟨41656161141030241602642635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27770774094020161068428423 41656161141030241602642635)
          ·
            refine ⟨62484241711545362403963953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41656161141030241602642635 62484241711545362403963953)
            ·
              refine ⟨46863181283659021802972965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62484241711545362403963953 46863181283659021802972965)
              ·
                refine ⟨8786846490686066588057431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46863181283659021802972965 8786846490686066588057431)
                ·
                  refine ⟨13180269736029099882086147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786846490686066588057431 13180269736029099882086147)
                  ·
                    refine ⟨19770404604043649823129221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13180269736029099882086147 19770404604043649823129221)
                    ·
                      refine ⟨3706950863258184341836729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19770404604043649823129221 3706950863258184341836729)
                      ·
                        rfl

theorem cell23_7219261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_7219261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219261 prefixEnd_7219261 := by exact prefixLift 7219261
  have htrace : WordTrace (prefixWord ++ tailWord_7219261) baseStart_7219261 baseEnd_7219261 := by
    simpa [prefixWord, tailWord_7219261, baseEnd_7219261] using wordTrace_append hprefix tailTrace_7219261
  have hstable : (prefixWord ++ tailWord_7219261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219261).length < 2 ^ (prefixWord ++ tailWord_7219261).sum := by decide
  have hdescent : baseEnd_7219261 < baseStart_7219261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219265 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7219265 : Nat := 118140960795 + 7219265 * 2 ^ 59
def prefixEnd_7219265 : Nat := 4983230072969 + 3 ^ 40 * 7219265 * 2
def baseEnd_7219265 : Nat := 3706952917180802326186711

theorem tailTrace_7219265 : CollatzResearch.WordTrace tailWord_7219265 prefixEnd_7219265 3706952917180802326186711 := by
  unfold tailWord_7219265
  simp only [CollatzResearch.WordTrace]
  refine ⟨263308226190843332146763249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175538817460562221431175499 263308226190843332146763249)
  ·
    refine ⟨197481169643132499110072437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263308226190843332146763249 197481169643132499110072437)
    ·
      refine ⟨18513859654043671791569291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197481169643132499110072437 18513859654043671791569291)
      ·
        refine ⟨27770789481065507687353937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18513859654043671791569291 27770789481065507687353937)
        ·
          refine ⟨20828092110799130765515453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27770789481065507687353937 20828092110799130765515453)
          ·
            refine ⟨7810534541549674037068295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20828092110799130765515453 7810534541549674037068295)
            ·
              refine ⟨11715801812324511055602443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810534541549674037068295 11715801812324511055602443)
              ·
                refine ⟨17573702718486766583403665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11715801812324511055602443 17573702718486766583403665)
                ·
                  refine ⟨13180277038865074937552749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17573702718486766583403665 13180277038865074937552749)
                  ·
                    refine ⟨4942603889574403101582281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13180277038865074937552749 4942603889574403101582281)
                    ·
                      refine ⟨3706952917180802326186711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942603889574403101582281 3706952917180802326186711)
                      ·
                        rfl

theorem cell23_7219265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7219265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219265 prefixEnd_7219265 := by exact prefixLift 7219265
  have htrace : WordTrace (prefixWord ++ tailWord_7219265) baseStart_7219265 baseEnd_7219265 := by
    simpa [prefixWord, tailWord_7219265, baseEnd_7219265] using wordTrace_append hprefix tailTrace_7219265
  have hstable : (prefixWord ++ tailWord_7219265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219265).length < 2 ^ (prefixWord ++ tailWord_7219265).sum := by decide
  have hdescent : baseEnd_7219265 < baseStart_7219265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219278 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_7219278 : Nat := 118140960795 + 7219278 * 2 ^ 59
def prefixEnd_7219278 : Nat := 4983230072969 + 3 ^ 40 * 7219278 * 2
def baseEnd_7219278 : Nat := 3706959592429310775324151

theorem tailTrace_7219278 : CollatzResearch.WordTrace tailWord_7219278 prefixEnd_7219278 3706959592429310775324151 := by
  unfold tailWord_7219278
  simp only [CollatzResearch.WordTrace]
  refine ⟨32913587542474529420873311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175539133559864156911324325 32913587542474529420873311)
  ·
    refine ⟨49370381313711794131309967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32913587542474529420873311 49370381313711794131309967)
    ·
      refine ⟨74055571970567691196964951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49370381313711794131309967 74055571970567691196964951)
      ·
        refine ⟨111083357955851536795447427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74055571970567691196964951 111083357955851536795447427)
        ·
          refine ⟨166625036933777305193171141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111083357955851536795447427 166625036933777305193171141)
          ·
            refine ⟨31242194425083244723719589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166625036933777305193171141 31242194425083244723719589)
            ·
              refine ⟨5857911454703108385697423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31242194425083244723719589 5857911454703108385697423)
              ·
                refine ⟨8786867182054662578546135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857911454703108385697423 8786867182054662578546135)
                ·
                  refine ⟨13180300773081993867819203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786867182054662578546135 13180300773081993867819203)
                  ·
                    refine ⟨19770451159622990801728805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13180300773081993867819203 19770451159622990801728805)
                    ·
                      refine ⟨3706959592429310775324151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19770451159622990801728805 3706959592429310775324151)
                      ·
                        rfl

theorem cell23_7219278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_7219278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219278 prefixEnd_7219278 := by exact prefixLift 7219278
  have htrace : WordTrace (prefixWord ++ tailWord_7219278) baseStart_7219278 baseEnd_7219278 := by
    simpa [prefixWord, tailWord_7219278, baseEnd_7219278] using wordTrace_append hprefix tailTrace_7219278
  have hstable : (prefixWord ++ tailWord_7219278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219278).length < 2 ^ (prefixWord ++ tailWord_7219278).sum := by decide
  have hdescent : baseEnd_7219278 < baseStart_7219278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219288 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 2, 4]
def baseStart_7219288 : Nat := 118140960795 + 7219288 * 2 ^ 59
def prefixEnd_7219288 : Nat := 4983230072969 + 3 ^ 40 * 7219288 * 2
def baseEnd_7219288 : Nat := 1235654909078618578733035

theorem tailTrace_7219288 : CollatzResearch.WordTrace tailWord_7219288 prefixEnd_7219288 1235654909078618578733035 := by
  unfold tailWord_7219288
  simp only [CollatzResearch.WordTrace]
  refine ⟨131654532534880003537425259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175539376713173338049900345 131654532534880003537425259)
  ·
    refine ⟨197481798802320005306137889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131654532534880003537425259 197481798802320005306137889)
    ·
      refine ⟨148111349101740003979603417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197481798802320005306137889 148111349101740003979603417)
      ·
        refine ⟨111083511826305002984702563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148111349101740003979603417 111083511826305002984702563)
        ·
          refine ⟨166625267739457504477053845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111083511826305002984702563 166625267739457504477053845)
          ·
            refine ⟨7810559425287070522361899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166625267739457504477053845 7810559425287070522361899)
            ·
              refine ⟨11715839137930605783542849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810559425287070522361899 11715839137930605783542849)
              ·
                refine ⟨8786879353447954337657137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11715839137930605783542849 8786879353447954337657137)
                ·
                  refine ⟨6590159515085965753242853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8786879353447954337657137 6590159515085965753242853)
                  ·
                    refine ⟨1235654909078618578733035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590159515085965753242853 1235654909078618578733035)
                    ·
                      rfl

theorem cell23_7219288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_7219288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219288 prefixEnd_7219288 := by exact prefixLift 7219288
  have htrace : WordTrace (prefixWord ++ tailWord_7219288) baseStart_7219288 baseEnd_7219288 := by
    simpa [prefixWord, tailWord_7219288, baseEnd_7219288] using wordTrace_append hprefix tailTrace_7219288
  have hstable : (prefixWord ++ tailWord_7219288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219288).length < 2 ^ (prefixWord ++ tailWord_7219288).sum := by decide
  have hdescent : baseEnd_7219288 < baseStart_7219288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219298 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7219298 : Nat := 118140960795 + 7219298 * 2 ^ 59
def prefixEnd_7219298 : Nat := 4983230072969 + 3 ^ 40 * 7219298 * 2
def baseEnd_7219298 : Nat := 3706969862042400697074059

theorem tailTrace_7219298 : CollatzResearch.WordTrace tailWord_7219298 prefixEnd_7219298 3706969862042400697074059 := by
  unfold tailWord_7219298
  simp only [CollatzResearch.WordTrace]
  refine ⟨65827357449930944695678637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175539619866482519188476365 65827357449930944695678637)
  ·
    refine ⟨24685259043724104260879489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65827357449930944695678637 24685259043724104260879489)
    ·
      refine ⟨18513944282793078195659617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24685259043724104260879489 18513944282793078195659617)
      ·
        refine ⟨13885458212094808646744713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18513944282793078195659617 13885458212094808646744713)
        ·
          refine ⟨10414093659071106485058535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13885458212094808646744713 10414093659071106485058535)
          ·
            refine ⟨15621140488606659727587803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10414093659071106485058535 15621140488606659727587803)
            ·
              refine ⟨23431710732909989591381705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15621140488606659727587803 23431710732909989591381705)
              ·
                refine ⟨17573783049682492193536279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23431710732909989591381705 17573783049682492193536279)
                ·
                  refine ⟨26360674574523738290304419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17573783049682492193536279 26360674574523738290304419)
                  ·
                    refine ⟨39541011861785607435456629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26360674574523738290304419 39541011861785607435456629)
                    ·
                      refine ⟨3706969862042400697074059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39541011861785607435456629 3706969862042400697074059)
                      ·
                        rfl

theorem cell23_7219298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7219298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219298 prefixEnd_7219298 := by exact prefixLift 7219298
  have htrace : WordTrace (prefixWord ++ tailWord_7219298) baseStart_7219298 baseEnd_7219298 := by
    simpa [prefixWord, tailWord_7219298, baseEnd_7219298] using wordTrace_append hprefix tailTrace_7219298
  have hstable : (prefixWord ++ tailWord_7219298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219298).length < 2 ^ (prefixWord ++ tailWord_7219298).sum := by decide
  have hdescent : baseEnd_7219298 < baseStart_7219298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219311 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_7219311 : Nat := 118140960795 + 7219311 * 2 ^ 59
def prefixEnd_7219311 : Nat := 4983230072969 + 3 ^ 40 * 7219311 * 2
def baseEnd_7219311 : Nat := 3706976537290909146211499

theorem tailTrace_7219311 : CollatzResearch.WordTrace tailWord_7219311 prefixEnd_7219311 3706976537290909146211499 := by
  unfold tailWord_7219311
  simp only [CollatzResearch.WordTrace]
  refine ⟨263309903948676682002937787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175539935965784454668625191 263309903948676682002937787)
  ·
    refine ⟨394964855923015023004406681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263309903948676682002937787 394964855923015023004406681)
    ·
      refine ⟨296223641942261267253305011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394964855923015023004406681 296223641942261267253305011)
      ·
        refine ⟨444335462913391900879957517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296223641942261267253305011 444335462913391900879957517)
        ·
          refine ⟨166625798592521962829984069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444335462913391900879957517 166625798592521962829984069)
          ·
            refine ⟨31242337236097868030622013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166625798592521962829984069 31242337236097868030622013)
            ·
              refine ⟨11715876463536700511483255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31242337236097868030622013 11715876463536700511483255)
              ·
                refine ⟨17573814695305050767224883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11715876463536700511483255 17573814695305050767224883)
                ·
                  refine ⟨26360722042957576150837325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17573814695305050767224883 26360722042957576150837325)
                  ·
                    refine ⟨9885270766109091056563997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26360722042957576150837325 9885270766109091056563997)
                    ·
                      refine ⟨3706976537290909146211499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9885270766109091056563997 3706976537290909146211499)
                      ·
                        rfl

theorem cell23_7219311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_7219311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219311 prefixEnd_7219311 := by exact prefixLift 7219311
  have htrace : WordTrace (prefixWord ++ tailWord_7219311) baseStart_7219311 baseEnd_7219311 := by
    simpa [prefixWord, tailWord_7219311, baseEnd_7219311] using wordTrace_append hprefix tailTrace_7219311
  have hstable : (prefixWord ++ tailWord_7219311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219311).length < 2 ^ (prefixWord ++ tailWord_7219311).sum := by decide
  have hdescent : baseEnd_7219311 < baseStart_7219311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219318 : List Nat := [5, 1, 1, 2, 1, 4, 2, 7]
def baseStart_7219318 : Nat := 118140960795 + 7219318 * 2 ^ 59
def prefixEnd_7219318 : Nat := 4983230072969 + 3 ^ 40 * 7219318 * 2
def baseEnd_7219318 : Nat := 137295560431684837734221

theorem tailTrace_7219318 : CollatzResearch.WordTrace tailWord_7219318 prefixEnd_7219318 137295560431684837734221 := by
  unfold tailWord_7219318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456884953728207637402663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175540106173100881465628405 16456884953728207637402663)
  ·
    refine ⟨24685327430592311456103995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16456884953728207637402663 24685327430592311456103995)
    ·
      refine ⟨37027991145888467184155993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24685327430592311456103995 37027991145888467184155993)
      ·
        refine ⟨27770993359416350388116995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37027991145888467184155993 27770993359416350388116995)
        ·
          refine ⟨41656490039124525582175493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27770993359416350388116995 41656490039124525582175493)
          ·
            refine ⟨7810591882335848546657905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41656490039124525582175493 7810591882335848546657905)
            ·
              refine ⟨5857943911751886409993429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7810591882335848546657905 5857943911751886409993429)
              ·
                refine ⟨137295560431684837734221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5857943911751886409993429 137295560431684837734221)
                ·
                  rfl

theorem cell23_7219318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_7219318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219318 prefixEnd_7219318 := by exact prefixLift 7219318
  have htrace : WordTrace (prefixWord ++ tailWord_7219318) baseStart_7219318 baseEnd_7219318 := by
    simpa [prefixWord, tailWord_7219318, baseEnd_7219318] using wordTrace_append hprefix tailTrace_7219318
  have hstable : (prefixWord ++ tailWord_7219318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219318).length < 2 ^ (prefixWord ++ tailWord_7219318).sum := by decide
  have hdescent : baseEnd_7219318 < baseStart_7219318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219324 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_7219324 : Nat := 118140960795 + 7219324 * 2 ^ 59
def prefixEnd_7219324 : Nat := 4983230072969 + 3 ^ 40 * 7219324 * 2
def baseEnd_7219324 : Nat := 3706983212539417595348939

theorem tailTrace_7219324 : CollatzResearch.WordTrace tailWord_7219324 prefixEnd_7219324 3706983212539417595348939 := by
  unfold tailWord_7219324
  simp only [CollatzResearch.WordTrace]
  refine ⟨131655189048814792611580513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175540252065086390148774017 131655189048814792611580513)
  ·
    refine ⟨98741391786611094458685385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131655189048814792611580513 98741391786611094458685385)
    ·
      refine ⟨74056043839958320844014039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98741391786611094458685385 74056043839958320844014039)
      ·
        refine ⟨111084065759937481266021059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74056043839958320844014039 111084065759937481266021059)
        ·
          refine ⟨166626098639906221899031589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111084065759937481266021059 166626098639906221899031589)
          ·
            refine ⟨31242393494982416606068423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166626098639906221899031589 31242393494982416606068423)
            ·
              refine ⟨46863590242473624909102635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31242393494982416606068423 46863590242473624909102635)
              ·
                refine ⟨70295385363710437363653953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46863590242473624909102635 70295385363710437363653953)
                ·
                  refine ⟨52721539022782828022740465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70295385363710437363653953 52721539022782828022740465)
                  ·
                    refine ⟨39541154267087121017055349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52721539022782828022740465 39541154267087121017055349)
                    ·
                      refine ⟨3706983212539417595348939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39541154267087121017055349 3706983212539417595348939)
                      ·
                        rfl

theorem cell23_7219324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_7219324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219324 prefixEnd_7219324 := by exact prefixLift 7219324
  have htrace : WordTrace (prefixWord ++ tailWord_7219324) baseStart_7219324 baseEnd_7219324 := by
    simpa [prefixWord, tailWord_7219324, baseEnd_7219324] using wordTrace_append hprefix tailTrace_7219324
  have hstable : (prefixWord ++ tailWord_7219324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219324).length < 2 ^ (prefixWord ++ tailWord_7219324).sum := by decide
  have hdescent : baseEnd_7219324 < baseStart_7219324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219329 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_7219329 : Nat := 118140960795 + 7219329 * 2 ^ 59
def prefixEnd_7219329 : Nat := 4983230072969 + 3 ^ 40 * 7219329 * 2
def baseEnd_7219329 : Nat := 3706985779942690075786417

theorem tailTrace_7219329 : CollatzResearch.WordTrace tailWord_7219329 prefixEnd_7219329 3706985779942690075786417 := by
  unfold tailWord_7219329
  simp only [CollatzResearch.WordTrace]
  refine ⟨263310560462611471077093041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175540373641740980718062027 263310560462611471077093041)
  ·
    refine ⟨197482920346958603307819781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263310560462611471077093041 197482920346958603307819781)
    ·
      refine ⟨37028047565054738120216209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197482920346958603307819781 37028047565054738120216209)
      ·
        refine ⟨27771035673791053590162157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37028047565054738120216209 27771035673791053590162157)
        ·
          refine ⟨10414138377671645096310809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27771035673791053590162157 10414138377671645096310809)
          ·
            refine ⟨7810603783253733822233107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10414138377671645096310809 7810603783253733822233107)
            ·
              refine ⟨11715905674880600733349661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810603783253733822233107 11715905674880600733349661)
              ·
                refine ⟨4393464628080225275006123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11715905674880600733349661 4393464628080225275006123)
                ·
                  refine ⟨6590196942120337912509185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393464628080225275006123 6590196942120337912509185)
                  ·
                    refine ⟨4942647706590253434381889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6590196942120337912509185 4942647706590253434381889)
                    ·
                      refine ⟨3706985779942690075786417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942647706590253434381889 3706985779942690075786417)
                      ·
                        rfl

theorem cell23_7219329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_7219329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219329 prefixEnd_7219329 := by exact prefixLift 7219329
  have htrace : WordTrace (prefixWord ++ tailWord_7219329) baseStart_7219329 baseEnd_7219329 := by
    simpa [prefixWord, tailWord_7219329, baseEnd_7219329] using wordTrace_append hprefix tailTrace_7219329
  have hstable : (prefixWord ++ tailWord_7219329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219329).length < 2 ^ (prefixWord ++ tailWord_7219329).sum := by decide
  have hdescent : baseEnd_7219329 < baseStart_7219329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219362 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7219362 : Nat := 118140960795 + 7219362 * 2 ^ 59
def prefixEnd_7219362 : Nat := 4983230072969 + 3 ^ 40 * 7219362 * 2
def baseEnd_7219362 : Nat := 3707002724804288446673765

theorem tailTrace_7219362 : CollatzResearch.WordTrace tailWord_7219362 prefixEnd_7219362 3707002724804288446673765 := by
  unfold tailWord_7219362
  simp only [CollatzResearch.WordTrace]
  refine ⟨65827941017872979428261085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175541176047661278475362893 65827941017872979428261085)
  ·
    refine ⟨24685477881702367285597907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65827941017872979428261085 24685477881702367285597907)
    ·
      refine ⟨37028216822553550928396861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24685477881702367285597907 37028216822553550928396861)
      ·
        refine ⟨13885581308457581598148823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37028216822553550928396861 13885581308457581598148823)
        ·
          refine ⟨20828371962686372397223235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13885581308457581598148823 20828371962686372397223235)
          ·
            refine ⟨31242557944029558595834853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20828371962686372397223235 31242557944029558595834853)
            ·
              refine ⟨5857979614505542236719035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31242557944029558595834853 5857979614505542236719035)
              ·
                refine ⟨8786969421758313355078553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857979614505542236719035 8786969421758313355078553)
                ·
                  refine ⟨6590227066318735016308915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8786969421758313355078553 6590227066318735016308915)
                  ·
                    refine ⟨9885340599478102524463373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6590227066318735016308915 9885340599478102524463373)
                    ·
                      refine ⟨3707002724804288446673765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9885340599478102524463373 3707002724804288446673765)
                      ·
                        rfl

theorem cell23_7219362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7219362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219362 prefixEnd_7219362 := by exact prefixLift 7219362
  have htrace : WordTrace (prefixWord ++ tailWord_7219362) baseStart_7219362 baseEnd_7219362 := by
    simpa [prefixWord, tailWord_7219362, baseEnd_7219362] using wordTrace_append hprefix tailTrace_7219362
  have hstable : (prefixWord ++ tailWord_7219362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219362).length < 2 ^ (prefixWord ++ tailWord_7219362).sum := by decide
  have hdescent : baseEnd_7219362 < baseStart_7219362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219391 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 5]
def baseStart_7219391 : Nat := 118140960795 + 7219391 * 2 ^ 59
def prefixEnd_7219391 : Nat := 4983230072969 + 3 ^ 40 * 7219391 * 2
def baseEnd_7219391 : Nat := 411890846193696537023459

theorem tailTrace_7219391 : CollatzResearch.WordTrace tailWord_7219391 prefixEnd_7219391 411890846193696537023459 := by
  unfold tailWord_7219391
  simp only [CollatzResearch.WordTrace]
  refine ⟨263312821788386855665850027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175541881192257903777233351 263312821788386855665850027)
  ·
    refine ⟨394969232682580283498775041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263312821788386855665850027 394969232682580283498775041)
    ·
      refine ⟨296226924511935212624081281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394969232682580283498775041 296226924511935212624081281)
      ·
        refine ⟨222170193383951409468060961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296226924511935212624081281 222170193383951409468060961)
        ·
          refine ⟨166627645037963557101045721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222170193383951409468060961 166627645037963557101045721)
          ·
            refine ⟨124970733778472667825784291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166627645037963557101045721 124970733778472667825784291)
            ·
              refine ⟨187456100667709001738676437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124970733778472667825784291 187456100667709001738676437)
              ·
                refine ⟨4393502359399429728250229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187456100667709001738676437 4393502359399429728250229)
                ·
                  refine ⟨411890846193696537023459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393502359399429728250229 411890846193696537023459)
                  ·
                    rfl

theorem cell23_7219391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 5].length) (baseStart_7219391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219391 prefixEnd_7219391 := by exact prefixLift 7219391
  have htrace : WordTrace (prefixWord ++ tailWord_7219391) baseStart_7219391 baseEnd_7219391 := by
    simpa [prefixWord, tailWord_7219391, baseEnd_7219391] using wordTrace_append hprefix tailTrace_7219391
  have hstable : (prefixWord ++ tailWord_7219391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219391).length < 2 ^ (prefixWord ++ tailWord_7219391).sum := by decide
  have hdescent : baseEnd_7219391 < baseStart_7219391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219468 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_7219468 : Nat := 118140960795 + 7219468 * 2 ^ 59
def prefixEnd_7219468 : Nat := 4983230072969 + 3 ^ 40 * 7219468 * 2
def baseEnd_7219468 : Nat := 1235685717917888343982759

theorem tailTrace_7219468 : CollatzResearch.WordTrace tailWord_7219468 prefixEnd_7219468 1235685717917888343982759 := by
  unfold tailWord_7219468
  simp only [CollatzResearch.WordTrace]
  refine ⟨131657815104553948908201529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175543753472738598544268705 131657815104553948908201529)
  ·
    refine ⟨98743361328415461681151147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131657815104553948908201529 98743361328415461681151147)
    ·
      refine ⟨148115041992623192521726721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98743361328415461681151147 148115041992623192521726721)
      ·
        refine ⟨111086281494467394391295041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148115041992623192521726721 111086281494467394391295041)
        ·
          refine ⟨83314711120850545793471281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111086281494467394391295041 83314711120850545793471281)
          ·
            refine ⟨62486033340637909345103461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83314711120850545793471281 62486033340637909345103461)
            ·
              refine ⟨11716131251369608002206899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62486033340637909345103461 11716131251369608002206899)
              ·
                refine ⟨17574196877054412003310349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11716131251369608002206899 17574196877054412003310349)
                ·
                  refine ⟨6590323828895404501241381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17574196877054412003310349 6590323828895404501241381)
                  ·
                    refine ⟨1235685717917888343982759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590323828895404501241381 1235685717917888343982759)
                    ·
                      rfl

theorem cell23_7219468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_7219468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219468 prefixEnd_7219468 := by exact prefixLift 7219468
  have htrace : WordTrace (prefixWord ++ tailWord_7219468) baseStart_7219468 baseEnd_7219468 := by
    simpa [prefixWord, tailWord_7219468, baseEnd_7219468] using wordTrace_append hprefix tailTrace_7219468
  have hstable : (prefixWord ++ tailWord_7219468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219468).length < 2 ^ (prefixWord ++ tailWord_7219468).sum := by decide
  have hdescent : baseEnd_7219468 < baseStart_7219468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219491 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 3]
def baseStart_7219491 : Nat := 118140960795 + 7219491 * 2 ^ 59
def prefixEnd_7219491 : Nat := 4983230072969 + 3 ^ 40 * 7219491 * 2
def baseEnd_7219491 : Nat := 3707068963808718441960671

theorem tailTrace_7219491 : CollatzResearch.WordTrace tailWord_7219491 prefixEnd_7219491 3707068963808718441960671 := by
  unfold tailWord_7219491
  simp only [CollatzResearch.WordTrace]
  refine ⟨263316469088024572744490327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175544312725349715162993551 263316469088024572744490327)
  ·
    refine ⟨394974703632036859116735491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263316469088024572744490327 394974703632036859116735491)
    ·
      refine ⟨592462055448055288675103237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394974703632036859116735491 592462055448055288675103237)
      ·
        refine ⟨111086635396510366626581857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 592462055448055288675103237 111086635396510366626581857)
        ·
          refine ⟨83314976547382774969936393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111086635396510366626581857 83314976547382774969936393)
          ·
            refine ⟨62486232410537081227452295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83314976547382774969936393 62486232410537081227452295)
            ·
              refine ⟨93729348615805621841178443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62486232410537081227452295 93729348615805621841178443)
              ·
                refine ⟨140594022923708432761767665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93729348615805621841178443 140594022923708432761767665)
                ·
                  refine ⟨105445517192781324571325749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140594022923708432761767665 105445517192781324571325749)
                  ·
                    refine ⟨9885517236823249178561789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105445517192781324571325749 9885517236823249178561789)
                    ·
                      refine ⟨3707068963808718441960671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9885517236823249178561789 3707068963808718441960671)
                      ·
                        rfl

theorem cell23_7219491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_7219491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219491 prefixEnd_7219491 := by exact prefixLift 7219491
  have htrace : WordTrace (prefixWord ++ tailWord_7219491) baseStart_7219491 baseEnd_7219491 := by
    simpa [prefixWord, tailWord_7219491, baseEnd_7219491] using wordTrace_append hprefix tailTrace_7219491
  have hstable : (prefixWord ++ tailWord_7219491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219491).length < 2 ^ (prefixWord ++ tailWord_7219491).sum := by decide
  have hdescent : baseEnd_7219491 < baseStart_7219491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219551 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_7219551 : Nat := 118140960795 + 7219551 * 2 ^ 59
def prefixEnd_7219551 : Nat := 4983230072969 + 3 ^ 40 * 7219551 * 2
def baseEnd_7219551 : Nat := 3707099772647988207210395

theorem tailTrace_7219551 : CollatzResearch.WordTrace tailWord_7219551 prefixEnd_7219551 3707099772647988207210395 := by
  unfold tailWord_7219551
  simp only [CollatzResearch.WordTrace]
  refine ⟨263318657467807202991674507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175545771645204801994449671 263318657467807202991674507)
  ·
    refine ⟨394977986201710804487511761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263318657467807202991674507 394977986201710804487511761)
    ·
      refine ⟨296233489651283103365633821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394977986201710804487511761 296233489651283103365633821)
      ·
        refine ⟨111087558619231163762112683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296233489651283103365633821 111087558619231163762112683)
        ·
          refine ⟨166631337928846745643169025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111087558619231163762112683 166631337928846745643169025)
          ·
            refine ⟨124973503446635059232376769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166631337928846745643169025 124973503446635059232376769)
            ·
              refine ⟨93730127584976294424282577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124973503446635059232376769 93730127584976294424282577)
              ·
                refine ⟨70297595688732220818211933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93730127584976294424282577 70297595688732220818211933)
                ·
                  refine ⟨26361598383274582806829475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70297595688732220818211933 26361598383274582806829475)
                  ·
                    refine ⟨39542397574911874210244213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26361598383274582806829475 39542397574911874210244213)
                    ·
                      refine ⟨3707099772647988207210395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39542397574911874210244213 3707099772647988207210395)
                      ·
                        rfl

theorem cell23_7219551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_7219551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219551 prefixEnd_7219551 := by exact prefixLift 7219551
  have htrace : WordTrace (prefixWord ++ tailWord_7219551) baseStart_7219551 baseEnd_7219551 := by
    simpa [prefixWord, tailWord_7219551, baseEnd_7219551] using wordTrace_append hprefix tailTrace_7219551
  have hstable : (prefixWord ++ tailWord_7219551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219551).length < 2 ^ (prefixWord ++ tailWord_7219551).sum := by decide
  have hdescent : baseEnd_7219551 < baseStart_7219551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219552 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 2, 3, 2]
def baseStart_7219552 : Nat := 118140960795 + 7219552 * 2 ^ 59
def prefixEnd_7219552 : Nat := 4983230072969 + 3 ^ 40 * 7219552 * 2
def baseEnd_7219552 : Nat := 3707100286128642703297891

theorem tailTrace_7219552 : CollatzResearch.WordTrace tailWord_7219552 prefixEnd_7219552 3707100286128642703297891 := by
  unfold tailWord_7219552
  simp only [CollatzResearch.WordTrace]
  refine ⟨131659346970401790081230455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175545795960535720108307273 131659346970401790081230455)
  ·
    refine ⟨197489020455602685121845683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131659346970401790081230455 197489020455602685121845683)
    ·
      refine ⟨296233530683404027682768525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197489020455602685121845683 296233530683404027682768525)
      ·
        refine ⟨111087574006276510381038197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296233530683404027682768525 111087574006276510381038197)
        ·
          refine ⟨10414460063088422848222331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111087574006276510381038197 10414460063088422848222331)
          ·
            refine ⟨15621690094632634272333497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10414460063088422848222331 15621690094632634272333497)
            ·
              refine ⟨11716267570974475704250123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15621690094632634272333497 11716267570974475704250123)
              ·
                refine ⟨17574401356461713556375185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11716267570974475704250123 17574401356461713556375185)
                ·
                  refine ⟨13180801017346285167281389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17574401356461713556375185 13180801017346285167281389)
                  ·
                    refine ⟨4942800381504856937730521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13180801017346285167281389 4942800381504856937730521)
                    ·
                      refine ⟨3707100286128642703297891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4942800381504856937730521 3707100286128642703297891)
                      ·
                        rfl

theorem cell23_7219552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_7219552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219552 prefixEnd_7219552 := by exact prefixLift 7219552
  have htrace : WordTrace (prefixWord ++ tailWord_7219552) baseStart_7219552 baseEnd_7219552 := by
    simpa [prefixWord, tailWord_7219552, baseEnd_7219552] using wordTrace_append hprefix tailTrace_7219552
  have hstable : (prefixWord ++ tailWord_7219552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219552).length < 2 ^ (prefixWord ++ tailWord_7219552).sum := by decide
  have hdescent : baseEnd_7219552 < baseStart_7219552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219562 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_7219562 : Nat := 118140960795 + 7219562 * 2 ^ 59
def prefixEnd_7219562 : Nat := 4983230072969 + 3 ^ 40 * 7219562 * 2
def baseEnd_7219562 : Nat := 1235701806978395888057615

theorem tailTrace_7219562 : CollatzResearch.WordTrace tailWord_7219562 prefixEnd_7219562 1235701806978395888057615 := by
  unfold tailWord_7219562
  simp only [CollatzResearch.WordTrace]
  refine ⟨65829764667691837967581235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175546039113844901246883293 65829764667691837967581235)
  ·
    refine ⟨98744647001537756951371853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65829764667691837967581235 98744647001537756951371853)
    ·
      refine ⟨37029242625576658856764445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98744647001537756951371853 37029242625576658856764445)
      ·
        refine ⟨13885965984591247071286667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37029242625576658856764445 13885965984591247071286667)
        ·
          refine ⟨20828948976886870606930001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13885965984591247071286667 20828948976886870606930001)
          ·
            refine ⟨15621711732665152955197501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20828948976886870606930001 15621711732665152955197501)
            ·
              refine ⟨5858141899749432358199063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15621711732665152955197501 5858141899749432358199063)
              ·
                refine ⟨8787212849624148537298595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858141899749432358199063 8787212849624148537298595)
                ·
                  refine ⟨13180819274436222805947893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8787212849624148537298595 13180819274436222805947893)
                  ·
                    refine ⟨1235701806978395888057615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13180819274436222805947893 1235701806978395888057615)
                    ·
                      rfl

theorem cell23_7219562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_7219562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219562 prefixEnd_7219562 := by exact prefixLift 7219562
  have htrace : WordTrace (prefixWord ++ tailWord_7219562) baseStart_7219562 baseEnd_7219562 := by
    simpa [prefixWord, tailWord_7219562, baseEnd_7219562] using wordTrace_append hprefix tailTrace_7219562
  have hstable : (prefixWord ++ tailWord_7219562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219562).length < 2 ^ (prefixWord ++ tailWord_7219562).sum := by decide
  have hdescent : baseEnd_7219562 < baseStart_7219562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219568 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_7219568 : Nat := 118140960795 + 7219568 * 2 ^ 59
def prefixEnd_7219568 : Nat := 4983230072969 + 3 ^ 40 * 7219568 * 2
def baseEnd_7219568 : Nat := 3707108501819114640697817

theorem tailTrace_7219568 : CollatzResearch.WordTrace tailWord_7219568 prefixEnd_7219568 3707108501819114640697817 := by
  unfold tailWord_7219568
  simp only [CollatzResearch.WordTrace]
  refine ⟨131659638754372807447521679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175546185005830409930028905 131659638754372807447521679)
  ·
    refine ⟨197489458131559211171282519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131659638754372807447521679 197489458131559211171282519)
    ·
      refine ⟨296234187197338816756923779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197489458131559211171282519 296234187197338816756923779)
      ·
        refine ⟨444351280796008225135385669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296234187197338816756923779 444351280796008225135385669)
        ·
          refine ⟨83315865149251542212884813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444351280796008225135385669 83315865149251542212884813)
          ·
            refine ⟨31243449430969328329831805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83315865149251542212884813 31243449430969328329831805)
            ·
              refine ⟨11716293536613498123686927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31243449430969328329831805 11716293536613498123686927)
              ·
                refine ⟨17574440304920247185530391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11716293536613498123686927 17574440304920247185530391)
                ·
                  refine ⟨26361660457380370778295587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17574440304920247185530391 26361660457380370778295587)
                  ·
                    refine ⟨39542490686070556167443381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26361660457380370778295587 39542490686070556167443381)
                    ·
                      refine ⟨3707108501819114640697817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39542490686070556167443381 3707108501819114640697817)
                      ·
                        rfl

theorem cell23_7219568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_7219568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219568 prefixEnd_7219568 := by exact prefixLift 7219568
  have htrace : WordTrace (prefixWord ++ tailWord_7219568) baseStart_7219568 baseEnd_7219568 := by
    simpa [prefixWord, tailWord_7219568, baseEnd_7219568] using wordTrace_append hprefix tailTrace_7219568
  have hstable : (prefixWord ++ tailWord_7219568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219568).length < 2 ^ (prefixWord ++ tailWord_7219568).sum := by decide
  have hdescent : baseEnd_7219568 < baseStart_7219568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219585 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_7219585 : Nat := 118140960795 + 7219585 * 2 ^ 59
def prefixEnd_7219585 : Nat := 4983230072969 + 3 ^ 40 * 7219585 * 2
def baseEnd_7219585 : Nat := 3707117230990241074185239

theorem tailTrace_7219585 : CollatzResearch.WordTrace tailWord_7219585 prefixEnd_7219585 3707117230990241074185239 := by
  unfold tailWord_7219585
  simp only [CollatzResearch.WordTrace]
  refine ⟨263319897549684026798412209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175546598366456017865608139 263319897549684026798412209)
  ·
    refine ⟨197489923162263020098809157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263319897549684026798412209 197489923162263020098809157)
    ·
      refine ⟨37029360592924316268526717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197489923162263020098809157 37029360592924316268526717)
      ·
        refine ⟨13886010222346618600697519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37029360592924316268526717 13886010222346618600697519)
        ·
          refine ⟨20829015333519927901046279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886010222346618600697519 20829015333519927901046279)
          ·
            refine ⟨31243523000279891851569419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20829015333519927901046279 31243523000279891851569419)
            ·
              refine ⟨46865284500419837777354129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31243523000279891851569419 46865284500419837777354129)
              ·
                refine ⟨35148963375314878333015597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46865284500419837777354129 35148963375314878333015597)
                ·
                  refine ⟨13180861265743079374880849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35148963375314878333015597 13180861265743079374880849)
                  ·
                    refine ⟨9885645949307309531160637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13180861265743079374880849 9885645949307309531160637)
                    ·
                      refine ⟨3707117230990241074185239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9885645949307309531160637 3707117230990241074185239)
                      ·
                        rfl

theorem cell23_7219585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_7219585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219585 prefixEnd_7219585 := by exact prefixLift 7219585
  have htrace : WordTrace (prefixWord ++ tailWord_7219585) baseStart_7219585 baseEnd_7219585 := by
    simpa [prefixWord, tailWord_7219585, baseEnd_7219585] using wordTrace_append hprefix tailTrace_7219585
  have hstable : (prefixWord ++ tailWord_7219585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219585).length < 2 ^ (prefixWord ++ tailWord_7219585).sum := by decide
  have hdescent : baseEnd_7219585 < baseStart_7219585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219615 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 3]
def baseStart_7219615 : Nat := 118140960795 + 7219615 * 2 ^ 59
def prefixEnd_7219615 : Nat := 4983230072969 + 3 ^ 40 * 7219615 * 2
def baseEnd_7219615 : Nat := 3707132635409875956810101

theorem tailTrace_7219615 : CollatzResearch.WordTrace tailWord_7219615 prefixEnd_7219615 3707132635409875956810101 := by
  unfold tailWord_7219615
  simp only [CollatzResearch.WordTrace]
  refine ⟨263320991739575341922004299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175547327826383561281336199 263320991739575341922004299)
  ·
    refine ⟨394981487609363012883006449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263320991739575341922004299 394981487609363012883006449)
    ·
      refine ⟨296236115707022259662254837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394981487609363012883006449 296236115707022259662254837)
      ·
        refine ⟨27772135847533336843336391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296236115707022259662254837 27772135847533336843336391)
        ·
          refine ⟨41658203771300005265004587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27772135847533336843336391 41658203771300005265004587)
          ·
            refine ⟨62487305656950007897506881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41658203771300005265004587 62487305656950007897506881)
            ·
              refine ⟨46865479242712505923130161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62487305656950007897506881 46865479242712505923130161)
              ·
                refine ⟨35149109432034379442347621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46865479242712505923130161 35149109432034379442347621)
                ·
                  refine ⟨6590458018506446145440179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35149109432034379442347621 6590458018506446145440179)
                  ·
                    refine ⟨9885687027759669218160269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6590458018506446145440179 9885687027759669218160269)
                    ·
                      refine ⟨3707132635409875956810101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9885687027759669218160269 3707132635409875956810101)
                      ·
                        rfl

theorem cell23_7219615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_7219615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219615 prefixEnd_7219615 := by exact prefixLift 7219615
  have htrace : WordTrace (prefixWord ++ tailWord_7219615) baseStart_7219615 baseEnd_7219615 := by
    simpa [prefixWord, tailWord_7219615, baseEnd_7219615] using wordTrace_append hprefix tailTrace_7219615
  have hstable : (prefixWord ++ tailWord_7219615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219615).length < 2 ^ (prefixWord ++ tailWord_7219615).sum := by decide
  have hdescent : baseEnd_7219615 < baseStart_7219615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219658 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_7219658 : Nat := 118140960795 + 7219658 * 2 ^ 59
def prefixEnd_7219658 : Nat := 4983230072969 + 3 ^ 40 * 7219658 * 2
def baseEnd_7219658 : Nat := 3707154715078019288572403

theorem tailTrace_7219658 : CollatzResearch.WordTrace tailWord_7219658 prefixEnd_7219658 3707154715078019288572403 := by
  unfold tailWord_7219658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65830640019604890066454907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175548373385613040177213085 65830640019604890066454907)
  ·
    refine ⟨98745960029407335099682361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65830640019604890066454907 98745960029407335099682361)
    ·
      refine ⟨74059470022055501324761771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98745960029407335099682361 74059470022055501324761771)
      ·
        refine ⟨111089205033083251987142657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74059470022055501324761771 111089205033083251987142657)
        ·
          refine ⟨83316903774812438990356993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111089205033083251987142657 83316903774812438990356993)
          ·
            refine ⟨62487677831109329242767745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83316903774812438990356993 62487677831109329242767745)
            ·
              refine ⟨46865758373331996932075809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62487677831109329242767745 46865758373331996932075809)
              ·
                refine ⟨35149318779998997699056857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46865758373331996932075809 35149318779998997699056857)
                ·
                  refine ⟨26361989084999248274292643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35149318779998997699056857 26361989084999248274292643)
                  ·
                    refine ⟨39542983627498872411438965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26361989084999248274292643 39542983627498872411438965)
                    ·
                      refine ⟨3707154715078019288572403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39542983627498872411438965 3707154715078019288572403)
                      ·
                        rfl

theorem cell23_7219658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_7219658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219658 prefixEnd_7219658 := by exact prefixLift 7219658
  have htrace : WordTrace (prefixWord ++ tailWord_7219658) baseStart_7219658 baseEnd_7219658 := by
    simpa [prefixWord, tailWord_7219658, baseEnd_7219658] using wordTrace_append hprefix tailTrace_7219658
  have hstable : (prefixWord ++ tailWord_7219658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219658).length < 2 ^ (prefixWord ++ tailWord_7219658).sum := by decide
  have hdescent : baseEnd_7219658 < baseStart_7219658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219708 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_7219708 : Nat := 118140960795 + 7219708 * 2 ^ 59
def prefixEnd_7219708 : Nat := 4983230072969 + 3 ^ 40 * 7219708 * 2
def baseEnd_7219708 : Nat := 1235726796370248030982391

theorem tailTrace_7219708 : CollatzResearch.WordTrace tailWord_7219708 prefixEnd_7219708 1235726796370248030982391 := by
  unfold tailWord_7219708
  simp only [CollatzResearch.WordTrace]
  refine ⟨131662191864119209402569889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175549589152158945870093185 131662191864119209402569889)
  ·
    refine ⟨98746643898089407051927417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131662191864119209402569889 98746643898089407051927417)
    ·
      refine ⟨74059982923567055288945563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98746643898089407051927417 74059982923567055288945563)
      ·
        refine ⟨111089974385350582933418345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74059982923567055288945563 111089974385350582933418345)
        ·
          refine ⟨83317480789012937200063759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111089974385350582933418345 83317480789012937200063759)
          ·
            refine ⟨124976221183519405800095639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83317480789012937200063759 124976221183519405800095639)
            ·
              refine ⟨187464331775279108700143459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124976221183519405800095639 187464331775279108700143459)
              ·
                refine ⟨281196497662918663050215189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187464331775279108700143459 281196497662918663050215189)
                ·
                  refine ⟨13181085827949312330478837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281196497662918663050215189 13181085827949312330478837)
                  ·
                    refine ⟨1235726796370248030982391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13181085827949312330478837 1235726796370248030982391)
                    ·
                      rfl

theorem cell23_7219708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_7219708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219708 prefixEnd_7219708 := by exact prefixLift 7219708
  have htrace : WordTrace (prefixWord ++ tailWord_7219708) baseStart_7219708 baseEnd_7219708 := by
    simpa [prefixWord, tailWord_7219708, baseEnd_7219708] using wordTrace_append hprefix tailTrace_7219708
  have hstable : (prefixWord ++ tailWord_7219708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219708).length < 2 ^ (prefixWord ++ tailWord_7219708).sum := by decide
  have hdescent : baseEnd_7219708 < baseStart_7219708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219745 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7219745 : Nat := 118140960795 + 7219745 * 2 ^ 59
def prefixEnd_7219745 : Nat := 4983230072969 + 3 ^ 40 * 7219745 * 2
def baseEnd_7219745 : Nat := 3707199387894960448184503

theorem tailTrace_7219745 : CollatzResearch.WordTrace tailWord_7219745 prefixEnd_7219745 3707199387894960448184503 := by
  unfold tailWord_7219745
  simp only [CollatzResearch.WordTrace]
  refine ⟨263325733229104374124236689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175550488819402916082824459 263325733229104374124236689)
  ·
    refine ⟨197494299921828280593177517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263325733229104374124236689 197494299921828280593177517)
    ·
      refine ⟨74060362470685605222441569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197494299921828280593177517 74060362470685605222441569)
      ·
        refine ⟨55545271853014203916831177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74060362470685605222441569 55545271853014203916831177)
        ·
          refine ⟨41658953889760652937623383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55545271853014203916831177 41658953889760652937623383)
          ·
            refine ⟨62488430834640979406435075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41658953889760652937623383 62488430834640979406435075)
            ·
              refine ⟨93732646251961469109652613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62488430834640979406435075 93732646251961469109652613)
              ·
                refine ⟨17574871172242775458059865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93732646251961469109652613 17574871172242775458059865)
                ·
                  refine ⟨13181153379182081593544899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17574871172242775458059865 13181153379182081593544899)
                  ·
                    refine ⟨19771730068773122390317349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13181153379182081593544899 19771730068773122390317349)
                    ·
                      refine ⟨3707199387894960448184503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19771730068773122390317349 3707199387894960448184503)
                      ·
                        rfl

theorem cell23_7219745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7219745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219745 prefixEnd_7219745 := by exact prefixLift 7219745
  have htrace : WordTrace (prefixWord ++ tailWord_7219745) baseStart_7219745 baseEnd_7219745 := by
    simpa [prefixWord, tailWord_7219745, baseEnd_7219745] using wordTrace_append hprefix tailTrace_7219745
  have hstable : (prefixWord ++ tailWord_7219745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219745).length < 2 ^ (prefixWord ++ tailWord_7219745).sum := by decide
  have hdescent : baseEnd_7219745 < baseStart_7219745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219765 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_7219765 : Nat := 118140960795 + 7219765 * 2 ^ 59
def prefixEnd_7219765 : Nat := 4983230072969 + 3 ^ 40 * 7219765 * 2
def baseEnd_7219765 : Nat := 3707209657508050369934411

theorem tailTrace_7219765 : CollatzResearch.WordTrace tailWord_7219765 prefixEnd_7219765 3707209657508050369934411 := by
  unfold tailWord_7219765
  simp only [CollatzResearch.WordTrace]
  refine ⟨263326462689031917539964749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175550975126021278359976499 263326462689031917539964749)
  ·
    refine ⟨98747423508386969077486781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263326462689031917539964749 98747423508386969077486781)
    ·
      refine ⟨37030283815645113404057543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98747423508386969077486781 37030283815645113404057543)
      ·
        refine ⟨55545425723467670106086315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37030283815645113404057543 55545425723467670106086315)
        ·
          refine ⟨83318138585201505159129473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55545425723467670106086315 83318138585201505159129473)
          ·
            refine ⟨62488603938901128869347105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83318138585201505159129473 62488603938901128869347105)
            ·
              refine ⟨46866452954175846652010329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62488603938901128869347105 46866452954175846652010329)
              ·
                refine ⟨35149839715631884989007747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46866452954175846652010329 35149839715631884989007747)
                ·
                  refine ⟨52724759573447827483511621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35149839715631884989007747 52724759573447827483511621)
                  ·
                    refine ⟨9885892420021467653158429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52724759573447827483511621 9885892420021467653158429)
                    ·
                      refine ⟨3707209657508050369934411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9885892420021467653158429 3707209657508050369934411)
                      ·
                        rfl

theorem cell23_7219765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_7219765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219765 prefixEnd_7219765 := by exact prefixLift 7219765
  have htrace : WordTrace (prefixWord ++ tailWord_7219765) baseStart_7219765 baseEnd_7219765 := by
    simpa [prefixWord, tailWord_7219765, baseEnd_7219765] using wordTrace_append hprefix tailTrace_7219765
  have hstable : (prefixWord ++ tailWord_7219765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219765).length < 2 ^ (prefixWord ++ tailWord_7219765).sum := by decide
  have hdescent : baseEnd_7219765 < baseStart_7219765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219772 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_7219772 : Nat := 118140960795 + 7219772 * 2 ^ 59
def prefixEnd_7219772 : Nat := 4983230072969 + 3 ^ 40 * 7219772 * 2
def baseEnd_7219772 : Nat := 1235737750624210614182293

theorem tailTrace_7219772 : CollatzResearch.WordTrace tailWord_7219772 prefixEnd_7219772 1235737750624210614182293 := by
  unfold tailWord_7219772
  simp only [CollatzResearch.WordTrace]
  refine ⟨131663359000003278867734785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175551145333337705156979713 131663359000003278867734785)
  ·
    refine ⟨98747519250002459150801089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131663359000003278867734785 98747519250002459150801089)
    ·
      refine ⟨74060639437501844363100817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98747519250002459150801089 74060639437501844363100817)
      ·
        refine ⟨55545479578126383272325613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74060639437501844363100817 55545479578126383272325613)
        ·
          refine ⟨20829554841797393727122105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55545479578126383272325613 20829554841797393727122105)
          ·
            refine ⟨15622166131348045295341579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20829554841797393727122105 15622166131348045295341579)
            ·
              refine ⟨23433249197022067943012369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15622166131348045295341579 23433249197022067943012369)
              ·
                refine ⟨17574936897766550957259277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23433249197022067943012369 17574936897766550957259277)
                ·
                  refine ⟨6590601336662456608972229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17574936897766550957259277 6590601336662456608972229)
                  ·
                    refine ⟨1235737750624210614182293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590601336662456608972229 1235737750624210614182293)
                    ·
                      rfl

theorem cell23_7219772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_7219772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219772 prefixEnd_7219772 := by exact prefixLift 7219772
  have htrace : WordTrace (prefixWord ++ tailWord_7219772) baseStart_7219772 baseEnd_7219772 := by
    simpa [prefixWord, tailWord_7219772, baseEnd_7219772] using wordTrace_append hprefix tailTrace_7219772
  have hstable : (prefixWord ++ tailWord_7219772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219772).length < 2 ^ (prefixWord ++ tailWord_7219772).sum := by decide
  have hdescent : baseEnd_7219772 < baseStart_7219772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219886 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7219886 : Nat := 118140960795 + 7219886 * 2 ^ 59
def prefixEnd_7219886 : Nat := 4983230072969 + 3 ^ 40 * 7219886 * 2
def baseEnd_7219886 : Nat := 3707271788667244396521355

theorem tailTrace_7219886 : CollatzResearch.WordTrace tailWord_7219886 prefixEnd_7219886 3707271788667244396521355 := by
  unfold tailWord_7219886
  simp only [CollatzResearch.WordTrace]
  refine ⟨32916359490199194400639939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175553917281062370136746341 32916359490199194400639939)
  ·
    refine ⟨49374539235298791600959909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32916359490199194400639939 49374539235298791600959909)
    ·
      refine ⟨9257726106618523425179983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49374539235298791600959909 9257726106618523425179983)
      ·
        refine ⟨13886589159927785137769975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9257726106618523425179983 13886589159927785137769975)
        ·
          refine ⟨20829883739891677706654963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886589159927785137769975 20829883739891677706654963)
          ·
            refine ⟨31244825609837516559982445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20829883739891677706654963 31244825609837516559982445)
            ·
              refine ⟨11716809603689068709993417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31244825609837516559982445 11716809603689068709993417)
              ·
                refine ⟨8787607202766801532495063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11716809603689068709993417 8787607202766801532495063)
                ·
                  refine ⟨13181410804150202298742595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8787607202766801532495063 13181410804150202298742595)
                  ·
                    refine ⟨19772116206225303448113893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13181410804150202298742595 19772116206225303448113893)
                    ·
                      refine ⟨3707271788667244396521355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19772116206225303448113893 3707271788667244396521355)
                      ·
                        rfl

theorem cell23_7219886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7219886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219886 prefixEnd_7219886 := by exact prefixLift 7219886
  have htrace : WordTrace (prefixWord ++ tailWord_7219886) baseStart_7219886 baseEnd_7219886 := by
    simpa [prefixWord, tailWord_7219886, baseEnd_7219886] using wordTrace_append hprefix tailTrace_7219886
  have hstable : (prefixWord ++ tailWord_7219886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219886).length < 2 ^ (prefixWord ++ tailWord_7219886).sum := by decide
  have hdescent : baseEnd_7219886 < baseStart_7219886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219935 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 8]
def baseStart_7219935 : Nat := 118140960795 + 7219935 * 2 ^ 59
def prefixEnd_7219935 : Nat := 4983230072969 + 3 ^ 40 * 7219935 * 2
def baseEnd_7219935 : Nat := 1235765649739771568269543

theorem tailTrace_7219935 : CollatzResearch.WordTrace tailWord_7219935 prefixEnd_7219935 1235765649739771568269543 := by
  unfold tailWord_7219935
  simp only [CollatzResearch.WordTrace]
  refine ⟨263332663098416036573653259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175555108732277357715768839 263332663098416036573653259)
  ·
    refine ⟨394998994647624054860479889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263332663098416036573653259 394998994647624054860479889)
    ·
      refine ⟨296249245985718041145359917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394998994647624054860479889 296249245985718041145359917)
      ·
        refine ⟨111093467244644265429509969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296249245985718041145359917 111093467244644265429509969)
        ·
          refine ⟨83320100433483199072132477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111093467244644265429509969 83320100433483199072132477)
          ·
            refine ⟨31245037662556199652049679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83320100433483199072132477 31245037662556199652049679)
            ·
              refine ⟨46867556493834299478074519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31245037662556199652049679 46867556493834299478074519)
              ·
                refine ⟨70301334740751449217111779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46867556493834299478074519 70301334740751449217111779)
                ·
                  refine ⟨105452002111127173825667669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70301334740751449217111779 105452002111127173825667669)
                  ·
                    refine ⟨1235765649739771568269543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105452002111127173825667669 1235765649739771568269543)
                    ·
                      rfl

theorem cell23_7219935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_7219935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219935 prefixEnd_7219935 := by exact prefixLift 7219935
  have htrace : WordTrace (prefixWord ++ tailWord_7219935) baseStart_7219935 baseEnd_7219935 := by
    simpa [prefixWord, tailWord_7219935, baseEnd_7219935] using wordTrace_append hprefix tailTrace_7219935
  have hstable : (prefixWord ++ tailWord_7219935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219935).length < 2 ^ (prefixWord ++ tailWord_7219935).sum := by decide
  have hdescent : baseEnd_7219935 < baseStart_7219935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219945 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_7219945 : Nat := 118140960795 + 7219945 * 2 ^ 59
def prefixEnd_7219945 : Nat := 4983230072969 + 3 ^ 40 * 7219945 * 2
def baseEnd_7219945 : Nat := 3707302084025859665683583

theorem tailTrace_7219945 : CollatzResearch.WordTrace tailWord_7219945 prefixEnd_7219945 3707302084025859665683583 := by
  unfold tailWord_7219945
  simp only [CollatzResearch.WordTrace]
  refine ⟨263333027828379808281517289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175555351885586538854344859 263333027828379808281517289)
  ·
    refine ⟨197499770871284856211137967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263333027828379808281517289 197499770871284856211137967)
    ·
      refine ⟨296249656306927284316706951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197499770871284856211137967 296249656306927284316706951)
      ·
        refine ⟨444374484460390926475060427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296249656306927284316706951 444374484460390926475060427)
        ·
          refine ⟨666561726690586389712590641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444374484460390926475060427 666561726690586389712590641)
          ·
            refine ⟨499921295017939792284442981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666561726690586389712590641 499921295017939792284442981)
            ·
              refine ⟨93735242815863711053333059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499921295017939792284442981 93735242815863711053333059)
              ·
                refine ⟨140602864223795566579999589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93735242815863711053333059 140602864223795566579999589)
                ·
                  refine ⟨26363037041961668733749923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140602864223795566579999589 26363037041961668733749923)
                  ·
                    refine ⟨39544555562942503100624885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26363037041961668733749923 39544555562942503100624885)
                    ·
                      refine ⟨3707302084025859665683583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39544555562942503100624885 3707302084025859665683583)
                      ·
                        rfl

theorem cell23_7219945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_7219945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219945 prefixEnd_7219945 := by exact prefixLift 7219945
  have htrace : WordTrace (prefixWord ++ tailWord_7219945) baseStart_7219945 baseEnd_7219945 := by
    simpa [prefixWord, tailWord_7219945, baseEnd_7219945] using wordTrace_append hprefix tailTrace_7219945
  have hstable : (prefixWord ++ tailWord_7219945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219945).length < 2 ^ (prefixWord ++ tailWord_7219945).sum := by decide
  have hdescent : baseEnd_7219945 < baseStart_7219945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219955 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4]
def baseStart_7219955 : Nat := 118140960795 + 7219955 * 2 ^ 59
def prefixEnd_7219955 : Nat := 4983230072969 + 3 ^ 40 * 7219955 * 2
def baseEnd_7219955 : Nat := 3707307218832404626558537

theorem tailTrace_7219955 : CollatzResearch.WordTrace tailWord_7219955 prefixEnd_7219955 3707307218832404626558537 := by
  unfold tailWord_7219955
  simp only [CollatzResearch.WordTrace]
  refine ⟨263333392558343579989381319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175555595038895719992920879 263333392558343579989381319)
  ·
    refine ⟨395000088837515369984071979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263333392558343579989381319 395000088837515369984071979)
    ·
      refine ⟨592500133256273054976107969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395000088837515369984071979 592500133256273054976107969)
      ·
        refine ⟨444375099942204791232080977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592500133256273054976107969 444375099942204791232080977)
        ·
          refine ⟨333281324956653593424060733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444375099942204791232080977 333281324956653593424060733)
          ·
            refine ⟨124980496858745097534022775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333281324956653593424060733 124980496858745097534022775)
            ·
              refine ⟨187470745288117646301034163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124980496858745097534022775 187470745288117646301034163)
              ·
                refine ⟨281206117932176469451551245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187470745288117646301034163 281206117932176469451551245)
                ·
                  refine ⟨105452294224566176044331717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281206117932176469451551245 105452294224566176044331717)
                  ·
                    refine ⟨19772305167106158008312197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105452294224566176044331717 19772305167106158008312197)
                    ·
                      refine ⟨3707307218832404626558537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19772305167106158008312197 3707307218832404626558537)
                      ·
                        rfl

theorem cell23_7219955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_7219955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219955 prefixEnd_7219955 := by exact prefixLift 7219955
  have htrace : WordTrace (prefixWord ++ tailWord_7219955) baseStart_7219955 baseEnd_7219955 := by
    simpa [prefixWord, tailWord_7219955, baseEnd_7219955] using wordTrace_append hprefix tailTrace_7219955
  have hstable : (prefixWord ++ tailWord_7219955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219955).length < 2 ^ (prefixWord ++ tailWord_7219955).sum := by decide
  have hdescent : baseEnd_7219955 < baseStart_7219955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219957 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7219957 : Nat := 118140960795 + 7219957 * 2 ^ 59
def prefixEnd_7219957 : Nat := 4983230072969 + 3 ^ 40 * 7219957 * 2
def baseEnd_7219957 : Nat := 3707308245793713618733529

theorem tailTrace_7219957 : CollatzResearch.WordTrace tailWord_7219957 prefixEnd_7219957 3707308245793713618733529 := by
  unfold tailWord_7219957
  simp only [CollatzResearch.WordTrace]
  refine ⟨263333465504336334330954125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175555643669557556220636083 263333465504336334330954125)
  ·
    refine ⟨98750049564126125374107797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263333465504336334330954125 98750049564126125374107797)
    ·
      refine ⟨4628908573318412126911303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98750049564126125374107797 4628908573318412126911303)
      ·
        refine ⟨6943362859977618190366955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628908573318412126911303 6943362859977618190366955)
        ·
          refine ⟨10415044289966427285550433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6943362859977618190366955 10415044289966427285550433)
          ·
            refine ⟨7811283217474820464162825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10415044289966427285550433 7811283217474820464162825)
            ·
              refine ⟨5858462413106115348122119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7811283217474820464162825 5858462413106115348122119)
              ·
                refine ⟨8787693619659173022183179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858462413106115348122119 8787693619659173022183179)
                ·
                  refine ⟨13181540429488759533274769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8787693619659173022183179 13181540429488759533274769)
                  ·
                    refine ⟨9886155322116569649956077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13181540429488759533274769 9886155322116569649956077)
                    ·
                      refine ⟨3707308245793713618733529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9886155322116569649956077 3707308245793713618733529)
                      ·
                        rfl

theorem cell23_7219957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7219957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219957 prefixEnd_7219957 := by exact prefixLift 7219957
  have htrace : WordTrace (prefixWord ++ tailWord_7219957) baseStart_7219957 baseEnd_7219957 := by
    simpa [prefixWord, tailWord_7219957, baseEnd_7219957] using wordTrace_append hprefix tailTrace_7219957
  have hstable : (prefixWord ++ tailWord_7219957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219957).length < 2 ^ (prefixWord ++ tailWord_7219957).sum := by decide
  have hdescent : baseEnd_7219957 < baseStart_7219957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219959 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 4, 2, 2]
def baseStart_7219959 : Nat := 118140960795 + 7219959 * 2 ^ 59
def prefixEnd_7219959 : Nat := 4983230072969 + 3 ^ 40 * 7219959 * 2
def baseEnd_7219959 : Nat := 3707309272755022610908519

theorem tailTrace_7219959 : CollatzResearch.WordTrace tailWord_7219959 prefixEnd_7219959 3707309272755022610908519 := by
  unfold tailWord_7219959
  simp only [CollatzResearch.WordTrace]
  refine ⟨263333538450329088672526931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175555692300219392448351287 263333538450329088672526931)
  ·
    refine ⟨395000307675493633008790397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263333538450329088672526931 395000307675493633008790397)
    ·
      refine ⟨148125115378310112378296399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395000307675493633008790397 148125115378310112378296399)
      ·
        refine ⟨222187673067465168567444599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148125115378310112378296399 222187673067465168567444599)
        ·
          refine ⟨333281509601197752851166899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222187673067465168567444599 333281509601197752851166899)
          ·
            refine ⟨499922264401796629276750349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333281509601197752851166899 499922264401796629276750349)
            ·
              refine ⟨187470849150673735978781381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499922264401796629276750349 187470849150673735978781381)
              ·
                refine ⟨35150784215751325496021509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187470849150673735978781381 35150784215751325496021509)
                ·
                  refine ⟨6590772040453373530504033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35150784215751325496021509 6590772040453373530504033)
                  ·
                    refine ⟨4943079030340030147878025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6590772040453373530504033 4943079030340030147878025)
                    ·
                      refine ⟨3707309272755022610908519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943079030340030147878025 3707309272755022610908519)
                      ·
                        rfl

theorem cell23_7219959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_7219959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219959 prefixEnd_7219959 := by exact prefixLift 7219959
  have htrace : WordTrace (prefixWord ++ tailWord_7219959) baseStart_7219959 baseEnd_7219959 := by
    simpa [prefixWord, tailWord_7219959, baseEnd_7219959] using wordTrace_append hprefix tailTrace_7219959
  have hstable : (prefixWord ++ tailWord_7219959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219959).length < 2 ^ (prefixWord ++ tailWord_7219959).sum := by decide
  have hdescent : baseEnd_7219959 < baseStart_7219959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219965 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 9]
def baseStart_7219965 : Nat := 118140960795 + 7219965 * 2 ^ 59
def prefixEnd_7219965 : Nat := 4983230072969 + 3 ^ 40 * 7219965 * 2
def baseEnd_7219965 : Nat := 411923594848772176381499

theorem tailTrace_7219965 : CollatzResearch.WordTrace tailWord_7219965 prefixEnd_7219965 411923594848772176381499 := by
  unfold tailWord_7219965
  simp only [CollatzResearch.WordTrace]
  refine ⟨263333757288307351697245349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175555838192204901131496899 263333757288307351697245349)
  ·
    refine ⟨49375079491557628443233503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263333757288307351697245349 49375079491557628443233503)
    ·
      refine ⟨74062619237336442664850255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49375079491557628443233503 74062619237336442664850255)
      ·
        refine ⟨111093928856004663997275383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74062619237336442664850255 111093928856004663997275383)
        ·
          refine ⟨166640893284006995995913075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111093928856004663997275383 166640893284006995995913075)
          ·
            refine ⟨249961339926010493993869613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166640893284006995995913075 249961339926010493993869613)
            ·
              refine ⟨93735502472253935247701105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249961339926010493993869613 93735502472253935247701105)
              ·
                refine ⟨70301626854190451435775829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93735502472253935247701105 70301626854190451435775829)
                ·
                  refine ⟨411923594848772176381499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70301626854190451435775829 411923594848772176381499)
                  ·
                    rfl

theorem cell23_7219965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_7219965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219965 prefixEnd_7219965 := by exact prefixLift 7219965
  have htrace : WordTrace (prefixWord ++ tailWord_7219965) baseStart_7219965 baseEnd_7219965 := by
    simpa [prefixWord, tailWord_7219965, baseEnd_7219965] using wordTrace_append hprefix tailTrace_7219965
  have hstable : (prefixWord ++ tailWord_7219965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219965).length < 2 ^ (prefixWord ++ tailWord_7219965).sum := by decide
  have hdescent : baseEnd_7219965 < baseStart_7219965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219972 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7219972 : Nat := 118140960795 + 7219972 * 2 ^ 59
def prefixEnd_7219972 : Nat := 4983230072969 + 3 ^ 40 * 7219972 * 2
def baseEnd_7219972 : Nat := 3707315948003531060045959

theorem tailTrace_7219972 : CollatzResearch.WordTrace tailWord_7219972 prefixEnd_7219972 3707315948003531060045959 := by
  unfold tailWord_7219972
  simp only [CollatzResearch.WordTrace]
  refine ⟨131667006299640995946375085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175556008399521327928500113 131667006299640995946375085)
  ·
    refine ⟨49375127362365373479890657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131667006299640995946375085 49375127362365373479890657)
    ·
      refine ⟨37031345521774030109917993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49375127362365373479890657 37031345521774030109917993)
      ·
        refine ⟨27773509141330522582438495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37031345521774030109917993 27773509141330522582438495)
        ·
          refine ⟨41660263711995783873657743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27773509141330522582438495 41660263711995783873657743)
          ·
            refine ⟨62490395567993675810486615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41660263711995783873657743 62490395567993675810486615)
            ·
              refine ⟨93735593351990513715729923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62490395567993675810486615 93735593351990513715729923)
              ·
                refine ⟨140603390027985770573594885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93735593351990513715729923 140603390027985770573594885)
                ·
                  refine ⟨26363135630247331982549041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140603390027985770573594885 26363135630247331982549041)
                  ·
                    refine ⟨19772351722685498986911781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26363135630247331982549041 19772351722685498986911781)
                    ·
                      refine ⟨3707315948003531060045959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19772351722685498986911781 3707315948003531060045959)
                      ·
                        rfl

theorem cell23_7219972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7219972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219972 prefixEnd_7219972 := by exact prefixLift 7219972
  have htrace : WordTrace (prefixWord ++ tailWord_7219972) baseStart_7219972 baseEnd_7219972 := by
    simpa [prefixWord, tailWord_7219972, baseEnd_7219972] using wordTrace_append hprefix tailTrace_7219972
  have hstable : (prefixWord ++ tailWord_7219972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219972).length < 2 ^ (prefixWord ++ tailWord_7219972).sum := by decide
  have hdescent : baseEnd_7219972 < baseStart_7219972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7219976 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_7219976 : Nat := 118140960795 + 7219976 * 2 ^ 59
def prefixEnd_7219976 : Nat := 4983230072969 + 3 ^ 40 * 7219976 * 2
def baseEnd_7219976 : Nat := 3707318001926149044395941

theorem tailTrace_7219976 : CollatzResearch.WordTrace tailWord_7219976 prefixEnd_7219976 3707318001926149044395941 := by
  unfold tailWord_7219976
  simp only [CollatzResearch.WordTrace]
  refine ⟨131667079245633750287947891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175556105660845000383930521 131667079245633750287947891)
  ·
    refine ⟨197500618868450625431921837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131667079245633750287947891 197500618868450625431921837)
    ·
      refine ⟨74062732075668984536970689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197500618868450625431921837 74062732075668984536970689)
      ·
        refine ⟨55547049056751738402728017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74062732075668984536970689 55547049056751738402728017)
        ·
          refine ⟨41660286792563803802046013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55547049056751738402728017 41660286792563803802046013)
          ·
            refine ⟨15622607547211426425767255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41660286792563803802046013 15622607547211426425767255)
            ·
              refine ⟨23433911320817139638650883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15622607547211426425767255 23433911320817139638650883)
              ·
                refine ⟨35150866981225709457976325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23433911320817139638650883 35150866981225709457976325)
                ·
                  refine ⟨6590787558979820523370561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35150866981225709457976325 6590787558979820523370561)
                  ·
                    refine ⟨4943090669234865392527921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6590787558979820523370561 4943090669234865392527921)
                    ·
                      refine ⟨3707318001926149044395941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943090669234865392527921 3707318001926149044395941)
                      ·
                        rfl

theorem cell23_7219976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_7219976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7219976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7219976 prefixEnd_7219976 := by exact prefixLift 7219976
  have htrace : WordTrace (prefixWord ++ tailWord_7219976) baseStart_7219976 baseEnd_7219976 := by
    simpa [prefixWord, tailWord_7219976, baseEnd_7219976] using wordTrace_append hprefix tailTrace_7219976
  have hstable : (prefixWord ++ tailWord_7219976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7219976).length < 2 ^ (prefixWord ++ tailWord_7219976).sum := by decide
  have hdescent : baseEnd_7219976 < baseStart_7219976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7219976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220012 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_7220012 : Nat := 118140960795 + 7220012 * 2 ^ 59
def prefixEnd_7220012 : Nat := 4983230072969 + 3 ^ 40 * 7220012 * 2
def baseEnd_7220012 : Nat := 1235778829076570301181925

theorem tailTrace_7220012 : CollatzResearch.WordTrace tailWord_7220012 prefixEnd_7220012 1235778829076570301181925 := by
  unfold tailWord_7220012
  simp only [CollatzResearch.WordTrace]
  refine ⟨131667735759568539362103145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175556981012758052482804193 131667735759568539362103145)
  ·
    refine ⟨98750801819676404521577359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131667735759568539362103145 98750801819676404521577359)
    ·
      refine ⟨148126202729514606782366039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98750801819676404521577359 148126202729514606782366039)
      ·
        refine ⟨222189304094271910173549059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148126202729514606782366039 222189304094271910173549059)
        ·
          refine ⟨333283956141407865260323589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222189304094271910173549059 333283956141407865260323589)
          ·
            refine ⟨62490741776513974736310673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333283956141407865260323589 62490741776513974736310673)
            ·
              refine ⟨46868056332385481052233005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62490741776513974736310673 46868056332385481052233005)
              ·
                refine ⟨17575521124644555394587377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46868056332385481052233005 17575521124644555394587377)
                ·
                  refine ⟨13181640843483416545940533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17575521124644555394587377 13181640843483416545940533)
                  ·
                    refine ⟨1235778829076570301181925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13181640843483416545940533 1235778829076570301181925)
                    ·
                      rfl

theorem cell23_7220012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_7220012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220012 prefixEnd_7220012 := by exact prefixLift 7220012
  have htrace : WordTrace (prefixWord ++ tailWord_7220012) baseStart_7220012 baseEnd_7220012 := by
    simpa [prefixWord, tailWord_7220012, baseEnd_7220012] using wordTrace_append hprefix tailTrace_7220012
  have hstable : (prefixWord ++ tailWord_7220012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220012).length < 2 ^ (prefixWord ++ tailWord_7220012).sum := by decide
  have hdescent : baseEnd_7220012 < baseStart_7220012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220033 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 7]
def baseStart_7220033 : Nat := 118140960795 + 7220033 * 2 ^ 59
def prefixEnd_7220033 : Nat := 4983230072969 + 3 ^ 40 * 7220033 * 2
def baseEnd_7220033 : Nat := 411927474480383924598131

theorem tailTrace_7220033 : CollatzResearch.WordTrace tailWord_7220033 prefixEnd_7220033 411927474480383924598131 := by
  unfold tailWord_7220033
  simp only [CollatzResearch.WordTrace]
  refine ⟨263336237452060999310720753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175557491634707332873813835 263336237452060999310720753)
  ·
    refine ⟨197502178089045749483040565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263336237452060999310720753 197502178089045749483040565)
    ·
      refine ⟨18515829195848039014035053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197502178089045749483040565 18515829195848039014035053)
      ·
        refine ⟨6943435948443014630263145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18515829195848039014035053 6943435948443014630263145)
        ·
          refine ⟨5207576961332260972697359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943435948443014630263145 5207576961332260972697359)
          ·
            refine ⟨7811365441998391459046039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207576961332260972697359 7811365441998391459046039)
            ·
              refine ⟨11717048162997587188569059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811365441998391459046039 11717048162997587188569059)
              ·
                refine ⟨17575572244496380782853589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11717048162997587188569059 17575572244496380782853589)
                ·
                  refine ⟨411927474480383924598131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17575572244496380782853589 411927474480383924598131)
                  ·
                    rfl

theorem cell23_7220033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 7].length) (baseStart_7220033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220033 prefixEnd_7220033 := by exact prefixLift 7220033
  have htrace : WordTrace (prefixWord ++ tailWord_7220033) baseStart_7220033 baseEnd_7220033 := by
    simpa [prefixWord, tailWord_7220033, baseEnd_7220033] using wordTrace_append hprefix tailTrace_7220033
  have hstable : (prefixWord ++ tailWord_7220033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220033).length < 2 ^ (prefixWord ++ tailWord_7220033).sum := by decide
  have hdescent : baseEnd_7220033 < baseStart_7220033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220069 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_7220069 : Nat := 118140960795 + 7220069 * 2 ^ 59
def prefixEnd_7220069 : Nat := 4983230072969 + 3 ^ 40 * 7220069 * 2
def baseEnd_7220069 : Nat := 3707365755627017180533013

theorem tailTrace_7220069 : CollatzResearch.WordTrace tailWord_7220069 prefixEnd_7220069 3707365755627017180533013 := by
  unfold tailWord_7220069
  simp only [CollatzResearch.WordTrace]
  refine ⟨263337550479930577459031261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175558366986620384972687507 263337550479930577459031261)
  ·
    refine ⟨98751581429973966547136723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263337550479930577459031261 98751581429973966547136723)
    ·
      refine ⟨148127372144960949820705085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98751581429973966547136723 148127372144960949820705085)
      ·
        refine ⟨55547764554360356182764407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148127372144960949820705085 55547764554360356182764407)
        ·
          refine ⟨83321646831540534274146611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55547764554360356182764407 83321646831540534274146611)
          ·
            refine ⟨124982470247310801411219917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83321646831540534274146611 124982470247310801411219917)
            ·
              refine ⟨46868426342741550529207469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124982470247310801411219917 46868426342741550529207469)
              ·
                refine ⟨17575659878528081448452801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46868426342741550529207469 17575659878528081448452801)
                ·
                  refine ⟨13181744908896061086339601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17575659878528081448452801 13181744908896061086339601)
                  ·
                    refine ⟨9886308681672045814754701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13181744908896061086339601 9886308681672045814754701)
                    ·
                      refine ⟨3707365755627017180533013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9886308681672045814754701 3707365755627017180533013)
                      ·
                        rfl

theorem cell23_7220069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_7220069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220069 prefixEnd_7220069 := by exact prefixLift 7220069
  have htrace : WordTrace (prefixWord ++ tailWord_7220069) baseStart_7220069 baseEnd_7220069 := by
    simpa [prefixWord, tailWord_7220069, baseEnd_7220069] using wordTrace_append hprefix tailTrace_7220069
  have hstable : (prefixWord ++ tailWord_7220069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220069).length < 2 ^ (prefixWord ++ tailWord_7220069).sum := by decide
  have hdescent : baseEnd_7220069 < baseStart_7220069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220076 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_7220076 : Nat := 118140960795 + 7220076 * 2 ^ 59
def prefixEnd_7220076 : Nat := 4983230072969 + 3 ^ 40 * 7220076 * 2
def baseEnd_7220076 : Nat := 1235789783330532884381827

theorem tailTrace_7220076 : CollatzResearch.WordTrace tailWord_7220076 prefixEnd_7220076 1235789783330532884381827 := by
  unfold tailWord_7220076
  simp only [CollatzResearch.WordTrace]
  refine ⟨131668902895452608827268041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175558537193936811769690721 131668902895452608827268041)
  ·
    refine ⟨98751677171589456620451031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131668902895452608827268041 98751677171589456620451031)
    ·
      refine ⟨148127515757384184930676547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98751677171589456620451031 148127515757384184930676547)
      ·
        refine ⟨222191273636076277396014821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148127515757384184930676547 222191273636076277396014821)
        ·
          refine ⟨41660863806764302011752779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222191273636076277396014821 41660863806764302011752779)
          ·
            refine ⟨62491295710146453017629169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41660863806764302011752779 62491295710146453017629169)
            ·
              refine ⟨46868471782609839763221877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62491295710146453017629169 46868471782609839763221877)
              ·
                refine ⟨4393919229619672477802051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46868471782609839763221877 4393919229619672477802051)
                ·
                  refine ⟨6590878844429508716703077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393919229619672477802051 6590878844429508716703077)
                  ·
                    refine ⟨1235789783330532884381827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590878844429508716703077 1235789783330532884381827)
                    ·
                      rfl

theorem cell23_7220076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_7220076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220076 prefixEnd_7220076 := by exact prefixLift 7220076
  have htrace : WordTrace (prefixWord ++ tailWord_7220076) baseStart_7220076 baseEnd_7220076 := by
    simpa [prefixWord, tailWord_7220076, baseEnd_7220076] using wordTrace_append hprefix tailTrace_7220076
  have hstable : (prefixWord ++ tailWord_7220076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220076).length < 2 ^ (prefixWord ++ tailWord_7220076).sum := by decide
  have hdescent : baseEnd_7220076 < baseStart_7220076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220089 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 6]
def baseStart_7220089 : Nat := 118140960795 + 7220089 * 2 ^ 59
def prefixEnd_7220089 : Nat := 4983230072969 + 3 ^ 40 * 7220089 * 2
def baseEnd_7220089 : Nat := 411930669471123011364769

theorem tailTrace_7220089 : CollatzResearch.WordTrace tailWord_7220089 prefixEnd_7220089 411930669471123011364769 := by
  unfold tailWord_7220089
  simp only [CollatzResearch.WordTrace]
  refine ⟨263338279939858120874759321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175558853293238747249839547 263338279939858120874759321)
  ·
    refine ⟨197503709954893590656069491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263338279939858120874759321 197503709954893590656069491)
    ·
      refine ⟨296255564932340385984104237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197503709954893590656069491 296255564932340385984104237)
      ·
        refine ⟨111095836849627644744039089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296255564932340385984104237 111095836849627644744039089)
        ·
          refine ⟨83321877637220733558029317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111095836849627644744039089 83321877637220733558029317)
          ·
            refine ⟨15622852056978887542130497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83321877637220733558029317 15622852056978887542130497)
            ·
              refine ⟨11717139042734165656597873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15622852056978887542130497 11717139042734165656597873)
              ·
                refine ⟨8787854282050624242448405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11717139042734165656597873 8787854282050624242448405)
                ·
                  refine ⟨411930669471123011364769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8787854282050624242448405 411930669471123011364769)
                  ·
                    rfl

theorem cell23_7220089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_7220089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220089 prefixEnd_7220089 := by exact prefixLift 7220089
  have htrace : WordTrace (prefixWord ++ tailWord_7220089) baseStart_7220089 baseEnd_7220089 := by
    simpa [prefixWord, tailWord_7220089, baseEnd_7220089] using wordTrace_append hprefix tailTrace_7220089
  have hstable : (prefixWord ++ tailWord_7220089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220089).length < 2 ^ (prefixWord ++ tailWord_7220089).sum := by decide
  have hdescent : baseEnd_7220089 < baseStart_7220089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220093 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_7220093 : Nat := 118140960795 + 7220093 * 2 ^ 59
def prefixEnd_7220093 : Nat := 4983230072969 + 3 ^ 40 * 7220093 * 2
def baseEnd_7220093 : Nat := 1235792693054241695544301

theorem tailTrace_7220093 : CollatzResearch.WordTrace tailWord_7220093 prefixEnd_7220093 1235792693054241695544301 := by
  unfold tailWord_7220093
  simp only [CollatzResearch.WordTrace]
  refine ⟨263338425831843629557904933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175558950554562419705269955 263338425831843629557904933)
  ·
    refine ⟨49375954843470680542107175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263338425831843629557904933 49375954843470680542107175)
    ·
      refine ⟨74063932265206020813160763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49375954843470680542107175 74063932265206020813160763)
      ·
        refine ⟨111095898397809031219741145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74063932265206020813160763 111095898397809031219741145)
        ·
          refine ⟨83321923798356773414805859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111095898397809031219741145 83321923798356773414805859)
          ·
            refine ⟨124982885697535160122208789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83321923798356773414805859 124982885697535160122208789)
            ·
              refine ⟨5858572767071960630728537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124982885697535160122208789 5858572767071960630728537)
              ·
                refine ⟨4393929575303970473046403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858572767071960630728537 4393929575303970473046403)
                ·
                  refine ⟨6590894362955955709569605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393929575303970473046403 6590894362955955709569605)
                  ·
                    refine ⟨1235792693054241695544301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590894362955955709569605 1235792693054241695544301)
                    ·
                      rfl

theorem cell23_7220093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_7220093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220093 prefixEnd_7220093 := by exact prefixLift 7220093
  have htrace : WordTrace (prefixWord ++ tailWord_7220093) baseStart_7220093 baseEnd_7220093 := by
    simpa [prefixWord, tailWord_7220093, baseEnd_7220093] using wordTrace_append hprefix tailTrace_7220093
  have hstable : (prefixWord ++ tailWord_7220093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220093).length < 2 ^ (prefixWord ++ tailWord_7220093).sum := by decide
  have hdescent : baseEnd_7220093 < baseStart_7220093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220119 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 1, 5]
def baseStart_7220119 : Nat := 118140960795 + 7220119 * 2 ^ 59
def prefixEnd_7220119 : Nat := 4983230072969 + 3 ^ 40 * 7220119 * 2
def baseEnd_7220119 : Nat := 1235797143219913994969261

theorem tailTrace_7220119 : CollatzResearch.WordTrace tailWord_7220119 prefixEnd_7220119 1235797143219913994969261 := by
  unfold tailWord_7220119
  simp only [CollatzResearch.WordTrace]
  refine ⟨263339374129749435998351411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175559582753166290665567607 263339374129749435998351411)
  ·
    refine ⟨395009061194624153997527117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263339374129749435998351411 395009061194624153997527117)
    ·
      refine ⟨148128397947984057749072669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395009061194624153997527117 148128397947984057749072669)
      ·
        refine ⟨55548149230494021655902251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148128397947984057749072669 55548149230494021655902251)
        ·
          refine ⟨83322223845741032483853377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55548149230494021655902251 83322223845741032483853377)
          ·
            refine ⟨62491667884305774362890033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83322223845741032483853377 62491667884305774362890033)
            ·
              refine ⟨46868750913229330772167525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62491667884305774362890033 46868750913229330772167525)
              ·
                refine ⟨8787890796230499519781411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46868750913229330772167525 8787890796230499519781411)
                ·
                  refine ⟨13181836194345749279672117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8787890796230499519781411 13181836194345749279672117)
                  ·
                    refine ⟨1235797143219913994969261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13181836194345749279672117 1235797143219913994969261)
                    ·
                      rfl

theorem cell23_7220119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_7220119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220119 prefixEnd_7220119 := by exact prefixLift 7220119
  have htrace : WordTrace (prefixWord ++ tailWord_7220119) baseStart_7220119 baseEnd_7220119 := by
    simpa [prefixWord, tailWord_7220119, baseEnd_7220119] using wordTrace_append hprefix tailTrace_7220119
  have hstable : (prefixWord ++ tailWord_7220119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220119).length < 2 ^ (prefixWord ++ tailWord_7220119).sum := by decide
  have hdescent : baseEnd_7220119 < baseStart_7220119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 4]
def baseStart_7220139 : Nat := 118140960795 + 7220139 * 2 ^ 59
def prefixEnd_7220139 : Nat := 4983230072969 + 3 ^ 40 * 7220139 * 2
def baseEnd_7220139 : Nat := 3707401699272831906657691

theorem tailTrace_7220139 : CollatzResearch.WordTrace tailWord_7220139 prefixEnd_7220139 3707401699272831906657691 := by
  unfold tailWord_7220139
  simp only [CollatzResearch.WordTrace]
  refine ⟨263340103589676979414079471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175560069059784652942719647 263340103589676979414079471)
  ·
    refine ⟨395010155384515469121119207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263340103589676979414079471 395010155384515469121119207)
    ·
      refine ⟨592515233076773203681678811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395010155384515469121119207 592515233076773203681678811)
      ·
        refine ⟨888772849615159805522518217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592515233076773203681678811 888772849615159805522518217)
        ·
          refine ⟨666579637211369854141888663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888772849615159805522518217 666579637211369854141888663)
          ·
            refine ⟨999869455817054781212832995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666579637211369854141888663 999869455817054781212832995)
            ·
              refine ⟨1499804183725582171819249493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999869455817054781212832995 1499804183725582171819249493)
              ·
                refine ⟨8787915139017083038003415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1499804183725582171819249493 8787915139017083038003415)
                ·
                  refine ⟨13181872708525624557005123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8787915139017083038003415 13181872708525624557005123)
                  ·
                    refine ⟨19772809062788436835507685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13181872708525624557005123 19772809062788436835507685)
                    ·
                      refine ⟨3707401699272831906657691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19772809062788436835507685 3707401699272831906657691)
                      ·
                        rfl

theorem cell23_7220139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 4].length) (baseStart_7220139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220139 prefixEnd_7220139 := by exact prefixLift 7220139
  have htrace : WordTrace (prefixWord ++ tailWord_7220139) baseStart_7220139 baseEnd_7220139 := by
    simpa [prefixWord, tailWord_7220139, baseEnd_7220139] using wordTrace_append hprefix tailTrace_7220139
  have hstable : (prefixWord ++ tailWord_7220139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220139).length < 2 ^ (prefixWord ++ tailWord_7220139).sum := by decide
  have hdescent : baseEnd_7220139 < baseStart_7220139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220159 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_7220159 : Nat := 118140960795 + 7220159 * 2 ^ 59
def prefixEnd_7220159 : Nat := 4983230072969 + 3 ^ 40 * 7220159 * 2
def baseEnd_7220159 : Nat := 3707411968885921828407599

theorem tailTrace_7220159 : CollatzResearch.WordTrace tailWord_7220159 prefixEnd_7220159 3707411968885921828407599 := by
  unfold tailWord_7220159
  simp only [CollatzResearch.WordTrace]
  refine ⟨263340833049604522829807531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175560555366403015219871687 263340833049604522829807531)
  ·
    refine ⟨395011249574406784244711297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263340833049604522829807531 395011249574406784244711297)
    ·
      refine ⟨296258437180805088183533473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395011249574406784244711297 296258437180805088183533473)
      ·
        refine ⟨222193827885603816137650105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296258437180805088183533473 222193827885603816137650105)
        ·
          refine ⟨166645370914202862103237579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222193827885603816137650105 166645370914202862103237579)
          ·
            refine ⟨249968056371304293154856369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166645370914202862103237579 249968056371304293154856369)
            ·
              refine ⟨187476042278478219866142277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249968056371304293154856369 187476042278478219866142277)
              ·
                refine ⟨35151757927214666224901677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187476042278478219866142277 35151757927214666224901677)
                ·
                  refine ⟨13181909222705499834338129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35151757927214666224901677 13181909222705499834338129)
                  ·
                    refine ⟨9886431917029124875753597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13181909222705499834338129 9886431917029124875753597)
                    ·
                      refine ⟨3707411968885921828407599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9886431917029124875753597 3707411968885921828407599)
                      ·
                        rfl

theorem cell23_7220159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_7220159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220159 prefixEnd_7220159 := by exact prefixLift 7220159
  have htrace : WordTrace (prefixWord ++ tailWord_7220159) baseStart_7220159 baseEnd_7220159 := by
    simpa [prefixWord, tailWord_7220159, baseEnd_7220159] using wordTrace_append hprefix tailTrace_7220159
  have hstable : (prefixWord ++ tailWord_7220159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220159).length < 2 ^ (prefixWord ++ tailWord_7220159).sum := by decide
  have hdescent : baseEnd_7220159 < baseStart_7220159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220192 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_7220192 : Nat := 118140960795 + 7220192 * 2 ^ 59
def prefixEnd_7220192 : Nat := 4983230072969 + 3 ^ 40 * 7220192 * 2
def baseEnd_7220192 : Nat := 1235809637915840066431649

theorem tailTrace_7220192 : CollatzResearch.WordTrace tailWord_7220192 prefixEnd_7220192 1235809637915840066431649 := by
  unfold tailWord_7220192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131671018329242484732879415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175561357772323312977172553 131671018329242484732879415)
  ·
    refine ⟨197506527493863727099319123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131671018329242484732879415 197506527493863727099319123)
    ·
      refine ⟨296259791240795590648978685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197506527493863727099319123 296259791240795590648978685)
      ·
        refine ⟨111097421715298346493367007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296259791240795590648978685 111097421715298346493367007)
        ·
          refine ⟨166646132572947519740050511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111097421715298346493367007 166646132572947519740050511)
          ·
            refine ⟨249969198859421279610075767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166646132572947519740050511 249969198859421279610075767)
            ·
              refine ⟨374953798289131919415113651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249969198859421279610075767 374953798289131919415113651)
              ·
                refine ⟨562430697433697879122670477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374953798289131919415113651 562430697433697879122670477)
                ·
                  refine ⟨210911511537636704671001429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562430697433697879122670477 210911511537636704671001429)
                  ·
                    refine ⟨1235809637915840066431649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210911511537636704671001429 1235809637915840066431649)
                    ·
                      rfl

theorem cell23_7220192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_7220192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220192 prefixEnd_7220192 := by exact prefixLift 7220192
  have htrace : WordTrace (prefixWord ++ tailWord_7220192) baseStart_7220192 baseEnd_7220192 := by
    simpa [prefixWord, tailWord_7220192, baseEnd_7220192] using wordTrace_append hprefix tailTrace_7220192
  have hstable : (prefixWord ++ tailWord_7220192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220192).length < 2 ^ (prefixWord ++ tailWord_7220192).sum := by decide
  have hdescent : baseEnd_7220192 < baseStart_7220192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220207 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 1, 2, 2]
def baseStart_7220207 : Nat := 118140960795 + 7220207 * 2 ^ 59
def prefixEnd_7220207 : Nat := 4983230072969 + 3 ^ 40 * 7220207 * 2
def baseEnd_7220207 : Nat := 3707436615957337640607379

theorem tailTrace_7220207 : CollatzResearch.WordTrace tailWord_7220207 prefixEnd_7220207 3707436615957337640607379 := by
  unfold tailWord_7220207
  simp only [CollatzResearch.WordTrace]
  refine ⟨263342583753430627027554875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175561722502287084685036583 263342583753430627027554875)
  ·
    refine ⟨395013875630145940541332313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263342583753430627027554875 395013875630145940541332313)
    ·
      refine ⟨296260406722609455405999235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395013875630145940541332313 296260406722609455405999235)
      ·
        refine ⟨444390610083914183108998853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296260406722609455405999235 444390610083914183108998853)
        ·
          refine ⟨83323239390733909332937285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444390610083914183108998853 83323239390733909332937285)
          ·
            refine ⟨15623107385762607999925741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83323239390733909332937285 15623107385762607999925741)
            ·
              refine ⟨5858665269660977999972153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15623107385762607999925741 5858665269660977999972153)
              ·
                refine ⟨4393998952245733499979115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858665269660977999972153 4393998952245733499979115)
                ·
                  refine ⟨6590998428368600249968673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393998952245733499979115 6590998428368600249968673)
                  ·
                    refine ⟨4943248821276450187476505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6590998428368600249968673 4943248821276450187476505)
                    ·
                      refine ⟨3707436615957337640607379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943248821276450187476505 3707436615957337640607379)
                      ·
                        rfl

theorem cell23_7220207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 2, 2].length) (baseStart_7220207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220207 prefixEnd_7220207 := by exact prefixLift 7220207
  have htrace : WordTrace (prefixWord ++ tailWord_7220207) baseStart_7220207 baseEnd_7220207 := by
    simpa [prefixWord, tailWord_7220207, baseEnd_7220207] using wordTrace_append hprefix tailTrace_7220207
  have hstable : (prefixWord ++ tailWord_7220207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220207).length < 2 ^ (prefixWord ++ tailWord_7220207).sum := by decide
  have hdescent : baseEnd_7220207 < baseStart_7220207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220213 : List Nat := [1, 3, 5, 2, 1, 1, 2, 8]
def baseStart_7220213 : Nat := 118140960795 + 7220213 * 2 ^ 59
def prefixEnd_7220213 : Nat := 4983230072969 + 3 ^ 40 * 7220213 * 2
def baseEnd_7220213 : Nat := 137312581364491282116013

theorem tailTrace_7220213 : CollatzResearch.WordTrace tailWord_7220213 prefixEnd_7220213 137312581364491282116013 := by
  unfold tailWord_7220213
  simp only [CollatzResearch.WordTrace]
  refine ⟨263342802591408890052273293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175561868394272593368182195 263342802591408890052273293)
  ·
    refine ⟨98753550971778333769602485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263342802591408890052273293 98753550971778333769602485)
    ·
      refine ⟨9258145403604218790900233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98753550971778333769602485 9258145403604218790900233)
      ·
        refine ⟨6943609052703164093175175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9258145403604218790900233 6943609052703164093175175)
        ·
          refine ⟨10415413579054746139762763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6943609052703164093175175 10415413579054746139762763)
          ·
            refine ⟨15623120368582119209644145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10415413579054746139762763 15623120368582119209644145)
            ·
              refine ⟨11717340276436589407233109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15623120368582119209644145 11717340276436589407233109)
              ·
                refine ⟨137312581364491282116013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11717340276436589407233109 137312581364491282116013)
                ·
                  rfl

theorem cell23_7220213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 8].length) (baseStart_7220213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220213 prefixEnd_7220213 := by exact prefixLift 7220213
  have htrace : WordTrace (prefixWord ++ tailWord_7220213) baseStart_7220213 baseEnd_7220213 := by
    simpa [prefixWord, tailWord_7220213, baseEnd_7220213] using wordTrace_append hprefix tailTrace_7220213
  have hstable : (prefixWord ++ tailWord_7220213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220213).length < 2 ^ (prefixWord ++ tailWord_7220213).sum := by decide
  have hdescent : baseEnd_7220213 < baseStart_7220213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220216 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 3, 3, 2]
def baseStart_7220216 : Nat := 118140960795 + 7220216 * 2 ^ 59
def prefixEnd_7220216 : Nat := 4983230072969 + 3 ^ 40 * 7220216 * 2
def baseEnd_7220216 : Nat := 3707441237283228105394837

theorem tailTrace_7220216 : CollatzResearch.WordTrace tailWord_7220216 prefixEnd_7220216 3707441237283228105394837 := by
  unfold tailWord_7220216
  simp only [CollatzResearch.WordTrace]
  refine ⟨131671456005199010782316251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175561941340265347709755001 131671456005199010782316251)
  ·
    refine ⟨197507184007798516173474377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131671456005199010782316251 197507184007798516173474377)
    ·
      refine ⟨148130388005848887130105783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197507184007798516173474377 148130388005848887130105783)
      ·
        refine ⟨222195582008773330695158675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148130388005848887130105783 222195582008773330695158675)
        ·
          refine ⟨333293373013159996042738013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222195582008773330695158675 333293373013159996042738013)
          ·
            refine ⟨124985014879934998516026755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333293373013159996042738013 124985014879934998516026755)
            ·
              refine ⟨187477522319902497774040133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124985014879934998516026755 187477522319902497774040133)
              ·
                refine ⟨35152035434981718332632525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187477522319902497774040133 35152035434981718332632525)
                ·
                  refine ⟨13182013288118144374737197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35152035434981718332632525 13182013288118144374737197)
                  ·
                    refine ⟨4943254983044304140526449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13182013288118144374737197 4943254983044304140526449)
                    ·
                      refine ⟨3707441237283228105394837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943254983044304140526449 3707441237283228105394837)
                      ·
                        rfl

theorem cell23_7220216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_7220216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220216 prefixEnd_7220216 := by exact prefixLift 7220216
  have htrace : WordTrace (prefixWord ++ tailWord_7220216) baseStart_7220216 baseEnd_7220216 := by
    simpa [prefixWord, tailWord_7220216, baseEnd_7220216] using wordTrace_append hprefix tailTrace_7220216
  have hstable : (prefixWord ++ tailWord_7220216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220216).length < 2 ^ (prefixWord ++ tailWord_7220216).sum := by decide
  have hdescent : baseEnd_7220216 < baseStart_7220216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220249 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_7220249 : Nat := 118140960795 + 7220249 * 2 ^ 59
def prefixEnd_7220249 : Nat := 4983230072969 + 3 ^ 40 * 7220249 * 2
def baseEnd_7220249 : Nat := 3707458182144826476282185

theorem tailTrace_7220249 : CollatzResearch.WordTrace tailWord_7220249 prefixEnd_7220249 3707458182144826476282185 := by
  unfold tailWord_7220249
  simp only [CollatzResearch.WordTrace]
  refine ⟨263344115619278468200583801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175562743746185645467055867 263344115619278468200583801)
  ·
    refine ⟨197508086714458851150437851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263344115619278468200583801 197508086714458851150437851)
    ·
      refine ⟨296262130071688276725656777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197508086714458851150437851 296262130071688276725656777)
      ·
        refine ⟨222196597553766207544242583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296262130071688276725656777 222196597553766207544242583)
        ·
          refine ⟨333294896330649311316363875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222196597553766207544242583 333294896330649311316363875)
          ·
            refine ⟨499942344495973966974545813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333294896330649311316363875 499942344495973966974545813)
            ·
              refine ⟨23434797398248779701931835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 499942344495973966974545813 23434797398248779701931835)
              ·
                refine ⟨35152196097373169552897753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23434797398248779701931835 35152196097373169552897753)
                ·
                  refine ⟨26364147073029877164673315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35152196097373169552897753 26364147073029877164673315)
                  ·
                    refine ⟨39546220609544815747009973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26364147073029877164673315 39546220609544815747009973)
                    ·
                      refine ⟨3707458182144826476282185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39546220609544815747009973 3707458182144826476282185)
                      ·
                        rfl

theorem cell23_7220249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_7220249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220249 prefixEnd_7220249 := by exact prefixLift 7220249
  have htrace : WordTrace (prefixWord ++ tailWord_7220249) baseStart_7220249 baseEnd_7220249 := by
    simpa [prefixWord, tailWord_7220249, baseEnd_7220249] using wordTrace_append hprefix tailTrace_7220249
  have hstable : (prefixWord ++ tailWord_7220249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220249).length < 2 ^ (prefixWord ++ tailWord_7220249).sum := by decide
  have hdescent : baseEnd_7220249 < baseStart_7220249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220250 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2]
def baseStart_7220250 : Nat := 118140960795 + 7220250 * 2 ^ 59
def prefixEnd_7220250 : Nat := 4983230072969 + 3 ^ 40 * 7220250 * 2
def baseEnd_7220250 : Nat := 3707458695625480972369681

theorem tailTrace_7220250 : CollatzResearch.WordTrace tailWord_7220250 prefixEnd_7220250 3707458695625480972369681 := by
  unfold tailWord_7220250
  simp only [CollatzResearch.WordTrace]
  refine ⟨65836038023068711342842551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175562768061516563580913469 65836038023068711342842551)
  ·
    refine ⟨98754057034603067014263827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65836038023068711342842551 98754057034603067014263827)
    ·
      refine ⟨148131085551904600521395741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98754057034603067014263827 148131085551904600521395741)
      ·
        refine ⟨55549157081964225195523403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148131085551904600521395741 55549157081964225195523403)
        ·
          refine ⟨83323735622946337793285105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55549157081964225195523403 83323735622946337793285105)
          ·
            refine ⟨62492801717209753344963829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83323735622946337793285105 62492801717209753344963829)
            ·
              refine ⟨5858700160988414376090359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62492801717209753344963829 5858700160988414376090359)
              ·
                refine ⟨8788050241482621564135539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858700160988414376090359 8788050241482621564135539)
                ·
                  refine ⟨13182075362223932346203309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8788050241482621564135539 13182075362223932346203309)
                  ·
                    refine ⟨4943278260833974629826241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13182075362223932346203309 4943278260833974629826241)
                    ·
                      refine ⟨3707458695625480972369681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943278260833974629826241 3707458695625480972369681)
                      ·
                        rfl

theorem cell23_7220250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_7220250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220250 prefixEnd_7220250 := by exact prefixLift 7220250
  have htrace : WordTrace (prefixWord ++ tailWord_7220250) baseStart_7220250 baseEnd_7220250 := by
    simpa [prefixWord, tailWord_7220250, baseEnd_7220250] using wordTrace_append hprefix tailTrace_7220250
  have hstable : (prefixWord ++ tailWord_7220250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220250).length < 2 ^ (prefixWord ++ tailWord_7220250).sum := by decide
  have hdescent : baseEnd_7220250 < baseStart_7220250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220280 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 2, 2, 2]
def baseStart_7220280 : Nat := 118140960795 + 7220280 * 2 ^ 59
def prefixEnd_7220280 : Nat := 4983230072969 + 3 ^ 40 * 7220280 * 2
def baseEnd_7220280 : Nat := 3707474100045115854994543

theorem tailTrace_7220280 : CollatzResearch.WordTrace tailWord_7220280 prefixEnd_7220280 3707474100045115854994543 := by
  unfold tailWord_7220280
  simp only [CollatzResearch.WordTrace]
  refine ⟨131672623141083080247481147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175563497521444106996641529 131672623141083080247481147)
  ·
    refine ⟨197508934711624620371221721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131672623141083080247481147 197508934711624620371221721)
    ·
      refine ⟨148131701033718465278416291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197508934711624620371221721 148131701033718465278416291)
      ·
        refine ⟨222197551550577697917624437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148131701033718465278416291 222197551550577697917624437)
        ·
          refine ⟨20831020457866659179777291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222197551550577697917624437 20831020457866659179777291)
          ·
            refine ⟨31246530686799988769665937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20831020457866659179777291 31246530686799988769665937)
            ·
              refine ⟨23434898015099991577249453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31246530686799988769665937 23434898015099991577249453)
              ·
                refine ⟨8788086755662496841468545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23434898015099991577249453 8788086755662496841468545)
                ·
                  refine ⟨6591065066746872631101409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8788086755662496841468545 6591065066746872631101409)
                  ·
                    refine ⟨4943298800060154473326057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6591065066746872631101409 4943298800060154473326057)
                    ·
                      refine ⟨3707474100045115854994543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943298800060154473326057 3707474100045115854994543)
                      ·
                        rfl

theorem cell23_7220280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_7220280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220280 prefixEnd_7220280 := by exact prefixLift 7220280
  have htrace : WordTrace (prefixWord ++ tailWord_7220280) baseStart_7220280 baseEnd_7220280 := by
    simpa [prefixWord, tailWord_7220280, baseEnd_7220280] using wordTrace_append hprefix tailTrace_7220280
  have hstable : (prefixWord ++ tailWord_7220280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220280).length < 2 ^ (prefixWord ++ tailWord_7220280).sum := by decide
  have hdescent : baseEnd_7220280 < baseStart_7220280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220286 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_7220286 : Nat := 118140960795 + 7220286 * 2 ^ 59
def prefixEnd_7220286 : Nat := 4983230072969 + 3 ^ 40 * 7220286 * 2
def baseEnd_7220286 : Nat := 411941908992115870168835

theorem tailTrace_7220286 : CollatzResearch.WordTrace tailWord_7220286 prefixEnd_7220286 411941908992115870168835 := by
  unfold tailWord_7220286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32918183140018052939960089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175563643413429615679787141 32918183140018052939960089)
  ·
    refine ⟨24688637355013539704970067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32918183140018052939960089 24688637355013539704970067)
    ·
      refine ⟨37032956032520309557455101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24688637355013539704970067 37032956032520309557455101)
      ·
        refine ⟨13887358512195116084045663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37032956032520309557455101 13887358512195116084045663)
        ·
          refine ⟨20831037768292674126068495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13887358512195116084045663 20831037768292674126068495)
          ·
            refine ⟨31246556652439011189102743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20831037768292674126068495 31246556652439011189102743)
            ·
              refine ⟨46869834978658516783654115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31246556652439011189102743 46869834978658516783654115)
              ·
                refine ⟨70304752467987775175481173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46869834978658516783654115 70304752467987775175481173)
                ·
                  refine ⟨411941908992115870168835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70304752467987775175481173 411941908992115870168835)
                  ·
                    rfl

theorem cell23_7220286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_7220286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220286 prefixEnd_7220286 := by exact prefixLift 7220286
  have htrace : WordTrace (prefixWord ++ tailWord_7220286) baseStart_7220286 baseEnd_7220286 := by
    simpa [prefixWord, tailWord_7220286, baseEnd_7220286] using wordTrace_append hprefix tailTrace_7220286
  have hstable : (prefixWord ++ tailWord_7220286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220286).length < 2 ^ (prefixWord ++ tailWord_7220286).sum := by decide
  have hdescent : baseEnd_7220286 < baseStart_7220286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220316 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7220316 : Nat := 118140960795 + 7220316 * 2 ^ 59
def prefixEnd_7220316 : Nat := 4983230072969 + 3 ^ 40 * 7220316 * 2
def baseEnd_7220316 : Nat := 1235830861782892571381459

theorem tailTrace_7220316 : CollatzResearch.WordTrace tailWord_7220316 prefixEnd_7220316 1235830861782892571381459 := by
  unfold tailWord_7220316
  simp only [CollatzResearch.WordTrace]
  refine ⟨131673279655017869321636401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175564372873357159095515201 131673279655017869321636401)
  ·
    refine ⟨98754959741263401991227301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131673279655017869321636401 98754959741263401991227301)
    ·
      refine ⟨18516554951486887873355119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98754959741263401991227301 18516554951486887873355119)
      ·
        refine ⟨27774832427230331810032679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18516554951486887873355119 27774832427230331810032679)
        ·
          refine ⟨41662248640845497715049019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27774832427230331810032679 41662248640845497715049019)
          ·
            refine ⟨62493372961268246572573529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41662248640845497715049019 62493372961268246572573529)
            ·
              refine ⟨46870029720951184929430147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62493372961268246572573529 46870029720951184929430147)
              ·
                refine ⟨70305044581426777394145221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46870029720951184929430147 70305044581426777394145221)
                ·
                  refine ⟨13182195859017520761402229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70305044581426777394145221 13182195859017520761402229)
                  ·
                    refine ⟨1235830861782892571381459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13182195859017520761402229 1235830861782892571381459)
                    ·
                      rfl

theorem cell23_7220316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7220316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220316 prefixEnd_7220316 := by exact prefixLift 7220316
  have htrace : WordTrace (prefixWord ++ tailWord_7220316) baseStart_7220316 baseEnd_7220316 := by
    simpa [prefixWord, tailWord_7220316, baseEnd_7220316] using wordTrace_append hprefix tailTrace_7220316
  have hstable : (prefixWord ++ tailWord_7220316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220316).length < 2 ^ (prefixWord ++ tailWord_7220316).sum := by decide
  have hdescent : baseEnd_7220316 < baseStart_7220316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220376 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 8]
def baseStart_7220376 : Nat := 118140960795 + 7220376 * 2 ^ 59
def prefixEnd_7220376 : Nat := 4983230072969 + 3 ^ 40 * 7220376 * 2
def baseEnd_7220376 : Nat := 411947043798660831043789

theorem tailTrace_7220376 : CollatzResearch.WordTrace tailWord_7220376 prefixEnd_7220376 411947043798660831043789 := by
  unfold tailWord_7220376
  simp only [CollatzResearch.WordTrace]
  refine ⟨131674373844909184445228491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175565831793212245926971321 131674373844909184445228491)
  ·
    refine ⟨197511560767363776667842737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131674373844909184445228491 197511560767363776667842737)
    ·
      refine ⟨148133670575522832500882053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197511560767363776667842737 148133670575522832500882053)
      ·
        refine ⟨27775063232910531093915385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148133670575522832500882053 27775063232910531093915385)
        ·
          refine ⟨20831297424682898320436539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27775063232910531093915385 20831297424682898320436539)
          ·
            refine ⟨31246946137024347480654809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20831297424682898320436539 31246946137024347480654809)
            ·
              refine ⟨23435209602768260610491107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31246946137024347480654809 23435209602768260610491107)
              ·
                refine ⟨35152814404152390915736661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23435209602768260610491107 35152814404152390915736661)
                ·
                  refine ⟨411947043798660831043789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35152814404152390915736661 411947043798660831043789)
                  ·
                    rfl

theorem cell23_7220376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_7220376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220376 prefixEnd_7220376 := by exact prefixLift 7220376
  have htrace : WordTrace (prefixWord ++ tailWord_7220376) baseStart_7220376 baseEnd_7220376 := by
    simpa [prefixWord, tailWord_7220376, baseEnd_7220376] using wordTrace_append hprefix tailTrace_7220376
  have hstable : (prefixWord ++ tailWord_7220376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220376).length < 2 ^ (prefixWord ++ tailWord_7220376).sum := by decide
  have hdescent : baseEnd_7220376 < baseStart_7220376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220380 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_7220380 : Nat := 118140960795 + 7220380 * 2 ^ 59
def prefixEnd_7220380 : Nat := 4983230072969 + 3 ^ 40 * 7220380 * 2
def baseEnd_7220380 : Nat := 1235841816036855154581361

theorem tailTrace_7220380 : CollatzResearch.WordTrace tailWord_7220380 prefixEnd_7220380 1235841816036855154581361 := by
  unfold tailWord_7220380
  simp only [CollatzResearch.WordTrace]
  refine ⟨131674446790901938786801297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175565929054535918382401729 131674446790901938786801297)
  ·
    refine ⟨98755835093176454090100973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131674446790901938786801297 98755835093176454090100973)
    ·
      refine ⟨37033438159941170283787865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98755835093176454090100973 37033438159941170283787865)
      ·
        refine ⟨27775078619955877712840899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37033438159941170283787865 27775078619955877712840899)
        ·
          refine ⟨41662617929933816569261349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27775078619955877712840899 41662617929933816569261349)
          ·
            refine ⟨7811740861862590606736503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41662617929933816569261349 7811740861862590606736503)
            ·
              refine ⟨11717611292793885910104755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811740861862590606736503 11717611292793885910104755)
              ·
                refine ⟨17576416939190828865157133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11717611292793885910104755 17576416939190828865157133)
                ·
                  refine ⟨6591156352196560824433925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17576416939190828865157133 6591156352196560824433925)
                  ·
                    refine ⟨1235841816036855154581361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6591156352196560824433925 1235841816036855154581361)
                    ·
                      rfl

theorem cell23_7220380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_7220380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220380 prefixEnd_7220380 := by exact prefixLift 7220380
  have htrace : WordTrace (prefixWord ++ tailWord_7220380) baseStart_7220380 baseEnd_7220380 := by
    simpa [prefixWord, tailWord_7220380, baseEnd_7220380] using wordTrace_append hprefix tailTrace_7220380
  have hstable : (prefixWord ++ tailWord_7220380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220380).length < 2 ^ (prefixWord ++ tailWord_7220380).sum := by decide
  have hdescent : baseEnd_7220380 < baseStart_7220380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220403 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 3]
def baseStart_7220403 : Nat := 118140960795 + 7220403 * 2 ^ 59
def prefixEnd_7220403 : Nat := 4983230072969 + 3 ^ 40 * 7220403 * 2
def baseEnd_7220403 : Nat := 3707537258165618873756477

theorem tailTrace_7220403 : CollatzResearch.WordTrace tailWord_7220403 prefixEnd_7220403 3707537258165618873756477 := by
  unfold tailWord_7220403
  simp only [CollatzResearch.WordTrace]
  refine ⟨263349732460720552501689863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175566488307147035001126575 263349732460720552501689863)
  ·
    refine ⟨395024598691080828752534795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263349732460720552501689863 395024598691080828752534795)
    ·
      refine ⟨592536898036621243128802193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395024598691080828752534795 592536898036621243128802193)
      ·
        refine ⟨444402673527465932346601645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592536898036621243128802193 444402673527465932346601645)
        ·
          refine ⟨166651002572799724629975617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444402673527465932346601645 166651002572799724629975617)
          ·
            refine ⟨124988251929599793472481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166651002572799724629975617 124988251929599793472481713)
            ·
              refine ⟨93741188947199845104361285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124988251929599793472481713 93741188947199845104361285)
              ·
                refine ⟨17576472927599970957067741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93741188947199845104361285 17576472927599970957067741)
                ·
                  refine ⟨6591177347849989108900403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17576472927599970957067741 6591177347849989108900403)
                  ·
                    refine ⟨9886766021774983663350605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6591177347849989108900403 9886766021774983663350605)
                    ·
                      refine ⟨3707537258165618873756477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9886766021774983663350605 3707537258165618873756477)
                      ·
                        rfl

theorem cell23_7220403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_7220403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220403 prefixEnd_7220403 := by exact prefixLift 7220403
  have htrace : WordTrace (prefixWord ++ tailWord_7220403) baseStart_7220403 baseEnd_7220403 := by
    simpa [prefixWord, tailWord_7220403, baseEnd_7220403] using wordTrace_append hprefix tailTrace_7220403
  have hstable : (prefixWord ++ tailWord_7220403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220403).length < 2 ^ (prefixWord ++ tailWord_7220403).sum := by decide
  have hdescent : baseEnd_7220403 < baseStart_7220403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220413 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_7220413 : Nat := 118140960795 + 7220413 * 2 ^ 59
def prefixEnd_7220413 : Nat := 4983230072969 + 3 ^ 40 * 7220413 * 2
def baseEnd_7220413 : Nat := 3707542392972163834631431

theorem tailTrace_7220413 : CollatzResearch.WordTrace tailWord_7220413 prefixEnd_7220413 3707542392972163834631431 := by
  unfold tailWord_7220413
  simp only [CollatzResearch.WordTrace]
  refine ⟨263350097190684324209553893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175566731460456216139702595 263350097190684324209553893)
  ·
    refine ⟨49378143223253310789291355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263350097190684324209553893 49378143223253310789291355)
    ·
      refine ⟨74067214834879966183937033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49378143223253310789291355 74067214834879966183937033)
      ·
        refine ⟨55550411126159974637952775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74067214834879966183937033 55550411126159974637952775)
        ·
          refine ⟨83325616689239961956929163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55550411126159974637952775 83325616689239961956929163)
          ·
            refine ⟨124988425033859942935393745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83325616689239961956929163 124988425033859942935393745)
            ·
              refine ⟨93741318775394957201545309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124988425033859942935393745 93741318775394957201545309)
              ·
                refine ⟨35152994540773108950579491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93741318775394957201545309 35152994540773108950579491)
                ·
                  refine ⟨52729491811159663425869237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35152994540773108950579491 52729491811159663425869237)
                  ·
                    refine ⟨4943389857296218446175241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52729491811159663425869237 4943389857296218446175241)
                    ·
                      refine ⟨3707542392972163834631431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943389857296218446175241 3707542392972163834631431)
                      ·
                        rfl

theorem cell23_7220413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_7220413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220413 prefixEnd_7220413 := by exact prefixLift 7220413
  have htrace : WordTrace (prefixWord ++ tailWord_7220413) baseStart_7220413 baseEnd_7220413 := by
    simpa [prefixWord, tailWord_7220413, baseEnd_7220413] using wordTrace_append hprefix tailTrace_7220413
  have hstable : (prefixWord ++ tailWord_7220413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220413).length < 2 ^ (prefixWord ++ tailWord_7220413).sum := by decide
  have hdescent : baseEnd_7220413 < baseStart_7220413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220460 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 5, 2, 2]
def baseStart_7220460 : Nat := 118140960795 + 7220460 * 2 ^ 59
def prefixEnd_7220460 : Nat := 4983230072969 + 3 ^ 40 * 7220460 * 2
def baseEnd_7220460 : Nat := 3707566526562925150743715

theorem tailTrace_7220460 : CollatzResearch.WordTrace tailWord_7220460 prefixEnd_7220460 3707566526562925150743715 := by
  unfold tailWord_7220460
  simp only [CollatzResearch.WordTrace]
  refine ⟨131675905710757025618257417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175567874281009367491009889 131675905710757025618257417)
  ·
    refine ⟨98756929283067769213693063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131675905710757025618257417 98756929283067769213693063)
    ·
      refine ⟨148135393924601653820539595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98756929283067769213693063 148135393924601653820539595)
      ·
        refine ⟨222203090886902480730809393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148135393924601653820539595 222203090886902480730809393)
        ·
          refine ⟨166652318165176860548107045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222203090886902480730809393 166652318165176860548107045)
          ·
            refine ⟨31247309655970661352770071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166652318165176860548107045 31247309655970661352770071)
            ·
              refine ⟨46870964483955992029155107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31247309655970661352770071 46870964483955992029155107)
              ·
                refine ⟨70306446725933988043732661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46870964483955992029155107 70306446725933988043732661)
                ·
                  refine ⟨6591229380556311379099937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70306446725933988043732661 6591229380556311379099937)
                  ·
                    refine ⟨4943422035417233534324953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6591229380556311379099937 4943422035417233534324953)
                    ·
                      refine ⟨3707566526562925150743715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943422035417233534324953 3707566526562925150743715)
                      ·
                        rfl

theorem cell23_7220460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_7220460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220460 prefixEnd_7220460 := by exact prefixLift 7220460
  have htrace : WordTrace (prefixWord ++ tailWord_7220460) baseStart_7220460 baseEnd_7220460 := by
    simpa [prefixWord, tailWord_7220460, baseEnd_7220460] using wordTrace_append hprefix tailTrace_7220460
  have hstable : (prefixWord ++ tailWord_7220460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220460).length < 2 ^ (prefixWord ++ tailWord_7220460).sum := by decide
  have hdescent : baseEnd_7220460 < baseStart_7220460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220494 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_7220494 : Nat := 118140960795 + 7220494 * 2 ^ 59
def prefixEnd_7220494 : Nat := 4983230072969 + 3 ^ 40 * 7220494 * 2
def baseEnd_7220494 : Nat := 3707583984905178017718559

theorem tailTrace_7220494 : CollatzResearch.WordTrace tailWord_7220494 prefixEnd_7220494 3707583984905178017718559 := by
  unfold tailWord_7220494
  simp only [CollatzResearch.WordTrace]
  refine ⟨32919131437923859380406567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175568701002260583362168357 32919131437923859380406567)
  ·
    refine ⟨49378697156885789070609851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32919131437923859380406567 49378697156885789070609851)
    ·
      refine ⟨74068045735328683605914777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49378697156885789070609851 74068045735328683605914777)
      ·
        refine ⟨55551034301496512704436083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74068045735328683605914777 55551034301496512704436083)
        ·
          refine ⟨83326551452244769056654125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55551034301496512704436083 83326551452244769056654125)
          ·
            refine ⟨31247456794591788396245297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83326551452244769056654125 31247456794591788396245297)
            ·
              refine ⟨23435592595943841297183973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31247456794591788396245297 23435592595943841297183973)
              ·
                refine ⟨4394173611739470243221995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23435592595943841297183973 4394173611739470243221995)
                ·
                  refine ⟨6591260417609205364832993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394173611739470243221995 6591260417609205364832993)
                  ·
                    refine ⟨4943445313206904023624745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6591260417609205364832993 4943445313206904023624745)
                    ·
                      refine ⟨3707583984905178017718559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943445313206904023624745 3707583984905178017718559)
                      ·
                        rfl

theorem cell23_7220494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_7220494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220494 prefixEnd_7220494 := by exact prefixLift 7220494
  have htrace : WordTrace (prefixWord ++ tailWord_7220494) baseStart_7220494 baseEnd_7220494 := by
    simpa [prefixWord, tailWord_7220494, baseEnd_7220494] using wordTrace_append hprefix tailTrace_7220494
  have hstable : (prefixWord ++ tailWord_7220494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220494).length < 2 ^ (prefixWord ++ tailWord_7220494).sum := by decide
  have hdescent : baseEnd_7220494 < baseStart_7220494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220603 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 2, 5]
def baseStart_7220603 : Nat := 118140960795 + 7220603 * 2 ^ 59
def prefixEnd_7220603 : Nat := 4983230072969 + 3 ^ 40 * 7220603 * 2
def baseEnd_7220603 : Nat := 1235879984765506030418519

theorem tailTrace_7220603 : CollatzResearch.WordTrace tailWord_7220603 prefixEnd_7220603 1235879984765506030418519 := by
  unfold tailWord_7220603
  simp only [CollatzResearch.WordTrace]
  refine ⟨263357027059995986658970463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175571351373330657772646975 263357027059995986658970463)
  ·
    refine ⟨395035540589993979988455695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263357027059995986658970463 395035540589993979988455695)
    ·
      refine ⟨592553310884990969982683543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395035540589993979988455695 592553310884990969982683543)
      ·
        refine ⟨888829966327486454974025315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592553310884990969982683543 888829966327486454974025315)
        ·
          refine ⟨1333244949491229682461037973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888829966327486454974025315 1333244949491229682461037973)
          ·
            refine ⟨62495857007401391365361155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1333244949491229682461037973 62495857007401391365361155)
            ·
              refine ⟨93743785511102087048041733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62495857007401391365361155 93743785511102087048041733)
              ·
                refine ⟨17576959783331641321507825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93743785511102087048041733 17576959783331641321507825)
                ·
                  refine ⟨13182719837498730991130869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17576959783331641321507825 13182719837498730991130869)
                  ·
                    refine ⟨1235879984765506030418519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13182719837498730991130869 1235879984765506030418519)
                    ·
                      rfl

theorem cell23_7220603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 5].length) (baseStart_7220603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220603 prefixEnd_7220603 := by exact prefixLift 7220603
  have htrace : WordTrace (prefixWord ++ tailWord_7220603) baseStart_7220603 baseEnd_7220603 := by
    simpa [prefixWord, tailWord_7220603, baseEnd_7220603] using wordTrace_append hprefix tailTrace_7220603
  have hstable : (prefixWord ++ tailWord_7220603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220603).length < 2 ^ (prefixWord ++ tailWord_7220603).sum := by decide
  have hdescent : baseEnd_7220603 < baseStart_7220603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220613 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_7220613 : Nat := 118140960795 + 7220613 * 2 ^ 59
def prefixEnd_7220613 : Nat := 4983230072969 + 3 ^ 40 * 7220613 * 2
def baseEnd_7220613 : Nat := 3707645089103063052130511

theorem tailTrace_7220613 : CollatzResearch.WordTrace tailWord_7220613 prefixEnd_7220613 3707645089103063052130511 := by
  unfold tailWord_7220613
  simp only [CollatzResearch.WordTrace]
  refine ⟨263357391789959758366834493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175571594526639838911222995 263357391789959758366834493)
  ·
    refine ⟨98759021921234909387562935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263357391789959758366834493 98759021921234909387562935)
    ·
      refine ⟨148138532881852364081344403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98759021921234909387562935 148138532881852364081344403)
      ·
        refine ⟨222207799322778546122016605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148138532881852364081344403 222207799322778546122016605)
        ·
          refine ⟨83327924746041954795756227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222207799322778546122016605 83327924746041954795756227)
          ·
            refine ⟨124991887119062932193634341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83327924746041954795756227 124991887119062932193634341)
            ·
              refine ⟨23435978834824299786306439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124991887119062932193634341 23435978834824299786306439)
              ·
                refine ⟨35153968252236449679459659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23435978834824299786306439 35153968252236449679459659)
                ·
                  refine ⟨52730952378354674519189489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35153968252236449679459659 52730952378354674519189489)
                  ·
                    refine ⟨39548214283766005889392117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52730952378354674519189489 39548214283766005889392117)
                    ·
                      refine ⟨3707645089103063052130511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39548214283766005889392117 3707645089103063052130511)
                      ·
                        rfl

theorem cell23_7220613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_7220613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220613 prefixEnd_7220613 := by exact prefixLift 7220613
  have htrace : WordTrace (prefixWord ++ tailWord_7220613) baseStart_7220613 baseEnd_7220613 := by
    simpa [prefixWord, tailWord_7220613, baseEnd_7220613] using wordTrace_append hprefix tailTrace_7220613
  have hstable : (prefixWord ++ tailWord_7220613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220613).length < 2 ^ (prefixWord ++ tailWord_7220613).sum := by decide
  have hdescent : baseEnd_7220613 < baseStart_7220613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220637 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_7220637 : Nat := 118140960795 + 7220637 * 2 ^ 59
def prefixEnd_7220637 : Nat := 4983230072969 + 3 ^ 40 * 7220637 * 2
def baseEnd_7220637 : Nat := 1235885804212923652743467

theorem tailTrace_7220637 : CollatzResearch.WordTrace tailWord_7220637 prefixEnd_7220637 1235885804212923652743467 := by
  unfold tailWord_7220637
  simp only [CollatzResearch.WordTrace]
  refine ⟨263358267141872810465708165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175572178094581873643805443 263358267141872810465708165)
  ·
    refine ⟨49379675089101151962320281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263358267141872810465708165 49379675089101151962320281)
    ·
      refine ⟨37034756316825863971740211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49379675089101151962320281 37034756316825863971740211)
      ·
        refine ⟨55552134475238795957610317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37034756316825863971740211 55552134475238795957610317)
        ·
          refine ⟨20832050428214548484103869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55552134475238795957610317 20832050428214548484103869)
          ·
            refine ⟨7812018910580455681538951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20832050428214548484103869 7812018910580455681538951)
            ·
              refine ⟨11718028365870683522308427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812018910580455681538951 11718028365870683522308427)
              ·
                refine ⟨17577042548806025283462641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718028365870683522308427 17577042548806025283462641)
                ·
                  refine ⟨13182781911604518962596981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17577042548806025283462641 13182781911604518962596981)
                  ·
                    refine ⟨1235885804212923652743467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13182781911604518962596981 1235885804212923652743467)
                    ·
                      rfl

theorem cell23_7220637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_7220637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220637 prefixEnd_7220637 := by exact prefixLift 7220637
  have htrace : WordTrace (prefixWord ++ tailWord_7220637) baseStart_7220637 baseEnd_7220637 := by
    simpa [prefixWord, tailWord_7220637, baseEnd_7220637] using wordTrace_append hprefix tailTrace_7220637
  have hstable : (prefixWord ++ tailWord_7220637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220637).length < 2 ^ (prefixWord ++ tailWord_7220637).sum := by decide
  have hdescent : baseEnd_7220637 < baseStart_7220637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220640 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 6, 2]
def baseStart_7220640 : Nat := 118140960795 + 7220640 * 2 ^ 59
def prefixEnd_7220640 : Nat := 4983230072969 + 3 ^ 40 * 7220640 * 2
def baseEnd_7220640 : Nat := 3707658953080734446492887

theorem tailTrace_7220640 : CollatzResearch.WordTrace tailWord_7220640 prefixEnd_7220640 3707658953080734446492887 := by
  unfold tailWord_7220640
  simp only [CollatzResearch.WordTrace]
  refine ⟨131679188280430970989033687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175572251040574627985378249 131679188280430970989033687)
  ·
    refine ⟨197518782420646456483550531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131679188280430970989033687 197518782420646456483550531)
    ·
      refine ⟨296278173630969684725325797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197518782420646456483550531 296278173630969684725325797)
      ·
        refine ⟨55552157555806815885998587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296278173630969684725325797 55552157555806815885998587)
        ·
          refine ⟨83328236333710223828997881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55552157555806815885998587 83328236333710223828997881)
          ·
            refine ⟨62496177250282667871748411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83328236333710223828997881 62496177250282667871748411)
            ·
              refine ⟨93744265875424001807622617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62496177250282667871748411 93744265875424001807622617)
              ·
                refine ⟨70308199406568001355716963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93744265875424001807622617 70308199406568001355716963)
                ·
                  refine ⟨105462299109852002033575445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70308199406568001355716963 105462299109852002033575445)
                  ·
                    refine ⟨4943545270774312595323849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105462299109852002033575445 4943545270774312595323849)
                    ·
                      refine ⟨3707658953080734446492887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943545270774312595323849 3707658953080734446492887)
                      ·
                        rfl

theorem cell23_7220640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_7220640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220640 prefixEnd_7220640 := by exact prefixLift 7220640
  have htrace : WordTrace (prefixWord ++ tailWord_7220640) baseStart_7220640 baseEnd_7220640 := by
    simpa [prefixWord, tailWord_7220640, baseEnd_7220640] using wordTrace_append hprefix tailTrace_7220640
  have hstable : (prefixWord ++ tailWord_7220640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220640).length < 2 ^ (prefixWord ++ tailWord_7220640).sum := by decide
  have hdescent : baseEnd_7220640 < baseStart_7220640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220663 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 8]
def baseStart_7220663 : Nat := 118140960795 + 7220663 * 2 ^ 59
def prefixEnd_7220663 : Nat := 4983230072969 + 3 ^ 40 * 7220663 * 2
def baseEnd_7220663 : Nat := 411963418126198650722809

theorem tailTrace_7220663 : CollatzResearch.WordTrace tailWord_7220663 prefixEnd_7220663 411963418126198650722809 := by
  unfold tailWord_7220663
  simp only [CollatzResearch.WordTrace]
  refine ⟨263359215439778616906154643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175572810293185744604103095 263359215439778616906154643)
  ·
    refine ⟨395038823159667925359231965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263359215439778616906154643 395038823159667925359231965)
    ·
      refine ⟨148139558684875472009711987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395038823159667925359231965 148139558684875472009711987)
      ·
        refine ⟨222209338027313208014567981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148139558684875472009711987 222209338027313208014567981)
        ·
          refine ⟨83328501760242453005462993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222209338027313208014567981 83328501760242453005462993)
          ·
            refine ⟨62496376320181839754097245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83328501760242453005462993 62496376320181839754097245)
            ·
              refine ⟨23436141120068189907786467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62496376320181839754097245 23436141120068189907786467)
              ·
                refine ⟨35154211680102284861679701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23436141120068189907786467 35154211680102284861679701)
                ·
                  refine ⟨411963418126198650722809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35154211680102284861679701 411963418126198650722809)
                  ·
                    rfl

theorem cell23_7220663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 8].length) (baseStart_7220663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220663 prefixEnd_7220663 := by exact prefixLift 7220663
  have htrace : WordTrace (prefixWord ++ tailWord_7220663) baseStart_7220663 baseEnd_7220663 := by
    simpa [prefixWord, tailWord_7220663, baseEnd_7220663] using wordTrace_append hprefix tailTrace_7220663
  have hstable : (prefixWord ++ tailWord_7220663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220663).length < 2 ^ (prefixWord ++ tailWord_7220663).sum := by decide
  have hdescent : baseEnd_7220663 < baseStart_7220663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220701 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_7220701 : Nat := 118140960795 + 7220701 * 2 ^ 59
def prefixEnd_7220701 : Nat := 4983230072969 + 3 ^ 40 * 7220701 * 2
def baseEnd_7220701 : Nat := 1235896758466886235943369

theorem tailTrace_7220701 : CollatzResearch.WordTrace tailWord_7220701 prefixEnd_7220701 1235896758466886235943369 := by
  unfold tailWord_7220701
  simp only [CollatzResearch.WordTrace]
  refine ⟨263360601413640949396037957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175573734275760632930691971 263360601413640949396037957)
  ·
    refine ⟨49380112765057678011757117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263360601413640949396037957 49380112765057678011757117)
    ·
      refine ⟨18517542286896629254408919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49380112765057678011757117 18517542286896629254408919)
      ·
        refine ⟨27776313430344943881613379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18517542286896629254408919 27776313430344943881613379)
        ·
          refine ⟨41664470145517415822420069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27776313430344943881613379 41664470145517415822420069)
          ·
            refine ⟨7812088152284515466703763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41664470145517415822420069 7812088152284515466703763)
            ·
              refine ⟨11718132228426773200055645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812088152284515466703763 11718132228426773200055645)
              ·
                refine ⟨4394299585660039950020867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11718132228426773200055645 4394299585660039950020867)
                ·
                  refine ⟨6591449378490059925031301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394299585660039950020867 6591449378490059925031301)
                  ·
                    refine ⟨1235896758466886235943369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6591449378490059925031301 1235896758466886235943369)
                    ·
                      rfl

theorem cell23_7220701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_7220701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220701 prefixEnd_7220701 := by exact prefixLift 7220701
  have htrace : WordTrace (prefixWord ++ tailWord_7220701) baseStart_7220701 baseEnd_7220701 := by
    simpa [prefixWord, tailWord_7220701, baseEnd_7220701] using wordTrace_append hprefix tailTrace_7220701
  have hstable : (prefixWord ++ tailWord_7220701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220701).length < 2 ^ (prefixWord ++ tailWord_7220701).sum := by decide
  have hdescent : baseEnd_7220701 < baseStart_7220701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220713 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_7220713 : Nat := 118140960795 + 7220713 * 2 ^ 59
def prefixEnd_7220713 : Nat := 4983230072969 + 3 ^ 40 * 7220713 * 2
def baseEnd_7220713 : Nat := 3707696437168512660880051

theorem tailTrace_7220713 : CollatzResearch.WordTrace tailWord_7220713 prefixEnd_7220713 3707696437168512660880051 := by
  unfold tailWord_7220713
  simp only [CollatzResearch.WordTrace]
  refine ⟨263361039089597475445474793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175574026059731650296983195 263361039089597475445474793)
  ·
    refine ⟨197520779317198106584106095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263361039089597475445474793 197520779317198106584106095)
    ·
      refine ⟨296281168975797159876159143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197520779317198106584106095 296281168975797159876159143)
      ·
        refine ⟨444421753463695739814238715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296281168975797159876159143 444421753463695739814238715)
        ·
          refine ⟨666632630195543609721358073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444421753463695739814238715 666632630195543609721358073)
          ·
            refine ⟨499974472646657707291018555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666632630195543609721358073 499974472646657707291018555)
            ·
              refine ⟨749961708969986560936527833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499974472646657707291018555 749961708969986560936527833)
              ·
                refine ⟨562471281727489920702395875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749961708969986560936527833 562471281727489920702395875)
                ·
                  refine ⟨843706922591234881053593813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562471281727489920702395875 843706922591234881053593813)
                  ·
                    refine ⟨19774380998232067524693605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 843706922591234881053593813 19774380998232067524693605)
                    ·
                      refine ⟨3707696437168512660880051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19774380998232067524693605 3707696437168512660880051)
                      ·
                        rfl

theorem cell23_7220713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_7220713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220713 prefixEnd_7220713 := by exact prefixLift 7220713
  have htrace : WordTrace (prefixWord ++ tailWord_7220713) baseStart_7220713 baseEnd_7220713 := by
    simpa [prefixWord, tailWord_7220713, baseEnd_7220713] using wordTrace_append hprefix tailTrace_7220713
  have hstable : (prefixWord ++ tailWord_7220713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220713).length < 2 ^ (prefixWord ++ tailWord_7220713).sum := by decide
  have hdescent : baseEnd_7220713 < baseStart_7220713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220723 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 5, 6]
def baseStart_7220723 : Nat := 118140960795 + 7220723 * 2 ^ 59
def prefixEnd_7220723 : Nat := 4983230072969 + 3 ^ 40 * 7220723 * 2
def baseEnd_7220723 : Nat := 1235900523991685873918335

theorem tailTrace_7220723 : CollatzResearch.WordTrace tailWord_7220723 prefixEnd_7220723 1235900523991685873918335 := by
  unfold tailWord_7220723
  simp only [CollatzResearch.WordTrace]
  refine ⟨263361403819561247153338823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175574269213040831435559215 263361403819561247153338823)
  ·
    refine ⟨395042105729341870730008235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263361403819561247153338823 395042105729341870730008235)
    ·
      refine ⟨592563158594012806095012353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395042105729341870730008235 592563158594012806095012353)
      ·
        refine ⟨444422368945509604571259265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592563158594012806095012353 444422368945509604571259265)
        ·
          refine ⟨333316776709132203428444449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444422368945509604571259265 333316776709132203428444449)
          ·
            refine ⟨249987582531849152571333337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333316776709132203428444449 249987582531849152571333337)
            ·
              refine ⟨187490686898886864428500003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249987582531849152571333337 187490686898886864428500003)
              ·
                refine ⟨281236030348330296642750005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187490686898886864428500003 281236030348330296642750005)
                ·
                  refine ⟨26365877845155965310257813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281236030348330296642750005 26365877845155965310257813)
                  ·
                    refine ⟨1235900523991685873918335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26365877845155965310257813 1235900523991685873918335)
                    ·
                      rfl

theorem cell23_7220723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 6].length) (baseStart_7220723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220723 prefixEnd_7220723 := by exact prefixLift 7220723
  have htrace : WordTrace (prefixWord ++ tailWord_7220723) baseStart_7220723 baseEnd_7220723 := by
    simpa [prefixWord, tailWord_7220723, baseEnd_7220723] using wordTrace_append hprefix tailTrace_7220723
  have hstable : (prefixWord ++ tailWord_7220723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220723).length < 2 ^ (prefixWord ++ tailWord_7220723).sum := by decide
  have hdescent : baseEnd_7220723 < baseStart_7220723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220730 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_7220730 : Nat := 118140960795 + 7220730 * 2 ^ 59
def prefixEnd_7220730 : Nat := 4983230072969 + 3 ^ 40 * 7220730 * 2
def baseEnd_7220730 : Nat := 3707705166339639094367473

theorem tailTrace_7220730 : CollatzResearch.WordTrace tailWord_7220730 prefixEnd_7220730 3707705166339639094367473 := by
  unfold tailWord_7220730
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840414782633971837210911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175574439420357258232562429 65840414782633971837210911)
  ·
    refine ⟨98760622173950957755816367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65840414782633971837210911 98760622173950957755816367)
    ·
      refine ⟨148140933260926436633724551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98760622173950957755816367 148140933260926436633724551)
      ·
        refine ⟨222211399891389654950586827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148140933260926436633724551 222211399891389654950586827)
        ·
          refine ⟨333317099837084482425880241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222211399891389654950586827 333317099837084482425880241)
          ·
            refine ⟨249987824877813361819410181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333317099837084482425880241 249987824877813361819410181)
            ·
              refine ⟨46872717164590005341139409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249987824877813361819410181 46872717164590005341139409)
              ·
                refine ⟨35154537873442504005854557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46872717164590005341139409 35154537873442504005854557)
                ·
                  refine ⟨13182951702540939002195459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35154537873442504005854557 13182951702540939002195459)
                  ·
                    refine ⟨19774427553811408503293189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13182951702540939002195459 19774427553811408503293189)
                    ·
                      refine ⟨3707705166339639094367473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19774427553811408503293189 3707705166339639094367473)
                      ·
                        rfl

theorem cell23_7220730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_7220730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220730 prefixEnd_7220730 := by exact prefixLift 7220730
  have htrace : WordTrace (prefixWord ++ tailWord_7220730) baseStart_7220730 baseEnd_7220730 := by
    simpa [prefixWord, tailWord_7220730, baseEnd_7220730] using wordTrace_append hprefix tailTrace_7220730
  have hstable : (prefixWord ++ tailWord_7220730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220730).length < 2 ^ (prefixWord ++ tailWord_7220730).sum := by decide
  have hdescent : baseEnd_7220730 < baseStart_7220730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220747 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 4]
def baseStart_7220747 : Nat := 118140960795 + 7220747 * 2 ^ 59
def prefixEnd_7220747 : Nat := 4983230072969 + 3 ^ 40 * 7220747 * 2
def baseEnd_7220747 : Nat := 3707713895510765527854895

theorem tailTrace_7220747 : CollatzResearch.WordTrace tailWord_7220747 prefixEnd_7220747 3707713895510765527854895 := by
  unfold tailWord_7220747
  simp only [CollatzResearch.WordTrace]
  refine ⟨263362279171474299252212495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175574852780982866168141663 263362279171474299252212495)
  ·
    refine ⟨395043418757211448878318743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263362279171474299252212495 395043418757211448878318743)
    ·
      refine ⟨592565128135817173317478115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395043418757211448878318743 592565128135817173317478115)
      ·
        refine ⟨888847692203725759976217173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592565128135817173317478115 888847692203725759976217173)
        ·
          refine ⟨10416183893012411249721295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 888847692203725759976217173 10416183893012411249721295)
          ·
            refine ⟨15624275839518616874581943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10416183893012411249721295 15624275839518616874581943)
            ·
              refine ⟨23436413759277925311872915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15624275839518616874581943 23436413759277925311872915)
              ·
                refine ⟨35154620638916887967809373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23436413759277925311872915 35154620638916887967809373)
                ·
                  refine ⟨13182982739593832987928515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35154620638916887967809373 13182982739593832987928515)
                  ·
                    refine ⟨19774474109390749481892773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13182982739593832987928515 19774474109390749481892773)
                    ·
                      refine ⟨3707713895510765527854895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19774474109390749481892773 3707713895510765527854895)
                      ·
                        rfl

theorem cell23_7220747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 4].length) (baseStart_7220747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220747 prefixEnd_7220747 := by exact prefixLift 7220747
  have htrace : WordTrace (prefixWord ++ tailWord_7220747) baseStart_7220747 baseEnd_7220747 := by
    simpa [prefixWord, tailWord_7220747, baseEnd_7220747] using wordTrace_append hprefix tailTrace_7220747
  have hstable : (prefixWord ++ tailWord_7220747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220747).length < 2 ^ (prefixWord ++ tailWord_7220747).sum := by decide
  have hdescent : baseEnd_7220747 < baseStart_7220747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220753 : List Nat := [1, 2, 2, 1, 1, 2, 3, 11]
def baseStart_7220753 : Nat := 118140960795 + 7220753 * 2 ^ 59
def prefixEnd_7220753 : Nat := 4983230072969 + 3 ^ 40 * 7220753 * 2
def baseEnd_7220753 : Nat := 137322850977581203865921

theorem tailTrace_7220753 : CollatzResearch.WordTrace tailWord_7220753 prefixEnd_7220753 137322850977581203865921 := by
  unfold tailWord_7220753
  simp only [CollatzResearch.WordTrace]
  refine ⟨263362498009452562276930913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175574998672968374851287275 263362498009452562276930913)
  ·
    refine ⟨197521873507089421707698185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263362498009452562276930913 197521873507089421707698185)
    ·
      refine ⟨148141405130317066280773639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197521873507089421707698185 148141405130317066280773639)
      ·
        refine ⟨222212107695475599421160459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148141405130317066280773639 222212107695475599421160459)
        ·
          refine ⟨333318161543213399131740689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222212107695475599421160459 333318161543213399131740689)
          ·
            refine ⟨249988621157410049348805517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333318161543213399131740689 249988621157410049348805517)
            ·
              refine ⟨93745732934028768505802069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249988621157410049348805517 93745732934028768505802069)
              ·
                refine ⟨137322850977581203865921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93745732934028768505802069 137322850977581203865921)
                ·
                  rfl

theorem cell23_7220753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 11].length) (baseStart_7220753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220753 prefixEnd_7220753 := by exact prefixLift 7220753
  have htrace : WordTrace (prefixWord ++ tailWord_7220753) baseStart_7220753 baseEnd_7220753 := by
    simpa [prefixWord, tailWord_7220753, baseEnd_7220753] using wordTrace_append hprefix tailTrace_7220753
  have hstable : (prefixWord ++ tailWord_7220753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220753).length < 2 ^ (prefixWord ++ tailWord_7220753).sum := by decide
  have hdescent : baseEnd_7220753 < baseStart_7220753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220764 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_7220764 : Nat := 118140960795 + 7220764 * 2 ^ 59
def prefixEnd_7220764 : Nat := 4983230072969 + 3 ^ 40 * 7220764 * 2
def baseEnd_7220764 : Nat := 3707722624681891961342317

theorem tailTrace_7220764 : CollatzResearch.WordTrace tailWord_7220764 prefixEnd_7220764 3707722624681891961342317 := by
  unfold tailWord_7220764
  simp only [CollatzResearch.WordTrace]
  refine ⟨131681449606206355577790673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175575266141608474103720897 131681449606206355577790673)
  ·
    refine ⟨98761087204654766683343005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131681449606206355577790673 98761087204654766683343005)
    ·
      refine ⟨37035407701745537506253627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98761087204654766683343005 37035407701745537506253627)
      ·
        refine ⟨55553111552618306259380441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37035407701745537506253627 55553111552618306259380441)
        ·
          refine ⟨41664833664463729694535331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55553111552618306259380441 41664833664463729694535331)
          ·
            refine ⟨62497250496695594541802997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41664833664463729694535331 62497250496695594541802997)
            ·
              refine ⟨5859117234065211988294031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62497250496695594541802997 5859117234065211988294031)
              ·
                refine ⟨8788675851097817982441047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859117234065211988294031 8788675851097817982441047)
                ·
                  refine ⟨13183013776646726973661571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8788675851097817982441047 13183013776646726973661571)
                  ·
                    refine ⟨19774520664970090460492357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13183013776646726973661571 19774520664970090460492357)
                    ·
                      refine ⟨3707722624681891961342317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19774520664970090460492357 3707722624681891961342317)
                      ·
                        rfl

theorem cell23_7220764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_7220764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220764 prefixEnd_7220764 := by exact prefixLift 7220764
  have htrace : WordTrace (prefixWord ++ tailWord_7220764) baseStart_7220764 baseEnd_7220764 := by
    simpa [prefixWord, tailWord_7220764, baseEnd_7220764] using wordTrace_append hprefix tailTrace_7220764
  have hstable : (prefixWord ++ tailWord_7220764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220764).length < 2 ^ (prefixWord ++ tailWord_7220764).sum := by decide
  have hdescent : baseEnd_7220764 < baseStart_7220764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220767 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 3]
def baseStart_7220767 : Nat := 118140960795 + 7220767 * 2 ^ 59
def prefixEnd_7220767 : Nat := 4983230072969 + 3 ^ 40 * 7220767 * 2
def baseEnd_7220767 : Nat := 3707724165123855449604803

theorem tailTrace_7220767 : CollatzResearch.WordTrace tailWord_7220767 prefixEnd_7220767 3707724165123855449604803 := by
  unfold tailWord_7220767
  simp only [CollatzResearch.WordTrace]
  refine ⟨263363008631401842667940555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175575339087601228445293703 263363008631401842667940555)
  ·
    refine ⟨395044512947102764001910833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263363008631401842667940555 395044512947102764001910833)
    ·
      refine ⟨296283384710327073001433125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395044512947102764001910833 296283384710327073001433125)
      ·
        refine ⟨55553134633186326187768711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296283384710327073001433125 55553134633186326187768711)
        ·
          refine ⟨83329701949779489281653067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55553134633186326187768711 83329701949779489281653067)
          ·
            refine ⟨124994552924669233922479601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83329701949779489281653067 124994552924669233922479601)
            ·
              refine ⟨93745914693501925441859701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124994552924669233922479601 93745914693501925441859701)
              ·
                refine ⟨8788679502515805510174347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93745914693501925441859701 8788679502515805510174347)
                ·
                  refine ⟨13183019253773708265261521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8788679502515805510174347 13183019253773708265261521)
                  ·
                    refine ⟨9887264440330281198946141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13183019253773708265261521 9887264440330281198946141)
                    ·
                      refine ⟨3707724165123855449604803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9887264440330281198946141 3707724165123855449604803)
                      ·
                        rfl

theorem cell23_7220767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_7220767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220767 prefixEnd_7220767 := by exact prefixLift 7220767
  have htrace : WordTrace (prefixWord ++ tailWord_7220767) baseStart_7220767 baseEnd_7220767 := by
    simpa [prefixWord, tailWord_7220767, baseEnd_7220767] using wordTrace_append hprefix tailTrace_7220767
  have hstable : (prefixWord ++ tailWord_7220767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220767).length < 2 ^ (prefixWord ++ tailWord_7220767).sum := by decide
  have hdescent : baseEnd_7220767 < baseStart_7220767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220810 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_7220810 : Nat := 118140960795 + 7220810 * 2 ^ 59
def prefixEnd_7220810 : Nat := 4983230072969 + 3 ^ 40 * 7220810 * 2
def baseEnd_7220810 : Nat := 3707746244791998781367105

theorem tailTrace_7220810 : CollatzResearch.WordTrace tailWord_7220810 prefixEnd_7220810 3707746244791998781367105 := by
  unfold tailWord_7220810
  simp only [CollatzResearch.WordTrace]
  refine ⟨65841144242561515252938971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175576384646830707341170589 65841144242561515252938971)
  ·
    refine ⟨98761716363842272879408457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65841144242561515252938971 98761716363842272879408457)
    ·
      refine ⟨74071287272881704659556343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98761716363842272879408457 74071287272881704659556343)
      ·
        refine ⟨111106930909322556989334515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74071287272881704659556343 111106930909322556989334515)
        ·
          refine ⟨166660396363983835484001773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111106930909322556989334515 166660396363983835484001773)
          ·
            refine ⟨62497648636493938306500665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166660396363983835484001773 62497648636493938306500665)
            ·
              refine ⟨46873236477370453729875499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62497648636493938306500665 46873236477370453729875499)
              ·
                refine ⟨70309854716055680594813249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46873236477370453729875499 70309854716055680594813249)
                ·
                  refine ⟨52732391037041760446109937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70309854716055680594813249 52732391037041760446109937)
                  ·
                    refine ⟨39549293277781320334582453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52732391037041760446109937 39549293277781320334582453)
                    ·
                      refine ⟨3707746244791998781367105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39549293277781320334582453 3707746244791998781367105)
                      ·
                        rfl

theorem cell23_7220810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_7220810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220810 prefixEnd_7220810 := by exact prefixLift 7220810
  have htrace : WordTrace (prefixWord ++ tailWord_7220810) baseStart_7220810 baseEnd_7220810 := by
    simpa [prefixWord, tailWord_7220810, baseEnd_7220810] using wordTrace_append hprefix tailTrace_7220810
  have hstable : (prefixWord ++ tailWord_7220810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220810).length < 2 ^ (prefixWord ++ tailWord_7220810).sum := by decide
  have hdescent : baseEnd_7220810 < baseStart_7220810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220894 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7220894 : Nat := 118140960795 + 7220894 * 2 ^ 59
def prefixEnd_7220894 : Nat := 4983230072969 + 3 ^ 40 * 7220894 * 2
def baseEnd_7220894 : Nat := 411976597462997383635191

theorem tailTrace_7220894 : CollatzResearch.WordTrace tailWord_7220894 prefixEnd_7220894 411976597462997383635191 := by
  unfold tailWord_7220894
  simp only [CollatzResearch.WordTrace]
  refine ⟨32920955087742717919726717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175578427134627828905209157 32920955087742717919726717)
  ·
    refine ⟨12345358157903519219897519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32920955087742717919726717 12345358157903519219897519)
    ·
      refine ⟨18518037236855278829846279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12345358157903519219897519 18518037236855278829846279)
      ·
        refine ⟨27777055855282918244769419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18518037236855278829846279 27777055855282918244769419)
        ·
          refine ⟨41665583782924377367154129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27777055855282918244769419 41665583782924377367154129)
          ·
            refine ⟨31249187837193283025365597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41665583782924377367154129 31249187837193283025365597)
            ·
              refine ⟨11718445438947481134512099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31249187837193283025365597 11718445438947481134512099)
              ·
                refine ⟨17577668158421221701768149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718445438947481134512099 17577668158421221701768149)
                ·
                  refine ⟨411976597462997383635191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17577668158421221701768149 411976597462997383635191)
                  ·
                    rfl

theorem cell23_7220894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7220894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220894 prefixEnd_7220894 := by exact prefixLift 7220894
  have htrace : WordTrace (prefixWord ++ tailWord_7220894) baseStart_7220894 baseEnd_7220894 := by
    simpa [prefixWord, tailWord_7220894, baseEnd_7220894] using wordTrace_append hprefix tailTrace_7220894
  have hstable : (prefixWord ++ tailWord_7220894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220894).length < 2 ^ (prefixWord ++ tailWord_7220894).sum := by decide
  have hdescent : baseEnd_7220894 < baseStart_7220894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220920 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_7220920 : Nat := 118140960795 + 7220920 * 2 ^ 59
def prefixEnd_7220920 : Nat := 4983230072969 + 3 ^ 40 * 7220920 * 2
def baseEnd_7220920 : Nat := 1235934242554664450330533

theorem tailTrace_7220920 : CollatzResearch.WordTrace tailWord_7220920 prefixEnd_7220920 1235934242554664450330533 := by
  unfold tailWord_7220920
  simp only [CollatzResearch.WordTrace]
  refine ⟨131684294499923774899130107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175579059333231699865506809 131684294499923774899130107)
  ·
    refine ⟨197526441749885662348695161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131684294499923774899130107 197526441749885662348695161)
    ·
      refine ⟨148144831312414246761521371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197526441749885662348695161 148144831312414246761521371)
      ·
        refine ⟨222217246968621370142282057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148144831312414246761521371 222217246968621370142282057)
        ·
          refine ⟨166662935226466027606711543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222217246968621370142282057 166662935226466027606711543)
          ·
            refine ⟨249994402839699041410067315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166662935226466027606711543 249994402839699041410067315)
            ·
              refine ⟨374991604259548562115100973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249994402839699041410067315 374991604259548562115100973)
              ·
                refine ⟨140621851597330710793162865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374991604259548562115100973 140621851597330710793162865)
                ·
                  refine ⟨105466388697998033094872149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140621851597330710793162865 105466388697998033094872149)
                  ·
                    refine ⟨1235934242554664450330533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105466388697998033094872149 1235934242554664450330533)
                    ·
                      rfl

theorem cell23_7220920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_7220920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220920 prefixEnd_7220920 := by exact prefixLift 7220920
  have htrace : WordTrace (prefixWord ++ tailWord_7220920) baseStart_7220920 baseEnd_7220920 := by
    simpa [prefixWord, tailWord_7220920, baseEnd_7220920] using wordTrace_append hprefix tailTrace_7220920
  have hstable : (prefixWord ++ tailWord_7220920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220920).length < 2 ^ (prefixWord ++ tailWord_7220920).sum := by decide
  have hdescent : baseEnd_7220920 < baseStart_7220920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220924 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_7220924 : Nat := 118140960795 + 7220924 * 2 ^ 59
def prefixEnd_7220924 : Nat := 4983230072969 + 3 ^ 40 * 7220924 * 2
def baseEnd_7220924 : Nat := 1235934927195537111780527

theorem tailTrace_7220924 : CollatzResearch.WordTrace tailWord_7220924 prefixEnd_7220924 1235934927195537111780527 := by
  unfold tailWord_7220924
  simp only [CollatzResearch.WordTrace]
  refine ⟨131684367445916529240702913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175579156594555372320937217 131684367445916529240702913)
  ·
    refine ⟨98763275584437396930527185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131684367445916529240702913 98763275584437396930527185)
    ·
      refine ⟨74072456688328047697895389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98763275584437396930527185 74072456688328047697895389)
      ·
        refine ⟨27777171258123017886710771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74072456688328047697895389 27777171258123017886710771)
        ·
          refine ⟨41665756887184526830066157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27777171258123017886710771 41665756887184526830066157)
          ·
            refine ⟨15624658832694197561274809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41665756887184526830066157 15624658832694197561274809)
            ·
              refine ⟨11718494124520648170956107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15624658832694197561274809 11718494124520648170956107)
              ·
                refine ⟨17577741186780972256434161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718494124520648170956107 17577741186780972256434161)
                ·
                  refine ⟨13183305890085729192325621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17577741186780972256434161 13183305890085729192325621)
                  ·
                    refine ⟨1235934927195537111780527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13183305890085729192325621 1235934927195537111780527)
                    ·
                      rfl

theorem cell23_7220924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_7220924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220924 prefixEnd_7220924 := by exact prefixLift 7220924
  have htrace : WordTrace (prefixWord ++ tailWord_7220924) baseStart_7220924 baseEnd_7220924 := by
    simpa [prefixWord, tailWord_7220924, baseEnd_7220924] using wordTrace_append hprefix tailTrace_7220924
  have hstable : (prefixWord ++ tailWord_7220924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220924).length < 2 ^ (prefixWord ++ tailWord_7220924).sum := by decide
  have hdescent : baseEnd_7220924 < baseStart_7220924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220941 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7220941 : Nat := 118140960795 + 7220941 * 2 ^ 59
def prefixEnd_7220941 : Nat := 4983230072969 + 3 ^ 40 * 7220941 * 2
def baseEnd_7220941 : Nat := 1235937836919245922943001

theorem tailTrace_7220941 : CollatzResearch.WordTrace tailWord_7220941 prefixEnd_7220941 1235937836919245922943001 := by
  unfold tailWord_7220941
  simp only [CollatzResearch.WordTrace]
  refine ⟨263369354932771470384774677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175579569955180980256516451 263369354932771470384774677)
  ·
    refine ⟨12345438512473662674286313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263369354932771470384774677 12345438512473662674286313)
    ·
      refine ⟨9259078884355247005714735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12345438512473662674286313 9259078884355247005714735)
      ·
        refine ⟨13888618326532870508572103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9259078884355247005714735 13888618326532870508572103)
        ·
          refine ⟨20832927489799305762858155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13888618326532870508572103 20832927489799305762858155)
          ·
            refine ⟨31249391234698958644287233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20832927489799305762858155 31249391234698958644287233)
            ·
              refine ⟨23437043426024218983215425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31249391234698958644287233 23437043426024218983215425)
              ·
                refine ⟨17577782569518164237411569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23437043426024218983215425 17577782569518164237411569)
                ·
                  refine ⟨13183336927138623178058677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17577782569518164237411569 13183336927138623178058677)
                  ·
                    refine ⟨1235937836919245922943001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13183336927138623178058677 1235937836919245922943001)
                    ·
                      rfl

theorem cell23_7220941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7220941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220941 prefixEnd_7220941 := by exact prefixLift 7220941
  have htrace : WordTrace (prefixWord ++ tailWord_7220941) baseStart_7220941 baseEnd_7220941 := by
    simpa [prefixWord, tailWord_7220941, baseEnd_7220941] using wordTrace_append hprefix tailTrace_7220941
  have hstable : (prefixWord ++ tailWord_7220941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220941).length < 2 ^ (prefixWord ++ tailWord_7220941).sum := by decide
  have hdescent : baseEnd_7220941 < baseStart_7220941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220947 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 3]
def baseStart_7220947 : Nat := 118140960795 + 7220947 * 2 ^ 59
def prefixEnd_7220947 : Nat := 4983230072969 + 3 ^ 40 * 7220947 * 2
def baseEnd_7220947 : Nat := 3707816591641664745353975

theorem tailTrace_7220947 : CollatzResearch.WordTrace tailWord_7220947 prefixEnd_7220947 3707816591641664745353975 := by
  unfold tailWord_7220947
  simp only [CollatzResearch.WordTrace]
  refine ⟨263369573770749733409493095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175579715847166488939662063 263369573770749733409493095)
  ·
    refine ⟨395054360656124600114239643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263369573770749733409493095 395054360656124600114239643)
    ·
      refine ⟨592581540984186900171359465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395054360656124600114239643 592581540984186900171359465)
      ·
        refine ⟨444436155738140175128519599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592581540984186900171359465 444436155738140175128519599)
        ·
          refine ⟨666654233607210262692779399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444436155738140175128519599 666654233607210262692779399)
          ·
            refine ⟨999981350410815394039169099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666654233607210262692779399 999981350410815394039169099)
            ·
              refine ⟨1499972025616223091058753649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999981350410815394039169099 1499972025616223091058753649)
              ·
                refine ⟨1124979019212167318294065237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499972025616223091058753649 1124979019212167318294065237)
                ·
                  refine ⟨13183347881392585761258577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1124979019212167318294065237 13183347881392585761258577)
                  ·
                    refine ⟨9887510911044439320943933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13183347881392585761258577 9887510911044439320943933)
                    ·
                      refine ⟨3707816591641664745353975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9887510911044439320943933 3707816591641664745353975)
                      ·
                        rfl

theorem cell23_7220947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_7220947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220947 prefixEnd_7220947 := by exact prefixLift 7220947
  have htrace : WordTrace (prefixWord ++ tailWord_7220947) baseStart_7220947 baseEnd_7220947 := by
    simpa [prefixWord, tailWord_7220947, baseEnd_7220947] using wordTrace_append hprefix tailTrace_7220947
  have hstable : (prefixWord ++ tailWord_7220947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220947).length < 2 ^ (prefixWord ++ tailWord_7220947).sum := by decide
  have hdescent : baseEnd_7220947 < baseStart_7220947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7220961 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_7220961 : Nat := 118140960795 + 7220961 * 2 ^ 59
def prefixEnd_7220961 : Nat := 4983230072969 + 3 ^ 40 * 7220961 * 2
def baseEnd_7220961 : Nat := 3707823780370827690578911

theorem tailTrace_7220961 : CollatzResearch.WordTrace tailWord_7220961 prefixEnd_7220961 3707823780370827690578911 := by
  unfold tailWord_7220961
  simp only [CollatzResearch.WordTrace]
  refine ⟨263370084392699013800502737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175580056261799342533668491 263370084392699013800502737)
  ·
    refine ⟨197527563294524260350377053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263370084392699013800502737 197527563294524260350377053)
    ·
      refine ⟨74072836235446597631391395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197527563294524260350377053 74072836235446597631391395)
      ·
        refine ⟨111109254353169896447087093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74072836235446597631391395 111109254353169896447087093)
        ·
          refine ⟨10416492595609677791914415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111109254353169896447087093 10416492595609677791914415)
          ·
            refine ⟨15624738893414516687871623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10416492595609677791914415 15624738893414516687871623)
            ·
              refine ⟨23437108340121775031807435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15624738893414516687871623 23437108340121775031807435)
              ·
                refine ⟨35155662510182662547711153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23437108340121775031807435 35155662510182662547711153)
                ·
                  refine ⟨26366746882636996910783365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35155662510182662547711153 26366746882636996910783365)
                  ·
                    refine ⟨4943765040494436920771881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26366746882636996910783365 4943765040494436920771881)
                    ·
                      refine ⟨3707823780370827690578911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943765040494436920771881 3707823780370827690578911)
                      ·
                        rfl

theorem cell23_7220961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_7220961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7220961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7220961 prefixEnd_7220961 := by exact prefixLift 7220961
  have htrace : WordTrace (prefixWord ++ tailWord_7220961) baseStart_7220961 baseEnd_7220961 := by
    simpa [prefixWord, tailWord_7220961, baseEnd_7220961] using wordTrace_append hprefix tailTrace_7220961
  have hstable : (prefixWord ++ tailWord_7220961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7220961).length < 2 ^ (prefixWord ++ tailWord_7220961).sum := by decide
  have hdescent : baseEnd_7220961 < baseStart_7220961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7220961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221062 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7221062 : Nat := 118140960795 + 7221062 * 2 ^ 59
def prefixEnd_7221062 : Nat := 4983230072969 + 3 ^ 40 * 7221062 * 2
def baseEnd_7221062 : Nat := 3707875641916931795415947

theorem tailTrace_7221062 : CollatzResearch.WordTrace tailWord_7221062 prefixEnd_7221062 3707875641916931795415947 := by
  unfold tailWord_7221062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230430255166659626560295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175582512110222072033286293 8230430255166659626560295)
  ·
    refine ⟨12345645382749989439840443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8230430255166659626560295 12345645382749989439840443)
    ·
      refine ⟨18518468074124984159760665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12345645382749989439840443 18518468074124984159760665)
      ·
        refine ⟨13888851055593738119820499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18518468074124984159760665 13888851055593738119820499)
        ·
          refine ⟨20833276583390607179730749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13888851055593738119820499 20833276583390607179730749)
          ·
            refine ⟨7812478718771477692399031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20833276583390607179730749 7812478718771477692399031)
            ·
              refine ⟨11718718078157216538598547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812478718771477692399031 11718718078157216538598547)
              ·
                refine ⟨17578077117235824807897821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718718078157216538598547 17578077117235824807897821)
                ·
                  refine ⟨6591778918963434302961683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17578077117235824807897821 6591778918963434302961683)
                  ·
                    refine ⟨9887668378445151454442525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6591778918963434302961683 9887668378445151454442525)
                    ·
                      refine ⟨3707875641916931795415947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9887668378445151454442525 3707875641916931795415947)
                      ·
                        rfl

theorem cell23_7221062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7221062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221062 prefixEnd_7221062 := by exact prefixLift 7221062
  have htrace : WordTrace (prefixWord ++ tailWord_7221062) baseStart_7221062 baseEnd_7221062 := by
    simpa [prefixWord, tailWord_7221062, baseEnd_7221062] using wordTrace_append hprefix tailTrace_7221062
  have hstable : (prefixWord ++ tailWord_7221062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221062).length < 2 ^ (prefixWord ++ tailWord_7221062).sum := by decide
  have hdescent : baseEnd_7221062 < baseStart_7221062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221074 : List Nat := [3, 2, 2, 1, 1, 4, 2, 8]
def baseStart_7221074 : Nat := 118140960795 + 7221074 * 2 ^ 59
def prefixEnd_7221074 : Nat := 4983230072969 + 3 ^ 40 * 7221074 * 2
def baseEnd_7221074 : Nat := 137328955692029101795033

theorem tailTrace_7221074 : CollatzResearch.WordTrace tailWord_7221074 prefixEnd_7221074 137328955692029101795033 := by
  unfold tailWord_7221074
  simp only [CollatzResearch.WordTrace]
  refine ⟨65843551460322408524841569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175582803894193089399577517 65843551460322408524841569)
  ·
    refine ⟨49382663595241806393631177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65843551460322408524841569 49382663595241806393631177)
    ·
      refine ⟨37036997696431354795223383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49382663595241806393631177 37036997696431354795223383)
      ·
        refine ⟨55555496544647032192835075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37036997696431354795223383 55555496544647032192835075)
        ·
          refine ⟨83333244816970548289252613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55555496544647032192835075 83333244816970548289252613)
          ·
            refine ⟨15624983403181977804234865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83333244816970548289252613 15624983403181977804234865)
            ·
              refine ⟨11718737552386483353176149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15624983403181977804234865 11718737552386483353176149)
              ·
                refine ⟨137328955692029101795033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11718737552386483353176149 137328955692029101795033)
                ·
                  rfl

theorem cell23_7221074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_7221074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221074 prefixEnd_7221074 := by exact prefixLift 7221074
  have htrace : WordTrace (prefixWord ++ tailWord_7221074) baseStart_7221074 baseEnd_7221074 := by
    simpa [prefixWord, tailWord_7221074, baseEnd_7221074] using wordTrace_append hprefix tailTrace_7221074
  have hstable : (prefixWord ++ tailWord_7221074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221074).length < 2 ^ (prefixWord ++ tailWord_7221074).sum := by decide
  have hdescent : baseEnd_7221074 < baseStart_7221074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221088 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3]
def baseStart_7221088 : Nat := 118140960795 + 7221088 * 2 ^ 59
def prefixEnd_7221088 : Nat := 4983230072969 + 3 ^ 40 * 7221088 * 2
def baseEnd_7221088 : Nat := 3707888992413948693690827

theorem tailTrace_7221088 : CollatzResearch.WordTrace tailWord_7221088 prefixEnd_7221088 3707888992413948693690827 := by
  unfold tailWord_7221088
  simp only [CollatzResearch.WordTrace]
  refine ⟨131687358231619457245187959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175583144308825942993583945 131687358231619457245187959)
  ·
    refine ⟨197531037347429185867781939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131687358231619457245187959 197531037347429185867781939)
    ·
      refine ⟨296296556021143778801672909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197531037347429185867781939 296296556021143778801672909)
      ·
        refine ⟨111111208507928917050627341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296296556021143778801672909 111111208507928917050627341)
        ·
          refine ⟨41666703190473343893985253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111111208507928917050627341 41666703190473343893985253)
          ·
            refine ⟨7812506848213751980122235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41666703190473343893985253 7812506848213751980122235)
            ·
              refine ⟨11718760272320627970183353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812506848213751980122235 11718760272320627970183353)
              ·
                refine ⟨8789070204240470977637515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11718760272320627970183353 8789070204240470977637515)
                ·
                  refine ⟨13183605306360706466456273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8789070204240470977637515 13183605306360706466456273)
                  ·
                    refine ⟨9887703979770529849842205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13183605306360706466456273 9887703979770529849842205)
                    ·
                      refine ⟨3707888992413948693690827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9887703979770529849842205 3707888992413948693690827)
                      ·
                        rfl

theorem cell23_7221088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_7221088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221088 prefixEnd_7221088 := by exact prefixLift 7221088
  have htrace : WordTrace (prefixWord ++ tailWord_7221088) baseStart_7221088 baseEnd_7221088 := by
    simpa [prefixWord, tailWord_7221088, baseEnd_7221088] using wordTrace_append hprefix tailTrace_7221088
  have hstable : (prefixWord ++ tailWord_7221088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221088).length < 2 ^ (prefixWord ++ tailWord_7221088).sum := by decide
  have hdescent : baseEnd_7221088 < baseStart_7221088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221097 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_7221097 : Nat := 118140960795 + 7221097 * 2 ^ 59
def prefixEnd_7221097 : Nat := 4983230072969 + 3 ^ 40 * 7221097 * 2
def baseEnd_7221097 : Nat := 3707893613739839158478285

theorem tailTrace_7221097 : CollatzResearch.WordTrace tailWord_7221097 prefixEnd_7221097 3707893613739839158478285 := by
  unfold tailWord_7221097
  simp only [CollatzResearch.WordTrace]
  refine ⟨263375044720206309027453545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175583363146804206018302363 263375044720206309027453545)
  ·
    refine ⟨197531283540154731770590159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263375044720206309027453545 197531283540154731770590159)
    ·
      refine ⟨296296925310232097655885239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197531283540154731770590159 296296925310232097655885239)
      ·
        refine ⟨444445387965348146483827859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296296925310232097655885239 444445387965348146483827859)
        ·
          refine ⟨666668081948022219725741789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444445387965348146483827859 666668081948022219725741789)
          ·
            refine ⟨250000530730508332397153171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666668081948022219725741789 250000530730508332397153171)
            ·
              refine ⟨375000796095762498595729757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250000530730508332397153171 375000796095762498595729757)
              ·
                refine ⟨140625298535910936973398659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375000796095762498595729757 140625298535910936973398659)
                ·
                  refine ⟨210937947803866405460097989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140625298535910936973398659 210937947803866405460097989)
                  ·
                    refine ⟨39550865213224951023768373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210937947803866405460097989 39550865213224951023768373)
                    ·
                      refine ⟨3707893613739839158478285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39550865213224951023768373 3707893613739839158478285)
                      ·
                        rfl

theorem cell23_7221097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_7221097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221097 prefixEnd_7221097 := by exact prefixLift 7221097
  have htrace : WordTrace (prefixWord ++ tailWord_7221097) baseStart_7221097 baseEnd_7221097 := by
    simpa [prefixWord, tailWord_7221097, baseEnd_7221097] using wordTrace_append hprefix tailTrace_7221097
  have hstable : (prefixWord ++ tailWord_7221097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221097).length < 2 ^ (prefixWord ++ tailWord_7221097).sum := by decide
  have hdescent : baseEnd_7221097 < baseStart_7221097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221098 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7221098 : Nat := 118140960795 + 7221098 * 2 ^ 59
def prefixEnd_7221098 : Nat := 4983230072969 + 3 ^ 40 * 7221098 * 2
def baseEnd_7221098 : Nat := 3707894127220493654565781

theorem tailTrace_7221098 : CollatzResearch.WordTrace tailWord_7221098 prefixEnd_7221098 3707894127220493654565781 := by
  unfold tailWord_7221098
  simp only [CollatzResearch.WordTrace]
  refine ⟨65843770298300671549559987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175583387462135124132159965 65843770298300671549559987)
  ·
    refine ⟨98765655447451007324339981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65843770298300671549559987 98765655447451007324339981)
    ·
      refine ⟨37037120792794127746627493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98765655447451007324339981 37037120792794127746627493)
      ·
        refine ⟨6944460148648898952492655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37037120792794127746627493 6944460148648898952492655)
        ·
          refine ⟨10416690222973348428738983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944460148648898952492655 10416690222973348428738983)
          ·
            refine ⟨15625035334460022643108475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10416690222973348428738983 15625035334460022643108475)
            ·
              refine ⟨23437553001690033964662713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15625035334460022643108475 23437553001690033964662713)
              ·
                refine ⟨17578164751267525473497035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23437553001690033964662713 17578164751267525473497035)
                ·
                  refine ⟨26367247126901288210245553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17578164751267525473497035 26367247126901288210245553)
                  ·
                    refine ⟨19775435345175966157684165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26367247126901288210245553 19775435345175966157684165)
                    ·
                      refine ⟨3707894127220493654565781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19775435345175966157684165 3707894127220493654565781)
                      ·
                        rfl

theorem cell23_7221098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7221098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221098 prefixEnd_7221098 := by exact prefixLift 7221098
  have htrace : WordTrace (prefixWord ++ tailWord_7221098) baseStart_7221098 baseEnd_7221098 := by
    simpa [prefixWord, tailWord_7221098, baseEnd_7221098] using wordTrace_append hprefix tailTrace_7221098
  have hstable : (prefixWord ++ tailWord_7221098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221098).length < 2 ^ (prefixWord ++ tailWord_7221098).sum := by decide
  have hdescent : baseEnd_7221098 < baseStart_7221098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221101 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7221101 : Nat := 118140960795 + 7221101 * 2 ^ 59
def prefixEnd_7221101 : Nat := 4983230072969 + 3 ^ 40 * 7221101 * 2
def baseEnd_7221101 : Nat := 3707895667662457142828267

theorem tailTrace_7221101 : CollatzResearch.WordTrace tailWord_7221101 prefixEnd_7221101 3707895667662457142828267 := by
  unfold tailWord_7221101
  simp only [CollatzResearch.WordTrace]
  refine ⟨263375190612191817710599157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175583460408127878473732771 263375190612191817710599157)
  ·
    refine ⟨24691424119892982910368671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263375190612191817710599157 24691424119892982910368671)
    ·
      refine ⟨37037136179839474365553007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24691424119892982910368671 37037136179839474365553007)
      ·
        refine ⟨55555704269759211548329511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37037136179839474365553007 55555704269759211548329511)
        ·
          refine ⟨83333556404638817322494267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55555704269759211548329511 83333556404638817322494267)
          ·
            refine ⟨125000334606958225983741401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83333556404638817322494267 125000334606958225983741401)
            ·
              refine ⟨93750250955218669487806051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125000334606958225983741401 93750250955218669487806051)
              ·
                refine ⟨140625376432828004231709077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93750250955218669487806051 140625376432828004231709077)
                ·
                  refine ⟨6591814520288812698361363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140625376432828004231709077 6591814520288812698361363)
                  ·
                    refine ⟨9887721780433219047542045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6591814520288812698361363 9887721780433219047542045)
                    ·
                      refine ⟨3707895667662457142828267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9887721780433219047542045 3707895667662457142828267)
                      ·
                        rfl

theorem cell23_7221101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7221101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221101 prefixEnd_7221101 := by exact prefixLift 7221101
  have htrace : WordTrace (prefixWord ++ tailWord_7221101) baseStart_7221101 baseEnd_7221101 := by
    simpa [prefixWord, tailWord_7221101, baseEnd_7221101] using wordTrace_append hprefix tailTrace_7221101
  have hstable : (prefixWord ++ tailWord_7221101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221101).length < 2 ^ (prefixWord ++ tailWord_7221101).sum := by decide
  have hdescent : baseEnd_7221101 < baseStart_7221101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221124 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_7221124 : Nat := 118140960795 + 7221124 * 2 ^ 59
def prefixEnd_7221124 : Nat := 4983230072969 + 3 ^ 40 * 7221124 * 2
def baseEnd_7221124 : Nat := 3707907477717510552840661

theorem tailTrace_7221124 : CollatzResearch.WordTrace tailWord_7221124 prefixEnd_7221124 3707907477717510552840661 := by
  unfold tailWord_7221124
  simp only [CollatzResearch.WordTrace]
  refine ⟨131688014745554246319343213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175584019660738995092457617 131688014745554246319343213)
  ·
    refine ⟨49383005529582842369753705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131688014745554246319343213 49383005529582842369753705)
    ·
      refine ⟨37037254147187131777315279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49383005529582842369753705 37037254147187131777315279)
      ·
        refine ⟨55555881220780697665972919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37037254147187131777315279 55555881220780697665972919)
        ·
          refine ⟨83333821831171046498959379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55555881220780697665972919 83333821831171046498959379)
          ·
            refine ⟨125000732746756569748439069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83333821831171046498959379 125000732746756569748439069)
            ·
              refine ⟨46875274780033713655664651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125000732746756569748439069 46875274780033713655664651)
              ·
                refine ⟨70312912170050570483496977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46875274780033713655664651 70312912170050570483496977)
                ·
                  refine ⟨52734684127537927862622733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70312912170050570483496977 52734684127537927862622733)
                  ·
                    refine ⟨19775506547826722948483525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52734684127537927862622733 19775506547826722948483525)
                    ·
                      refine ⟨3707907477717510552840661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19775506547826722948483525 3707907477717510552840661)
                      ·
                        rfl

theorem cell23_7221124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_7221124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221124 prefixEnd_7221124 := by exact prefixLift 7221124
  have htrace : WordTrace (prefixWord ++ tailWord_7221124) baseStart_7221124 baseEnd_7221124 := by
    simpa [prefixWord, tailWord_7221124, baseEnd_7221124] using wordTrace_append hprefix tailTrace_7221124
  have hstable : (prefixWord ++ tailWord_7221124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221124).length < 2 ^ (prefixWord ++ tailWord_7221124).sum := by decide
  have hdescent : baseEnd_7221124 < baseStart_7221124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221181 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 7]
def baseStart_7221181 : Nat := 118140960795 + 7221181 * 2 ^ 59
def prefixEnd_7221181 : Nat := 4983230072969 + 3 ^ 40 * 7221181 * 2
def baseEnd_7221181 : Nat := 411992971790535203314211

theorem tailTrace_7221181 : CollatzResearch.WordTrace tailWord_7221181 prefixEnd_7221181 411992971790535203314211 := by
  unfold tailWord_7221181
  simp only [CollatzResearch.WordTrace]
  refine ⟨263378108451901991373511397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175585405634601327582340931 263378108451901991373511397)
  ·
    refine ⟨49383395334731623382533387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263378108451901991373511397 49383395334731623382533387)
    ·
      refine ⟨74075093002097435073800081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49383395334731623382533387 74075093002097435073800081)
      ·
        refine ⟨55556319751573076305350061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74075093002097435073800081 55556319751573076305350061)
        ·
          refine ⟨20833619906839903614506273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55556319751573076305350061 20833619906839903614506273)
          ·
            refine ⟨15625214930129927710879705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20833619906839903614506273 15625214930129927710879705)
            ·
              refine ⟨11718911197597445783159779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15625214930129927710879705 11718911197597445783159779)
              ·
                refine ⟨17578366796396168674739669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718911197597445783159779 17578366796396168674739669)
                ·
                  refine ⟨411992971790535203314211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17578366796396168674739669 411992971790535203314211)
                  ·
                    rfl

theorem cell23_7221181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_7221181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221181 prefixEnd_7221181 := by exact prefixLift 7221181
  have htrace : WordTrace (prefixWord ++ tailWord_7221181) baseStart_7221181 baseEnd_7221181 := by
    simpa [prefixWord, tailWord_7221181, baseEnd_7221181] using wordTrace_append hprefix tailTrace_7221181
  have hstable : (prefixWord ++ tailWord_7221181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221181).length < 2 ^ (prefixWord ++ tailWord_7221181).sum := by decide
  have hdescent : baseEnd_7221181 < baseStart_7221181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221192 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_7221192 : Nat := 118140960795 + 7221192 * 2 ^ 59
def prefixEnd_7221192 : Nat := 4983230072969 + 3 ^ 40 * 7221192 * 2
def baseEnd_7221192 : Nat := 3707942394402016286790349

theorem tailTrace_7221192 : CollatzResearch.WordTrace tailWord_7221192 prefixEnd_7221192 3707942394402016286790349 := by
  unfold tailWord_7221192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131689254827431070126080915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175585673103241426834774553 131689254827431070126080915)
  ·
    refine ⟨197533882241146605189121373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131689254827431070126080915 197533882241146605189121373)
    ·
      refine ⟨74075205840429976945920515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197533882241146605189121373 74075205840429976945920515)
      ·
        refine ⟨111112808760644965418880773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74075205840429976945920515 111112808760644965418880773)
        ·
          refine ⟨20833651642620931016040145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111112808760644965418880773 20833651642620931016040145)
          ·
            refine ⟨15625238731965698262030109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20833651642620931016040145 15625238731965698262030109)
            ·
              refine ⟨5859464524487136848261291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15625238731965698262030109 5859464524487136848261291)
              ·
                refine ⟨8789196786730705272391937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859464524487136848261291 8789196786730705272391937)
                ·
                  refine ⟨6591897590048028954293953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8789196786730705272391937 6591897590048028954293953)
                  ·
                    refine ⟨4943923192536021715720465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6591897590048028954293953 4943923192536021715720465)
                    ·
                      refine ⟨3707942394402016286790349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4943923192536021715720465 3707942394402016286790349)
                      ·
                        rfl

theorem cell23_7221192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_7221192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221192 prefixEnd_7221192 := by exact prefixLift 7221192
  have htrace : WordTrace (prefixWord ++ tailWord_7221192) baseStart_7221192 baseEnd_7221192 := by
    simpa [prefixWord, tailWord_7221192, baseEnd_7221192] using wordTrace_append hprefix tailTrace_7221192
  have hstable : (prefixWord ++ tailWord_7221192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221192).length < 2 ^ (prefixWord ++ tailWord_7221192).sum := by decide
  have hdescent : baseEnd_7221192 < baseStart_7221192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221194 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_7221194 : Nat := 118140960795 + 7221194 * 2 ^ 59
def prefixEnd_7221194 : Nat := 4983230072969 + 3 ^ 40 * 7221194 * 2
def baseEnd_7221194 : Nat := 1235981140454441759655113

theorem tailTrace_7221194 : CollatzResearch.WordTrace tailWord_7221194 prefixEnd_7221194 1235981140454441759655113 := by
  unfold tailWord_7221194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65844645650213723648433659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175585721733903263062489757 65844645650213723648433659)
  ·
    refine ⟨98766968475320585472650489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65844645650213723648433659 98766968475320585472650489)
    ·
      refine ⟨74075226356490439104487867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98766968475320585472650489 74075226356490439104487867)
      ·
        refine ⟨111112839534735658656731801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74075226356490439104487867 111112839534735658656731801)
        ·
          refine ⟨83334629651051743992548851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111112839534735658656731801 83334629651051743992548851)
          ·
            refine ⟨125001944476577615988823277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83334629651051743992548851 125001944476577615988823277)
            ·
              refine ⟨46875729178716605995808729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125001944476577615988823277 46875729178716605995808729)
              ·
                refine ⟨35156796884037454496856547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46875729178716605995808729 35156796884037454496856547)
                ·
                  refine ⟨52735195326056181745284821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35156796884037454496856547 52735195326056181745284821)
                  ·
                    refine ⟨1235981140454441759655113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52735195326056181745284821 1235981140454441759655113)
                    ·
                      rfl

theorem cell23_7221194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_7221194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221194 prefixEnd_7221194 := by exact prefixLift 7221194
  have htrace : WordTrace (prefixWord ++ tailWord_7221194) baseStart_7221194 baseEnd_7221194 := by
    simpa [prefixWord, tailWord_7221194, baseEnd_7221194] using wordTrace_append hprefix tailTrace_7221194
  have hstable : (prefixWord ++ tailWord_7221194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221194).length < 2 ^ (prefixWord ++ tailWord_7221194).sum := by decide
  have hdescent : baseEnd_7221194 < baseStart_7221194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221231 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_7221231 : Nat := 118140960795 + 7221231 * 2 ^ 59
def prefixEnd_7221231 : Nat := 4983230072969 + 3 ^ 40 * 7221231 * 2
def baseEnd_7221231 : Nat := 3707962420147541634202669

theorem tailTrace_7221231 : CollatzResearch.WordTrace tailWord_7221231 prefixEnd_7221231 3707962420147541634202669 := by
  unfold tailWord_7221231
  simp only [CollatzResearch.WordTrace]
  refine ⟨263379932101720849912831547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175586621401147233275221031 263379932101720849912831547)
  ·
    refine ⟨395069898152581274869247321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263379932101720849912831547 395069898152581274869247321)
    ·
      refine ⟨296302423614435956151935491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395069898152581274869247321 296302423614435956151935491)
      ·
        refine ⟨444453635421653934227903237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296302423614435956151935491 444453635421653934227903237)
        ·
          refine ⟨83335056641560112667731857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444453635421653934227903237 83335056641560112667731857)
          ·
            refine ⟨62501292481170084500798893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83335056641560112667731857 62501292481170084500798893)
            ·
              refine ⟨23437984680438781687799585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62501292481170084500798893 23437984680438781687799585)
              ·
                refine ⟨17578488510329086265849689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23437984680438781687799585 17578488510329086265849689)
                ·
                  refine ⟨13183866382746814699387267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17578488510329086265849689 13183866382746814699387267)
                  ·
                    refine ⟨19775799574120222049080901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13183866382746814699387267 19775799574120222049080901)
                    ·
                      refine ⟨3707962420147541634202669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19775799574120222049080901 3707962420147541634202669)
                      ·
                        rfl

theorem cell23_7221231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_7221231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221231 prefixEnd_7221231 := by exact prefixLift 7221231
  have htrace : WordTrace (prefixWord ++ tailWord_7221231) baseStart_7221231 baseEnd_7221231 := by
    simpa [prefixWord, tailWord_7221231, baseEnd_7221231] using wordTrace_append hprefix tailTrace_7221231
  have hstable : (prefixWord ++ tailWord_7221231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221231).length < 2 ^ (prefixWord ++ tailWord_7221231).sum := by decide
  have hdescent : baseEnd_7221231 < baseStart_7221231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221238 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_7221238 : Nat := 118140960795 + 7221238 * 2 ^ 59
def prefixEnd_7221238 : Nat := 4983230072969 + 3 ^ 40 * 7221238 * 2
def baseEnd_7221238 : Nat := 3707966014512123106815137

theorem tailTrace_7221238 : CollatzResearch.WordTrace tailWord_7221238 prefixEnd_7221238 3707966014512123106815137 := by
  unfold tailWord_7221238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16461261713293468131771023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175586791608463660072224245 16461261713293468131771023)
  ·
    refine ⟨24691892569940202197656535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16461261713293468131771023 24691892569940202197656535)
    ·
      refine ⟨37037838854910303296484803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24691892569940202197656535 37037838854910303296484803)
      ·
        refine ⟨55556758282365454944727205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37037838854910303296484803 55556758282365454944727205)
        ·
          refine ⟨10416892177943522802136351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55556758282365454944727205 10416892177943522802136351)
          ·
            refine ⟨15625338266915284203204527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10416892177943522802136351 15625338266915284203204527)
            ·
              refine ⟨23438007400372926304806791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15625338266915284203204527 23438007400372926304806791)
              ·
                refine ⟨35157011100559389457210187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23438007400372926304806791 35157011100559389457210187)
                ·
                  refine ⟨52735516650839084185815281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35157011100559389457210187 52735516650839084185815281)
                  ·
                    refine ⟨39551637488129313139361461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52735516650839084185815281 39551637488129313139361461)
                    ·
                      refine ⟨3707966014512123106815137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39551637488129313139361461 3707966014512123106815137)
                      ·
                        rfl

theorem cell23_7221238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_7221238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221238 prefixEnd_7221238 := by exact prefixLift 7221238
  have htrace : WordTrace (prefixWord ++ tailWord_7221238) baseStart_7221238 baseEnd_7221238 := by
    simpa [prefixWord, tailWord_7221238, baseEnd_7221238] using wordTrace_append hprefix tailTrace_7221238
  have hstable : (prefixWord ++ tailWord_7221238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221238).length < 2 ^ (prefixWord ++ tailWord_7221238).sum := by decide
  have hdescent : baseEnd_7221238 < baseStart_7221238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221301 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7221301 : Nat := 118140960795 + 7221301 * 2 ^ 59
def prefixEnd_7221301 : Nat := 4983230072969 + 3 ^ 40 * 7221301 * 2
def baseEnd_7221301 : Nat := 1235999454597785453442449

theorem tailTrace_7221301 : CollatzResearch.WordTrace tailWord_7221301 prefixEnd_7221301 1235999454597785453442449 := by
  unfold tailWord_7221301
  simp only [CollatzResearch.WordTrace]
  refine ⟨263382485211467251867879757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175588323474311501245253171 263382485211467251867879757)
  ·
    refine ⟨98768431954300219450454909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263382485211467251867879757 98768431954300219450454909)
    ·
      refine ⟨37038161982862582293920591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98768431954300219450454909 37038161982862582293920591)
      ·
        refine ⟨55557242974293873440880887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37038161982862582293920591 55557242974293873440880887)
        ·
          refine ⟨83335864461440810161321331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55557242974293873440880887 83335864461440810161321331)
          ·
            refine ⟨125003796692161215241981997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83335864461440810161321331 125003796692161215241981997)
            ·
              refine ⟨46876423759560455715743249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125003796692161215241981997 46876423759560455715743249)
              ·
                refine ⟨35157317819670341786807437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46876423759560455715743249 35157317819670341786807437)
                ·
                  refine ⟨13183994182376378170052789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35157317819670341786807437 13183994182376378170052789)
                  ·
                    refine ⟨1235999454597785453442449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13183994182376378170052789 1235999454597785453442449)
                    ·
                      rfl

theorem cell23_7221301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7221301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221301 prefixEnd_7221301 := by exact prefixLift 7221301
  have htrace : WordTrace (prefixWord ++ tailWord_7221301) baseStart_7221301 baseEnd_7221301 := by
    simpa [prefixWord, tailWord_7221301, baseEnd_7221301] using wordTrace_append hprefix tailTrace_7221301
  have hstable : (prefixWord ++ tailWord_7221301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221301).length < 2 ^ (prefixWord ++ tailWord_7221301).sum := by decide
  have hdescent : baseEnd_7221301 < baseStart_7221301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221308 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_7221308 : Nat := 118140960795 + 7221308 * 2 ^ 59
def prefixEnd_7221308 : Nat := 4983230072969 + 3 ^ 40 * 7221308 * 2
def baseEnd_7221308 : Nat := 3708001958157937832939815

theorem tailTrace_7221308 : CollatzResearch.WordTrace tailWord_7221308 prefixEnd_7221308 3708001958157937832939815 := by
  unfold tailWord_7221308
  simp only [CollatzResearch.WordTrace]
  refine ⟨131691370261220946031692289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175588493681627928042256385 131691370261220946031692289)
  ·
    refine ⟨98768527695915709523769217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131691370261220946031692289 98768527695915709523769217)
    ·
      refine ⟨74076395771936782142826913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98768527695915709523769217 74076395771936782142826913)
      ·
        refine ⟨55557296828952586607120185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74076395771936782142826913 55557296828952586607120185)
        ·
          refine ⟨41667972621714439955340139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55557296828952586607120185 41667972621714439955340139)
          ·
            refine ⟨62501958932571659933010209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41667972621714439955340139 62501958932571659933010209)
            ·
              refine ⟨46876469199428744949757657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62501958932571659933010209 46876469199428744949757657)
              ·
                refine ⟨35157351899571558712318243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46876469199428744949757657 35157351899571558712318243)
                ·
                  refine ⟨52736027849357338068477365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35157351899571558712318243 52736027849357338068477365)
                  ·
                    refine ⟨4944002610877250443919753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52736027849357338068477365 4944002610877250443919753)
                    ·
                      refine ⟨3708001958157937832939815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944002610877250443919753 3708001958157937832939815)
                      ·
                        rfl

theorem cell23_7221308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_7221308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221308 prefixEnd_7221308 := by exact prefixLift 7221308
  have htrace : WordTrace (prefixWord ++ tailWord_7221308) baseStart_7221308 baseEnd_7221308 := by
    simpa [prefixWord, tailWord_7221308, baseEnd_7221308] using wordTrace_append hprefix tailTrace_7221308
  have hstable : (prefixWord ++ tailWord_7221308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221308).length < 2 ^ (prefixWord ++ tailWord_7221308).sum := by decide
  have hdescent : baseEnd_7221308 < baseStart_7221308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221321 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_7221321 : Nat := 118140960795 + 7221321 * 2 ^ 59
def prefixEnd_7221321 : Nat := 4983230072969 + 3 ^ 40 * 7221321 * 2
def baseEnd_7221321 : Nat := 3708008633406446282077255

theorem tailTrace_7221321 : CollatzResearch.WordTrace tailWord_7221321 prefixEnd_7221321 3708008633406446282077255 := by
  unfold tailWord_7221321
  simp only [CollatzResearch.WordTrace]
  refine ⟨263383214671394795283607817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175588809780929863522405211 263383214671394795283607817)
  ·
    refine ⟨197537411003546096462705863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263383214671394795283607817 197537411003546096462705863)
    ·
      refine ⟨296306116505319144694058795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197537411003546096462705863 296306116505319144694058795)
      ·
        refine ⟨444459174757978717041088193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296306116505319144694058795 444459174757978717041088193)
        ·
          refine ⟨333344381068484037780816145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444459174757978717041088193 333344381068484037780816145)
          ·
            refine ⟨250008285801363028335612109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333344381068484037780816145 250008285801363028335612109)
            ·
              refine ⟨93753107175511135625854541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250008285801363028335612109 93753107175511135625854541)
              ·
                refine ⟨35157415190816675859695453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93753107175511135625854541 35157415190816675859695453)
                ·
                  refine ⟨13184030696556253447385795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35157415190816675859695453 13184030696556253447385795)
                  ·
                    refine ⟨19776046044834380171078693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13184030696556253447385795 19776046044834380171078693)
                    ·
                      refine ⟨3708008633406446282077255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19776046044834380171078693 3708008633406446282077255)
                      ·
                        rfl

theorem cell23_7221321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_7221321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221321 prefixEnd_7221321 := by exact prefixLift 7221321
  have htrace : WordTrace (prefixWord ++ tailWord_7221321) baseStart_7221321 baseEnd_7221321 := by
    simpa [prefixWord, tailWord_7221321, baseEnd_7221321] using wordTrace_append hprefix tailTrace_7221321
  have hstable : (prefixWord ++ tailWord_7221321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221321).length < 2 ^ (prefixWord ++ tailWord_7221321).sum := by decide
  have hdescent : baseEnd_7221321 < baseStart_7221321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221325 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_7221325 : Nat := 118140960795 + 7221325 * 2 ^ 59
def prefixEnd_7221325 : Nat := 4983230072969 + 3 ^ 40 * 7221325 * 2
def baseEnd_7221325 : Nat := 3708010687329064266427237

theorem tailTrace_7221325 : CollatzResearch.WordTrace tailWord_7221325 prefixEnd_7221325 3708010687329064266427237 := by
  unfold tailWord_7221325
  simp only [CollatzResearch.WordTrace]
  refine ⟨263383360563380303966753429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175588907042253535977835619 263383360563380303966753429)
  ·
    refine ⟨12346095026408451748441567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263383360563380303966753429 12346095026408451748441567)
    ·
      refine ⟨18519142539612677622662351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346095026408451748441567 18519142539612677622662351)
      ·
        refine ⟨27778713809419016433993527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18519142539612677622662351 27778713809419016433993527)
        ·
          refine ⟨41668070714128524650990291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27778713809419016433993527 41668070714128524650990291)
          ·
            refine ⟨62502106071192786976485437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41668070714128524650990291 62502106071192786976485437)
            ·
              refine ⟨23438289776697295116182039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62502106071192786976485437 23438289776697295116182039)
              ·
                refine ⟨35157434665045942674273059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23438289776697295116182039 35157434665045942674273059)
                ·
                  refine ⟨52736151997568914011409589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35157434665045942674273059 52736151997568914011409589)
                  ·
                    refine ⟨4944014249772085688569649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52736151997568914011409589 4944014249772085688569649)
                    ·
                      refine ⟨3708010687329064266427237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944014249772085688569649 3708010687329064266427237)
                      ·
                        rfl

theorem cell23_7221325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_7221325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221325 prefixEnd_7221325 := by exact prefixLift 7221325
  have htrace : WordTrace (prefixWord ++ tailWord_7221325) baseStart_7221325 baseEnd_7221325 := by
    simpa [prefixWord, tailWord_7221325, baseEnd_7221325] using wordTrace_append hprefix tailTrace_7221325
  have hstable : (prefixWord ++ tailWord_7221325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221325).length < 2 ^ (prefixWord ++ tailWord_7221325).sum := by decide
  have hdescent : baseEnd_7221325 < baseStart_7221325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221338 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_7221338 : Nat := 118140960795 + 7221338 * 2 ^ 59
def prefixEnd_7221338 : Nat := 4983230072969 + 3 ^ 40 * 7221338 * 2
def baseEnd_7221338 : Nat := 3708017362577572715564677

theorem tailTrace_7221338 : CollatzResearch.WordTrace tailWord_7221338 prefixEnd_7221338 3708017362577572715564677 := by
  unfold tailWord_7221338
  simp only [CollatzResearch.WordTrace]
  refine ⟨65845958678083301796744167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175589223141555471457984445 65845958678083301796744167)
  ·
    refine ⟨98768938017124952695116251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65845958678083301796744167 98768938017124952695116251)
    ·
      refine ⟨148153407025687429042674377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98768938017124952695116251 148153407025687429042674377)
      ·
        refine ⟨111115055269265571782005783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148153407025687429042674377 111115055269265571782005783)
        ·
          refine ⟨166672582903898357673008675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111115055269265571782005783 166672582903898357673008675)
          ·
            refine ⟨250008874355847536509513013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166672582903898357673008675 250008874355847536509513013)
            ·
              refine ⟨23438331970860706547766845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250008874355847536509513013 23438331970860706547766845)
              ·
                refine ⟨8789374489072764955412567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23438331970860706547766845 8789374489072764955412567)
                ·
                  refine ⟨13184061733609147433118851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8789374489072764955412567 13184061733609147433118851)
                  ·
                    refine ⟨19776092600413721149678277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13184061733609147433118851 19776092600413721149678277)
                    ·
                      refine ⟨3708017362577572715564677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19776092600413721149678277 3708017362577572715564677)
                      ·
                        rfl

theorem cell23_7221338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_7221338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221338 prefixEnd_7221338 := by exact prefixLift 7221338
  have htrace : WordTrace (prefixWord ++ tailWord_7221338) baseStart_7221338 baseEnd_7221338 := by
    simpa [prefixWord, tailWord_7221338, baseEnd_7221338] using wordTrace_append hprefix tailTrace_7221338
  have hstable : (prefixWord ++ tailWord_7221338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221338).length < 2 ^ (prefixWord ++ tailWord_7221338).sum := by decide
  have hdescent : baseEnd_7221338 < baseStart_7221338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221351 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_7221351 : Nat := 118140960795 + 7221351 * 2 ^ 59
def prefixEnd_7221351 : Nat := 4983230072969 + 3 ^ 40 * 7221351 * 2
def baseEnd_7221351 : Nat := 3708024037826081164702117

theorem tailTrace_7221351 : CollatzResearch.WordTrace tailWord_7221351 prefixEnd_7221351 3708024037826081164702117 := by
  unfold tailWord_7221351
  simp only [CollatzResearch.WordTrace]
  refine ⟨263384308861286110407199907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175589539240857406938133271 263384308861286110407199907)
  ·
    refine ⟨395076463291929165610799861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263384308861286110407199907 395076463291929165610799861)
    ·
      refine ⟨37038418433618359276012487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 395076463291929165610799861 37038418433618359276012487)
      ·
        refine ⟨55557627650427538914018731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37038418433618359276012487 55557627650427538914018731)
        ·
          refine ⟨83336441475641308371028097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55557627650427538914018731 83336441475641308371028097)
          ·
            refine ⟨62502331106730981278271073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83336441475641308371028097 62502331106730981278271073)
            ·
              refine ⟨46876748330048235958703305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62502331106730981278271073 46876748330048235958703305)
              ·
                refine ⟨35157561247536176969027479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46876748330048235958703305 35157561247536176969027479)
                ·
                  refine ⟨52736341871304265453541219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35157561247536176969027479 52736341871304265453541219)
                  ·
                    refine ⟨79104512806956398180311829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52736341871304265453541219 79104512806956398180311829)
                    ·
                      refine ⟨3708024037826081164702117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79104512806956398180311829 3708024037826081164702117)
                      ·
                        rfl

theorem cell23_7221351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_7221351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221351 prefixEnd_7221351 := by exact prefixLift 7221351
  have htrace : WordTrace (prefixWord ++ tailWord_7221351) baseStart_7221351 baseEnd_7221351 := by
    simpa [prefixWord, tailWord_7221351, baseEnd_7221351] using wordTrace_append hprefix tailTrace_7221351
  have hstable : (prefixWord ++ tailWord_7221351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221351).length < 2 ^ (prefixWord ++ tailWord_7221351).sum := by decide
  have hdescent : baseEnd_7221351 < baseStart_7221351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221358 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7221358 : Nat := 118140960795 + 7221358 * 2 ^ 59
def prefixEnd_7221358 : Nat := 4983230072969 + 3 ^ 40 * 7221358 * 2
def baseEnd_7221358 : Nat := 3708027632190662637314585

theorem tailTrace_7221358 : CollatzResearch.WordTrace tailWord_7221358 prefixEnd_7221358 3708027632190662637314585 := by
  unfold tailWord_7221358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32923070521532593825338091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175589709448173833735136485 32923070521532593825338091)
  ·
    refine ⟨49384605782298890738007137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32923070521532593825338091 49384605782298890738007137)
    ·
      refine ⟨37038454336724168053505353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49384605782298890738007137 37038454336724168053505353)
      ·
        refine ⟨27778840752543126040129015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37038454336724168053505353 27778840752543126040129015)
        ·
          refine ⟨41668261128814689060193523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27778840752543126040129015 41668261128814689060193523)
          ·
            refine ⟨62502391693222033590290285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41668261128814689060193523 62502391693222033590290285)
            ·
              refine ⟨23438396884958262596358857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62502391693222033590290285 23438396884958262596358857)
              ·
                refine ⟨17578797663718696947269143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23438396884958262596358857 17578797663718696947269143)
                ·
                  refine ⟨26368196495578045420903715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17578797663718696947269143 26368196495578045420903715)
                  ·
                    refine ⟨39552294743367068131355573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26368196495578045420903715 39552294743367068131355573)
                    ·
                      refine ⟨3708027632190662637314585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39552294743367068131355573 3708027632190662637314585)
                      ·
                        rfl

theorem cell23_7221358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7221358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221358 prefixEnd_7221358 := by exact prefixLift 7221358
  have htrace : WordTrace (prefixWord ++ tailWord_7221358) baseStart_7221358 baseEnd_7221358 := by
    simpa [prefixWord, tailWord_7221358, baseEnd_7221358] using wordTrace_append hprefix tailTrace_7221358
  have hstable : (prefixWord ++ tailWord_7221358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221358).length < 2 ^ (prefixWord ++ tailWord_7221358).sum := by decide
  have hdescent : baseEnd_7221358 < baseStart_7221358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221405 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_7221405 : Nat := 118140960795 + 7221405 * 2 ^ 59
def prefixEnd_7221405 : Nat := 4983230072969 + 3 ^ 40 * 7221405 * 2
def baseEnd_7221405 : Nat := 3708051765781423953426869

theorem tailTrace_7221405 : CollatzResearch.WordTrace tailWord_7221405 prefixEnd_7221405 3708051765781423953426869 := by
  unfold tailWord_7221405
  simp only [CollatzResearch.WordTrace]
  refine ⟨263386278403090477629665669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175590852268726985086443779 263386278403090477629665669)
  ·
    refine ⟨49384927200579464555562313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263386278403090477629665669 49384927200579464555562313)
    ·
      refine ⟨37038695400434598416671735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49384927200579464555562313 37038695400434598416671735)
      ·
        refine ⟨55558043100651897625007603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37038695400434598416671735 55558043100651897625007603)
        ·
          refine ⟨83337064650977846437511405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55558043100651897625007603 83337064650977846437511405)
          ·
            refine ⟨31251399244116692414066777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83337064650977846437511405 31251399244116692414066777)
            ·
              refine ⟨23438549433087519310550083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31251399244116692414066777 23438549433087519310550083)
              ·
                refine ⟨35157824149631278965825125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23438549433087519310550083 35157824149631278965825125)
                ·
                  refine ⟨6592092028055864806092211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35157824149631278965825125 6592092028055864806092211)
                  ·
                    refine ⟨9888138042083797209138317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6592092028055864806092211 9888138042083797209138317)
                    ·
                      refine ⟨3708051765781423953426869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9888138042083797209138317 3708051765781423953426869)
                      ·
                        rfl

theorem cell23_7221405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_7221405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221405 prefixEnd_7221405 := by exact prefixLift 7221405
  have htrace : WordTrace (prefixWord ++ tailWord_7221405) baseStart_7221405 baseEnd_7221405 := by
    simpa [prefixWord, tailWord_7221405, baseEnd_7221405] using wordTrace_append hprefix tailTrace_7221405
  have hstable : (prefixWord ++ tailWord_7221405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221405).length < 2 ^ (prefixWord ++ tailWord_7221405).sum := by decide
  have hdescent : baseEnd_7221405 < baseStart_7221405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221406 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_7221406 : Nat := 118140960795 + 7221406 * 2 ^ 59
def prefixEnd_7221406 : Nat := 4983230072969 + 3 ^ 40 * 7221406 * 2
def baseEnd_7221406 : Nat := 3708052279262078449514365

theorem tailTrace_7221406 : CollatzResearch.WordTrace tailWord_7221406 prefixEnd_7221406 3708052279262078449514365 := by
  unfold tailWord_7221406
  simp only [CollatzResearch.WordTrace]
  refine ⟨32923289359510856850056509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175590876584057903200301381 32923289359510856850056509)
  ·
    refine ⟨12346233509816571318771191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32923289359510856850056509 12346233509816571318771191)
    ·
      refine ⟨18519350264724856978156787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346233509816571318771191 18519350264724856978156787)
      ·
        refine ⟨27779025397087285467235181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18519350264724856978156787 27779025397087285467235181)
        ·
          refine ⟨10417134523907732050213193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27779025397087285467235181 10417134523907732050213193)
          ·
            refine ⟨7812850892930799037659895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10417134523907732050213193 7812850892930799037659895)
            ·
              refine ⟨11719276339396198556489843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812850892930799037659895 11719276339396198556489843)
              ·
                refine ⟨17578914509094297834734765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11719276339396198556489843 17578914509094297834734765)
                ·
                  refine ⟨6592092940910361688025537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17578914509094297834734765 6592092940910361688025537)
                  ·
                    refine ⟨4944069705682771266019153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592092940910361688025537 4944069705682771266019153)
                    ·
                      refine ⟨3708052279262078449514365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944069705682771266019153 3708052279262078449514365)
                      ·
                        rfl

theorem cell23_7221406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_7221406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221406 prefixEnd_7221406 := by exact prefixLift 7221406
  have htrace : WordTrace (prefixWord ++ tailWord_7221406) baseStart_7221406 baseEnd_7221406 := by
    simpa [prefixWord, tailWord_7221406, baseEnd_7221406] using wordTrace_append hprefix tailTrace_7221406
  have hstable : (prefixWord ++ tailWord_7221406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221406).length < 2 ^ (prefixWord ++ tailWord_7221406).sum := by decide
  have hdescent : baseEnd_7221406 < baseStart_7221406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221445 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 6, 2, 2]
def baseStart_7221445 : Nat := 118140960795 + 7221445 * 2 ^ 59
def prefixEnd_7221445 : Nat := 4983230072969 + 3 ^ 40 * 7221445 * 2
def baseEnd_7221445 : Nat := 3708072305007603796926685

theorem tailTrace_7221445 : CollatzResearch.WordTrace tailWord_7221445 prefixEnd_7221445 3708072305007603796926685 := by
  unfold tailWord_7221445
  simp only [CollatzResearch.WordTrace]
  refine ⟨263387737322945564461121789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175591824881963709640747859 263387737322945564461121789)
  ·
    refine ⟨98770401496104586672920671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263387737322945564461121789 98770401496104586672920671)
    ·
      refine ⟨148155602244156880009381007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98770401496104586672920671 148155602244156880009381007)
      ·
        refine ⟨222233403366235320014071511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148155602244156880009381007 222233403366235320014071511)
        ·
          refine ⟨333350105049352980021107267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222233403366235320014071511 333350105049352980021107267)
          ·
            refine ⟨500025157574029470031660901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333350105049352980021107267 500025157574029470031660901)
            ·
              refine ⟨93754717045130525630936419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 500025157574029470031660901 93754717045130525630936419)
              ·
                refine ⟨140632075567695788446404629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93754717045130525630936419 140632075567695788446404629)
                ·
                  refine ⟨6592128542235740083425217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140632075567695788446404629 6592128542235740083425217)
                  ·
                    refine ⟨4944096406676805062568913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592128542235740083425217 4944096406676805062568913)
                    ·
                      refine ⟨3708072305007603796926685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944096406676805062568913 3708072305007603796926685)
                      ·
                        rfl

theorem cell23_7221445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_7221445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221445 prefixEnd_7221445 := by exact prefixLift 7221445
  have htrace : WordTrace (prefixWord ++ tailWord_7221445) baseStart_7221445 baseEnd_7221445 := by
    simpa [prefixWord, tailWord_7221445, baseEnd_7221445] using wordTrace_append hprefix tailTrace_7221445
  have hstable : (prefixWord ++ tailWord_7221445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221445).length < 2 ^ (prefixWord ++ tailWord_7221445).sum := by decide
  have hdescent : baseEnd_7221445 < baseStart_7221445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221471 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_7221471 : Nat := 118140960795 + 7221471 * 2 ^ 59
def prefixEnd_7221471 : Nat := 4983230072969 + 3 ^ 40 * 7221471 * 2
def baseEnd_7221471 : Nat := 3708085655504620695201565

theorem tailTrace_7221471 : CollatzResearch.WordTrace tailWord_7221471 prefixEnd_7221471 3708085655504620695201565 := by
  unfold tailWord_7221471
  simp only [CollatzResearch.WordTrace]
  refine ⟨263388685620851370901568267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175592457080567580601045511 263388685620851370901568267)
  ·
    refine ⟨395083028431277056352352401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263388685620851370901568267 395083028431277056352352401)
    ·
      refine ⟨296312271323457792264264301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395083028431277056352352401 296312271323457792264264301)
      ·
        refine ⟨111117101746296672099099113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296312271323457792264264301 111117101746296672099099113)
        ·
          refine ⟨83337826309722504074324335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111117101746296672099099113 83337826309722504074324335)
          ·
            refine ⟨125006739464583756111486503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83337826309722504074324335 125006739464583756111486503)
            ·
              refine ⟨187510109196875634167229755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125006739464583756111486503 187510109196875634167229755)
              ·
                refine ⟨281265163795313451250844633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187510109196875634167229755 281265163795313451250844633)
                ·
                  refine ⟨210948872846485088438133475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281265163795313451250844633 210948872846485088438133475)
                  ·
                    refine ⟨316423309269727632657200213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210948872846485088438133475 316423309269727632657200213)
                    ·
                      refine ⟨3708085655504620695201565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 316423309269727632657200213 3708085655504620695201565)
                      ·
                        rfl

theorem cell23_7221471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_7221471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221471 prefixEnd_7221471 := by exact prefixLift 7221471
  have htrace : WordTrace (prefixWord ++ tailWord_7221471) baseStart_7221471 baseEnd_7221471 := by
    simpa [prefixWord, tailWord_7221471, baseEnd_7221471] using wordTrace_append hprefix tailTrace_7221471
  have hstable : (prefixWord ++ tailWord_7221471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221471).length < 2 ^ (prefixWord ++ tailWord_7221471).sum := by decide
  have hdescent : baseEnd_7221471 < baseStart_7221471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221479 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7221479 : Nat := 118140960795 + 7221479 * 2 ^ 59
def prefixEnd_7221479 : Nat := 4983230072969 + 3 ^ 40 * 7221479 * 2
def baseEnd_7221479 : Nat := 3708089763349856663901529

theorem tailTrace_7221479 : CollatzResearch.WordTrace tailWord_7221479 prefixEnd_7221479 3708089763349856663901529 := by
  unfold tailWord_7221479
  simp only [CollatzResearch.WordTrace]
  refine ⟨263388977404822388267859491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175592651603214925511906327 263388977404822388267859491)
  ·
    refine ⟨395083466107233582401789237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263388977404822388267859491 395083466107233582401789237)
    ·
      refine ⟨37039074947553148350167741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 395083466107233582401789237 37039074947553148350167741)
      ·
        refine ⟨13889653105332430631312903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37039074947553148350167741 13889653105332430631312903)
        ·
          refine ⟨20834479657998645946969355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13889653105332430631312903 20834479657998645946969355)
          ·
            refine ⟨31251719486997968920454033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20834479657998645946969355 31251719486997968920454033)
            ·
              refine ⟨23438789615248476690340525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31251719486997968920454033 23438789615248476690340525)
              ·
                refine ⟨8789546105718178758877697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23438789615248476690340525 8789546105718178758877697)
                ·
                  refine ⟨6592159579288634069158273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8789546105718178758877697 6592159579288634069158273)
                  ·
                    refine ⟨4944119684466475551868705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592159579288634069158273 4944119684466475551868705)
                    ·
                      refine ⟨3708089763349856663901529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944119684466475551868705 3708089763349856663901529)
                      ·
                        rfl

theorem cell23_7221479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7221479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221479 prefixEnd_7221479 := by exact prefixLift 7221479
  have htrace : WordTrace (prefixWord ++ tailWord_7221479) baseStart_7221479 baseEnd_7221479 := by
    simpa [prefixWord, tailWord_7221479, baseEnd_7221479] using wordTrace_append hprefix tailTrace_7221479
  have hstable : (prefixWord ++ tailWord_7221479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221479).length < 2 ^ (prefixWord ++ tailWord_7221479).sum := by decide
  have hdescent : baseEnd_7221479 < baseStart_7221479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221481 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_7221481 : Nat := 118140960795 + 7221481 * 2 ^ 59
def prefixEnd_7221481 : Nat := 4983230072969 + 3 ^ 40 * 7221481 * 2
def baseEnd_7221481 : Nat := 1236030263437055218692173

theorem tailTrace_7221481 : CollatzResearch.WordTrace tailWord_7221481 prefixEnd_7221481 1236030263437055218692173 := by
  unfold tailWord_7221481
  simp only [CollatzResearch.WordTrace]
  refine ⟨263389050350815142609432297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175592700233876761739621531 263389050350815142609432297)
  ·
    refine ⟨197541787763111356957074223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263389050350815142609432297 197541787763111356957074223)
    ·
      refine ⟨296312681644667035435611335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197541787763111356957074223 296312681644667035435611335)
      ·
        refine ⟨444469022467000553153417003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296312681644667035435611335 444469022467000553153417003)
        ·
          refine ⟨666703533700500829730125505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444469022467000553153417003 666703533700500829730125505)
          ·
            refine ⟨500027650275375622297594129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666703533700500829730125505 500027650275375622297594129)
            ·
              refine ⟨375020737706531716723195597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500027650275375622297594129 375020737706531716723195597)
              ·
                refine ⟨140632776639949393771198349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375020737706531716723195597 140632776639949393771198349)
                ·
                  refine ⟨52737291239981022664199381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140632776639949393771198349 52737291239981022664199381)
                  ·
                    refine ⟨1236030263437055218692173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52737291239981022664199381 1236030263437055218692173)
                    ·
                      rfl

theorem cell23_7221481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_7221481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221481 prefixEnd_7221481 := by exact prefixLift 7221481
  have htrace : WordTrace (prefixWord ++ tailWord_7221481) baseStart_7221481 baseEnd_7221481 := by
    simpa [prefixWord, tailWord_7221481, baseEnd_7221481] using wordTrace_append hprefix tailTrace_7221481
  have hstable : (prefixWord ++ tailWord_7221481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221481).length < 2 ^ (prefixWord ++ tailWord_7221481).sum := by decide
  have hdescent : baseEnd_7221481 < baseStart_7221481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221485 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 7]
def baseStart_7221485 : Nat := 118140960795 + 7221485 * 2 ^ 59
def prefixEnd_7221485 : Nat := 4983230072969 + 3 ^ 40 * 7221485 * 2
def baseEnd_7221485 : Nat := 412010316025975960047389

theorem tailTrace_7221485 : CollatzResearch.WordTrace tailWord_7221485 prefixEnd_7221485 412010316025975960047389 := by
  unfold tailWord_7221485
  simp only [CollatzResearch.WordTrace]
  refine ⟨263389196242800651292577909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175592797495200434195051939 263389196242800651292577909)
  ·
    refine ⟨24692737147762561058679179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263389196242800651292577909 24692737147762561058679179)
    ·
      refine ⟨37039105721643841588018769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24692737147762561058679179 37039105721643841588018769)
      ·
        refine ⟨27779329291232881191014077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37039105721643841588018769 27779329291232881191014077)
        ·
          refine ⟨10417248484212330446630279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27779329291232881191014077 10417248484212330446630279)
          ·
            refine ⟨15625872726318495669945419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10417248484212330446630279 15625872726318495669945419)
            ·
              refine ⟨23438809089477743504918129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15625872726318495669945419 23438809089477743504918129)
              ·
                refine ⟨17579106817108307628688597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23438809089477743504918129 17579106817108307628688597)
                ·
                  refine ⟨412010316025975960047389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17579106817108307628688597 412010316025975960047389)
                  ·
                    rfl

theorem cell23_7221485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_7221485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221485 prefixEnd_7221485 := by exact prefixLift 7221485
  have htrace : WordTrace (prefixWord ++ tailWord_7221485) baseStart_7221485 baseEnd_7221485 := by
    simpa [prefixWord, tailWord_7221485, baseEnd_7221485] using wordTrace_append hprefix tailTrace_7221485
  have hstable : (prefixWord ++ tailWord_7221485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221485).length < 2 ^ (prefixWord ++ tailWord_7221485).sum := by decide
  have hdescent : baseEnd_7221485 < baseStart_7221485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221498 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_7221498 : Nat := 118140960795 + 7221498 * 2 ^ 59
def prefixEnd_7221498 : Nat := 4983230072969 + 3 ^ 40 * 7221498 * 2
def baseEnd_7221498 : Nat := 1236033173160764029854647

theorem tailTrace_7221498 : CollatzResearch.WordTrace tailWord_7221498 prefixEnd_7221498 1236033173160764029854647 := by
  unfold tailWord_7221498
  simp only [CollatzResearch.WordTrace]
  refine ⟨65847417597938388628200287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175593113594502369675200765 65847417597938388628200287)
  ·
    refine ⟨98771126396907582942300431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65847417597938388628200287 98771126396907582942300431)
    ·
      refine ⟨148156689595361374413450647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98771126396907582942300431 148156689595361374413450647)
      ·
        refine ⟨222235034393042061620175971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148156689595361374413450647 222235034393042061620175971)
        ·
          refine ⟨333352551589563092430263957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222235034393042061620175971 333352551589563092430263957)
          ·
            refine ⟨15625900855760769957668623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 333352551589563092430263957 15625900855760769957668623)
            ·
              refine ⟨23438851283641154936502935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15625900855760769957668623 23438851283641154936502935)
              ·
                refine ⟨35158276925461732404754403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23438851283641154936502935 35158276925461732404754403)
                ·
                  refine ⟨52737415388192598607131605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35158276925461732404754403 52737415388192598607131605)
                  ·
                    refine ⟨1236033173160764029854647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52737415388192598607131605 1236033173160764029854647)
                    ·
                      rfl

theorem cell23_7221498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_7221498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221498 prefixEnd_7221498 := by exact prefixLift 7221498
  have htrace : WordTrace (prefixWord ++ tailWord_7221498) baseStart_7221498 baseEnd_7221498 := by
    simpa [prefixWord, tailWord_7221498, baseEnd_7221498] using wordTrace_append hprefix tailTrace_7221498
  have hstable : (prefixWord ++ tailWord_7221498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221498).length < 2 ^ (prefixWord ++ tailWord_7221498).sum := by decide
  have hdescent : baseEnd_7221498 < baseStart_7221498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221502 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_7221502 : Nat := 118140960795 + 7221502 * 2 ^ 59
def prefixEnd_7221502 : Nat := 4983230072969 + 3 ^ 40 * 7221502 * 2
def baseEnd_7221502 : Nat := 412011285933878897101547

theorem tailTrace_7221502 : CollatzResearch.WordTrace tailWord_7221502 prefixEnd_7221502 412011285933878897101547 := by
  unfold tailWord_7221502
  simp only [CollatzResearch.WordTrace]
  refine ⟨32923727035467382899493345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175593210855826042130631173 32923727035467382899493345)
  ·
    refine ⟨24692795276600537174620009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32923727035467382899493345 24692795276600537174620009)
    ·
      refine ⟨18519596457450402880965007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24692795276600537174620009 18519596457450402880965007)
      ·
        refine ⟨27779394686175604321447511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18519596457450402880965007 27779394686175604321447511)
        ·
          refine ⟨41669092029263406482171267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27779394686175604321447511 41669092029263406482171267)
          ·
            refine ⟨62503638043895109723256901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41669092029263406482171267 62503638043895109723256901)
            ·
              refine ⟨11719432133230333073110669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62503638043895109723256901 11719432133230333073110669)
              ·
                refine ⟨4394787049961374902416501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11719432133230333073110669 4394787049961374902416501)
                ·
                  refine ⟨412011285933878897101547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394787049961374902416501 412011285933878897101547)
                  ·
                    rfl

theorem cell23_7221502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_7221502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221502 prefixEnd_7221502 := by exact prefixLift 7221502
  have htrace : WordTrace (prefixWord ++ tailWord_7221502) baseStart_7221502 baseEnd_7221502 := by
    simpa [prefixWord, tailWord_7221502, baseEnd_7221502] using wordTrace_append hprefix tailTrace_7221502
  have hstable : (prefixWord ++ tailWord_7221502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221502).length < 2 ^ (prefixWord ++ tailWord_7221502).sum := by decide
  have hdescent : baseEnd_7221502 < baseStart_7221502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221555 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 3]
def baseStart_7221555 : Nat := 118140960795 + 7221555 * 2 ^ 59
def prefixEnd_7221555 : Nat := 4983230072969 + 3 ^ 40 * 7221555 * 2
def baseEnd_7221555 : Nat := 3708128787879598366551179

theorem tailTrace_7221555 : CollatzResearch.WordTrace tailWord_7221555 prefixEnd_7221555 3708128787879598366551179 := by
  unfold tailWord_7221555
  simp only [CollatzResearch.WordTrace]
  refine ⟨263391749352547053247626119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175594499568364702165084079 263391749352547053247626119)
  ·
    refine ⟨395087624028820579871439179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263391749352547053247626119 395087624028820579871439179)
    ·
      refine ⟨592631436043230869807158769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395087624028820579871439179 592631436043230869807158769)
      ·
        refine ⟨444473577032423152355369077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592631436043230869807158769 444473577032423152355369077)
        ·
          refine ⟨41669397846789670533315851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444473577032423152355369077 41669397846789670533315851)
          ·
            refine ⟨62504096770184505799973777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41669397846789670533315851 62504096770184505799973777)
            ·
              refine ⟨46878072577638379349980333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62504096770184505799973777 46878072577638379349980333)
              ·
                refine ⟨17579277216614392256242625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46878072577638379349980333 17579277216614392256242625)
                ·
                  refine ⟨13184457912460794192181969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17579277216614392256242625 13184457912460794192181969)
                  ·
                    refine ⟨9888343434345595644136477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13184457912460794192181969 9888343434345595644136477)
                    ·
                      refine ⟨3708128787879598366551179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9888343434345595644136477 3708128787879598366551179)
                      ·
                        rfl

theorem cell23_7221555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_7221555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221555 prefixEnd_7221555 := by exact prefixLift 7221555
  have htrace : WordTrace (prefixWord ++ tailWord_7221555) baseStart_7221555 baseEnd_7221555 := by
    simpa [prefixWord, tailWord_7221555, baseEnd_7221555] using wordTrace_append hprefix tailTrace_7221555
  have hstable : (prefixWord ++ tailWord_7221555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221555).length < 2 ^ (prefixWord ++ tailWord_7221555).sum := by decide
  have hdescent : baseEnd_7221555 < baseStart_7221555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221605 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_7221605 : Nat := 118140960795 + 7221605 * 2 ^ 59
def prefixEnd_7221605 : Nat := 4983230072969 + 3 ^ 40 * 7221605 * 2
def baseEnd_7221605 : Nat := 1236051487304107723641983

theorem tailTrace_7221605 : CollatzResearch.WordTrace tailWord_7221605 prefixEnd_7221605 1236051487304107723641983 := by
  unfold tailWord_7221605
  simp only [CollatzResearch.WordTrace]
  refine ⟨263393573002365911786946269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175595715334910607857964179 263393573002365911786946269)
  ·
    refine ⟨98772589875887216920104851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263393573002365911786946269 98772589875887216920104851)
    ·
      refine ⟨148158884813830825380157277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98772589875887216920104851 148158884813830825380157277)
      ·
        refine ⟨55559581805186559517558979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148158884813830825380157277 55559581805186559517558979)
        ·
          refine ⟨83339372707779839276338469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55559581805186559517558979 83339372707779839276338469)
          ·
            refine ⟨15626132382708719864313463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83339372707779839276338469 15626132382708719864313463)
            ·
              refine ⟨23439198574063079796470195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15626132382708719864313463 23439198574063079796470195)
              ·
                refine ⟨35158797861094619694705293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23439198574063079796470195 35158797861094619694705293)
                ·
                  refine ⟨13184549197910482385514485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35158797861094619694705293 13184549197910482385514485)
                  ·
                    refine ⟨1236051487304107723641983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13184549197910482385514485 1236051487304107723641983)
                    ·
                      rfl

theorem cell23_7221605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_7221605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221605 prefixEnd_7221605 := by exact prefixLift 7221605
  have htrace : WordTrace (prefixWord ++ tailWord_7221605) baseStart_7221605 baseEnd_7221605 := by
    simpa [prefixWord, tailWord_7221605, baseEnd_7221605] using wordTrace_append hprefix tailTrace_7221605
  have hstable : (prefixWord ++ tailWord_7221605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221605).length < 2 ^ (prefixWord ++ tailWord_7221605).sum := by decide
  have hdescent : baseEnd_7221605 < baseStart_7221605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221655 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_7221655 : Nat := 118140960795 + 7221655 * 2 ^ 59
def prefixEnd_7221655 : Nat := 4983230072969 + 3 ^ 40 * 7221655 * 2
def baseEnd_7221655 : Nat := 3708180135945047975300719

theorem tailTrace_7221655 : CollatzResearch.WordTrace tailWord_7221655 prefixEnd_7221655 3708180135945047975300719 := by
  unfold tailWord_7221655
  simp only [CollatzResearch.WordTrace]
  refine ⟨263395396652184770326266419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175596931101456513550844279 263395396652184770326266419)
  ·
    refine ⟨395093094978277155489399629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263395396652184770326266419 395093094978277155489399629)
    ·
      refine ⟨148159910616853933308524861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395093094978277155489399629 148159910616853933308524861)
      ·
        refine ⟨55559966481320224990696823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148159910616853933308524861 55559966481320224990696823)
        ·
          refine ⟨83339949721980337486045235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55559966481320224990696823 83339949721980337486045235)
          ·
            refine ⟨125009924582970506229067853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83339949721980337486045235 125009924582970506229067853)
            ·
              refine ⟨46878721718613939835900445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125009924582970506229067853 46878721718613939835900445)
              ·
                refine ⟨17579520644480227438462667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46878721718613939835900445 17579520644480227438462667)
                ·
                  refine ⟨26369280966720341157694001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17579520644480227438462667 26369280966720341157694001)
                  ·
                    refine ⟨19776960725040255868270501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26369280966720341157694001 19776960725040255868270501)
                    ·
                      refine ⟨3708180135945047975300719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19776960725040255868270501 3708180135945047975300719)
                      ·
                        rfl

theorem cell23_7221655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_7221655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221655 prefixEnd_7221655 := by exact prefixLift 7221655
  have htrace : WordTrace (prefixWord ++ tailWord_7221655) baseStart_7221655 baseEnd_7221655 := by
    simpa [prefixWord, tailWord_7221655, baseEnd_7221655] using wordTrace_append hprefix tailTrace_7221655
  have hstable : (prefixWord ++ tailWord_7221655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221655).length < 2 ^ (prefixWord ++ tailWord_7221655).sum := by decide
  have hdescent : baseEnd_7221655 < baseStart_7221655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221785 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_7221785 : Nat := 118140960795 + 7221785 * 2 ^ 59
def prefixEnd_7221785 : Nat := 4983230072969 + 3 ^ 40 * 7221785 * 2
def baseEnd_7221785 : Nat := 1236082296143377488891707

theorem tailTrace_7221785 : CollatzResearch.WordTrace tailWord_7221785 prefixEnd_7221785 1236082296143377488891707 := by
  unfold tailWord_7221785
  simp only [CollatzResearch.WordTrace]
  refine ⟨263400138141713802528498809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175600092094475868352332539 263400138141713802528498809)
  ·
    refine ⟨197550103606285351896374107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263400138141713802528498809 197550103606285351896374107)
    ·
      refine ⟨296325155409428027844561161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197550103606285351896374107 296325155409428027844561161)
      ·
        refine ⟨222243866557071020883420871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296325155409428027844561161 222243866557071020883420871)
        ·
          refine ⟨333365799835606531325131307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222243866557071020883420871 333365799835606531325131307)
          ·
            refine ⟨500048699753409796987696961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333365799835606531325131307 500048699753409796987696961)
            ·
              refine ⟨375036524815057347740772721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500048699753409796987696961 375036524815057347740772721)
              ·
                refine ⟨281277393611293010805579541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375036524815057347740772721 281277393611293010805579541)
                ·
                  refine ⟨13184877825529359881511541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281277393611293010805579541 13184877825529359881511541)
                  ·
                    refine ⟨1236082296143377488891707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13184877825529359881511541 1236082296143377488891707)
                    ·
                      rfl

theorem cell23_7221785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_7221785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221785 prefixEnd_7221785 := by exact prefixLift 7221785
  have htrace : WordTrace (prefixWord ++ tailWord_7221785) baseStart_7221785 baseEnd_7221785 := by
    simpa [prefixWord, tailWord_7221785, baseEnd_7221785] using wordTrace_append hprefix tailTrace_7221785
  have hstable : (prefixWord ++ tailWord_7221785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221785).length < 2 ^ (prefixWord ++ tailWord_7221785).sum := by decide
  have hdescent : baseEnd_7221785 < baseStart_7221785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221806 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_7221806 : Nat := 118140960795 + 7221806 * 2 ^ 59
def prefixEnd_7221806 : Nat := 4983230072969 + 3 ^ 40 * 7221806 * 2
def baseEnd_7221806 : Nat := 412028630169319653834725

theorem tailTrace_7221806 : CollatzResearch.WordTrace tailWord_7221806 prefixEnd_7221806 412028630169319653834725 := by
  unfold tailWord_7221806
  simp only [CollatzResearch.WordTrace]
  refine ⟨32925113009329715389376659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175600602716425148743342181 32925113009329715389376659)
  ·
    refine ⟨49387669513994573084064989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32925113009329715389376659 49387669513994573084064989)
    ·
      refine ⟨18520376067747964906524371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49387669513994573084064989 18520376067747964906524371)
      ·
        refine ⟨27780564101621947359786557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18520376067747964906524371 27780564101621947359786557)
        ·
          refine ⟨10417711538108230259919959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27780564101621947359786557 10417711538108230259919959)
          ·
            refine ⟨15626567307162345389879939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10417711538108230259919959 15626567307162345389879939)
            ·
              refine ⟨23439850960743518084819909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15626567307162345389879939 23439850960743518084819909)
              ·
                refine ⟨4394972055139409640903733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23439850960743518084819909 4394972055139409640903733)
                ·
                  refine ⟨412028630169319653834725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394972055139409640903733 412028630169319653834725)
                  ·
                    rfl

theorem cell23_7221806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_7221806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221806 prefixEnd_7221806 := by exact prefixLift 7221806
  have htrace : WordTrace (prefixWord ++ tailWord_7221806) baseStart_7221806 baseEnd_7221806 := by
    simpa [prefixWord, tailWord_7221806, baseEnd_7221806] using wordTrace_append hprefix tailTrace_7221806
  have hstable : (prefixWord ++ tailWord_7221806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221806).length < 2 ^ (prefixWord ++ tailWord_7221806).sum := by decide
  have hdescent : baseEnd_7221806 < baseStart_7221806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221866 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_7221866 : Nat := 118140960795 + 7221866 * 2 ^ 59
def prefixEnd_7221866 : Nat := 4983230072969 + 3 ^ 40 * 7221866 * 2
def baseEnd_7221866 : Nat := 1236096160121048883254083

theorem tailTrace_7221866 : CollatzResearch.WordTrace tailWord_7221866 prefixEnd_7221866 1236096160121048883254083 := by
  unfold tailWord_7221866
  simp only [CollatzResearch.WordTrace]
  refine ⟨65850773113605088340549363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175602061636280235574798301 65850773113605088340549363)
  ·
    refine ⟨98776159670407632510824045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65850773113605088340549363 98776159670407632510824045)
    ·
      refine ⟨37041059876402862191559017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98776159670407632510824045 37041059876402862191559017)
      ·
        refine ⟨27780794907302146643669263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37041059876402862191559017 27780794907302146643669263)
        ·
          refine ⟨41671192360953219965503895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27780794907302146643669263 41671192360953219965503895)
          ·
            refine ⟨62506788541429829948255843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41671192360953219965503895 62506788541429829948255843)
            ·
              refine ⟨93760182812144744922383765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62506788541429829948255843 93760182812144744922383765)
              ·
                refine ⟨4395008569319284918236739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93760182812144744922383765 4395008569319284918236739)
                ·
                  refine ⟨6592512853978927377355109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395008569319284918236739 6592512853978927377355109)
                  ·
                    refine ⟨1236096160121048883254083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6592512853978927377355109 1236096160121048883254083)
                    ·
                      rfl

theorem cell23_7221866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_7221866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221866 prefixEnd_7221866 := by exact prefixLift 7221866
  have htrace : WordTrace (prefixWord ++ tailWord_7221866) baseStart_7221866 baseEnd_7221866 := by
    simpa [prefixWord, tailWord_7221866, baseEnd_7221866] using wordTrace_append hprefix tailTrace_7221866
  have hstable : (prefixWord ++ tailWord_7221866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221866).length < 2 ^ (prefixWord ++ tailWord_7221866).sum := by decide
  have hdescent : baseEnd_7221866 < baseStart_7221866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221875 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 9]
def baseStart_7221875 : Nat := 118140960795 + 7221875 * 2 ^ 59
def prefixEnd_7221875 : Nat := 4983230072969 + 3 ^ 40 * 7221875 * 2
def baseEnd_7221875 : Nat := 1236097700563012371516569

theorem tailTrace_7221875 : CollatzResearch.WordTrace tailWord_7221875 prefixEnd_7221875 1236097700563012371516569 := by
  unfold tailWord_7221875
  simp only [CollatzResearch.WordTrace]
  refine ⟨263403420711387747899275079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175602280474258498599516719 263403420711387747899275079)
  ·
    refine ⟨395105131067081621848912619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263403420711387747899275079 395105131067081621848912619)
    ·
      refine ⟨592657696600622432773368929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395105131067081621848912619 592657696600622432773368929)
      ·
        refine ⟨444493272450466824580026697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592657696600622432773368929 444493272450466824580026697)
        ·
          refine ⟨333369954337850118435020023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444493272450466824580026697 333369954337850118435020023)
          ·
            refine ⟨500054931506775177652530035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333369954337850118435020023 500054931506775177652530035)
            ·
              refine ⟨750082397260162766478795053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500054931506775177652530035 750082397260162766478795053)
              ·
                refine ⟨281280898972561037429548145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750082397260162766478795053 281280898972561037429548145)
                ·
                  refine ⟨210960674229420778072161109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281280898972561037429548145 210960674229420778072161109)
                  ·
                    refine ⟨1236097700563012371516569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210960674229420778072161109 1236097700563012371516569)
                    ·
                      rfl

theorem cell23_7221875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_7221875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221875 prefixEnd_7221875 := by exact prefixLift 7221875
  have htrace : WordTrace (prefixWord ++ tailWord_7221875) baseStart_7221875 baseEnd_7221875 := by
    simpa [prefixWord, tailWord_7221875, baseEnd_7221875] using wordTrace_append hprefix tailTrace_7221875
  have hstable : (prefixWord ++ tailWord_7221875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221875).length < 2 ^ (prefixWord ++ tailWord_7221875).sum := by decide
  have hdescent : baseEnd_7221875 < baseStart_7221875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221916 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7221916 : Nat := 118140960795 + 7221916 * 2 ^ 59
def prefixEnd_7221916 : Nat := 4983230072969 + 3 ^ 40 * 7221916 * 2
def baseEnd_7221916 : Nat := 3708314154395871454137019

theorem tailTrace_7221916 : CollatzResearch.WordTrace tailWord_7221916 prefixEnd_7221916 3708314154395871454137019 := by
  unfold tailWord_7221916
  simp only [CollatzResearch.WordTrace]
  refine ⟨131702458052119605950758801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175603277402826141267678401 131702458052119605950758801)
  ·
    refine ⟨98776843539089704463069101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131702458052119605950758801 98776843539089704463069101)
    ·
      refine ⟨37041316327158639173650913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98776843539089704463069101 37041316327158639173650913)
      ·
        refine ⟨27780987245368979380238185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37041316327158639173650913 27780987245368979380238185)
        ·
          refine ⟨20835740434026734535178639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27780987245368979380238185 20835740434026734535178639)
          ·
            refine ⟨31253610651040101802767959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20835740434026734535178639 31253610651040101802767959)
            ·
              refine ⟨46880415976560152704151939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31253610651040101802767959 46880415976560152704151939)
              ·
                refine ⟨70320623964840229056227909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46880415976560152704151939 70320623964840229056227909)
                ·
                  refine ⟨13185116993407542948042733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70320623964840229056227909 13185116993407542948042733)
                  ·
                    refine ⟨4944418872527828605516025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13185116993407542948042733 4944418872527828605516025)
                    ·
                      refine ⟨3708314154395871454137019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944418872527828605516025 3708314154395871454137019)
                      ·
                        rfl

theorem cell23_7221916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7221916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221916 prefixEnd_7221916 := by exact prefixLift 7221916
  have htrace : WordTrace (prefixWord ++ tailWord_7221916) baseStart_7221916 baseEnd_7221916 := by
    simpa [prefixWord, tailWord_7221916, baseEnd_7221916] using wordTrace_append hprefix tailTrace_7221916
  have hstable : (prefixWord ++ tailWord_7221916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221916).length < 2 ^ (prefixWord ++ tailWord_7221916).sum := by decide
  have hdescent : baseEnd_7221916 < baseStart_7221916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221930 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_7221930 : Nat := 118140960795 + 7221930 * 2 ^ 59
def prefixEnd_7221930 : Nat := 4983230072969 + 3 ^ 40 * 7221930 * 2
def baseEnd_7221930 : Nat := 412035704791670488817995

theorem tailTrace_7221930 : CollatzResearch.WordTrace tailWord_7221930 prefixEnd_7221930 412035704791670488817995 := by
  unfold tailWord_7221930
  simp only [CollatzResearch.WordTrace]
  refine ⟨65851356681547123073131811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175603617817458994861684829 65851356681547123073131811)
  ·
    refine ⟨98777035022320684609697717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65851356681547123073131811 98777035022320684609697717)
    ·
      refine ⟨9260347033342564182159161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98777035022320684609697717 9260347033342564182159161)
      ·
        refine ⟨6945260275006923136619371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9260347033342564182159161 6945260275006923136619371)
        ·
          refine ⟨10417890412510384704929057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945260275006923136619371 10417890412510384704929057)
          ·
            refine ⟨7813417809382788528696793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10417890412510384704929057 7813417809382788528696793)
            ·
              refine ⟨5860063357037091396522595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7813417809382788528696793 5860063357037091396522595)
              ·
                refine ⟨8790095035555637094783893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5860063357037091396522595 8790095035555637094783893)
                ·
                  refine ⟨412035704791670488817995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8790095035555637094783893 412035704791670488817995)
                  ·
                    rfl

theorem cell23_7221930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_7221930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221930 prefixEnd_7221930 := by exact prefixLift 7221930
  have htrace : WordTrace (prefixWord ++ tailWord_7221930) baseStart_7221930 baseEnd_7221930 := by
    simpa [prefixWord, tailWord_7221930, baseEnd_7221930] using wordTrace_append hprefix tailTrace_7221930
  have hstable : (prefixWord ++ tailWord_7221930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221930).length < 2 ^ (prefixWord ++ tailWord_7221930).sum := by decide
  have hdescent : baseEnd_7221930 < baseStart_7221930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221943 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 1, 5]
def baseStart_7221943 : Nat := 118140960795 + 7221943 * 2 ^ 59
def prefixEnd_7221943 : Nat := 4983230072969 + 3 ^ 40 * 7221943 * 2
def baseEnd_7221943 : Nat := 1236109339457847616166465

theorem tailTrace_7221943 : CollatzResearch.WordTrace tailWord_7221943 prefixEnd_7221943 1236109339457847616166465 := by
  unfold tailWord_7221943
  simp only [CollatzResearch.WordTrace]
  refine ⟨263405900875141395512750483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175603933916760930341833655 263405900875141395512750483)
  ·
    refine ⟨395108851312712093269125725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263405900875141395512750483 395108851312712093269125725)
    ·
      refine ⟨148165819242267034975922147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395108851312712093269125725 148165819242267034975922147)
      ·
        refine ⟨222248728863400552463883221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148165819242267034975922147 222248728863400552463883221)
        ·
          refine ⟨5208954582735950448372263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 222248728863400552463883221 5208954582735950448372263)
          ·
            refine ⟨7813431874103925672558395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208954582735950448372263 7813431874103925672558395)
            ·
              refine ⟨11720147811155888508837593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813431874103925672558395 11720147811155888508837593)
              ·
                refine ⟨8790110858366916381628195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11720147811155888508837593 8790110858366916381628195)
                ·
                  refine ⟨13185166287550374572442293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8790110858366916381628195 13185166287550374572442293)
                  ·
                    refine ⟨1236109339457847616166465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13185166287550374572442293 1236109339457847616166465)
                    ·
                      rfl

theorem cell23_7221943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_7221943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221943 prefixEnd_7221943 := by exact prefixLift 7221943
  have htrace : WordTrace (prefixWord ++ tailWord_7221943) baseStart_7221943 baseEnd_7221943 := by
    simpa [prefixWord, tailWord_7221943, baseEnd_7221943] using wordTrace_append hprefix tailTrace_7221943
  have hstable : (prefixWord ++ tailWord_7221943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221943).length < 2 ^ (prefixWord ++ tailWord_7221943).sum := by decide
  have hdescent : baseEnd_7221943 < baseStart_7221943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221946 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2]
def baseStart_7221946 : Nat := 118140960795 + 7221946 * 2 ^ 59
def prefixEnd_7221946 : Nat := 4983230072969 + 3 ^ 40 * 7221946 * 2
def baseEnd_7221946 : Nat := 3708329558815506336761881

theorem tailTrace_7221946 : CollatzResearch.WordTrace tailWord_7221946 prefixEnd_7221946 3708329558815506336761881 := by
  unfold tailWord_7221946
  simp only [CollatzResearch.WordTrace]
  refine ⟨65851502573532631756277423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175604006862753684683406461 65851502573532631756277423)
  ·
    refine ⟨98777253860298947634416135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65851502573532631756277423 98777253860298947634416135)
    ·
      refine ⟨148165880790448421451624203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98777253860298947634416135 148165880790448421451624203)
      ·
        refine ⟨222248821185672632177436305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148165880790448421451624203 222248821185672632177436305)
        ·
          refine ⟨166686615889254474133077229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222248821185672632177436305 166686615889254474133077229)
          ·
            refine ⟨62507480958470427799903961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166686615889254474133077229 62507480958470427799903961)
            ·
              refine ⟨46880610718852820849927971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62507480958470427799903961 46880610718852820849927971)
              ·
                refine ⟨70320916078279231274891957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46880610718852820849927971 70320916078279231274891957)
                ·
                  refine ⟨6592585882338677932021121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70320916078279231274891957 6592585882338677932021121)
                  ·
                    refine ⟨4944439411754008449015841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592585882338677932021121 4944439411754008449015841)
                    ·
                      refine ⟨3708329558815506336761881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944439411754008449015841 3708329558815506336761881)
                      ·
                        rfl

theorem cell23_7221946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_7221946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221946 prefixEnd_7221946 := by exact prefixLift 7221946
  have htrace : WordTrace (prefixWord ++ tailWord_7221946) baseStart_7221946 baseEnd_7221946 := by
    simpa [prefixWord, tailWord_7221946, baseEnd_7221946] using wordTrace_append hprefix tailTrace_7221946
  have hstable : (prefixWord ++ tailWord_7221946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221946).length < 2 ^ (prefixWord ++ tailWord_7221946).sum := by decide
  have hdescent : baseEnd_7221946 < baseStart_7221946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221952 : List Nat := [2, 1, 1, 2, 4, 2, 2, 9]
def baseStart_7221952 : Nat := 118140960795 + 7221952 * 2 ^ 59
def prefixEnd_7221952 : Nat := 4983230072969 + 3 ^ 40 * 7221952 * 2
def baseEnd_7221952 : Nat := 137345653322201233825439

theorem tailTrace_7221952 : CollatzResearch.WordTrace tailWord_7221952 prefixEnd_7221952 137345653322201233825439 := by
  unfold tailWord_7221952
  simp only [CollatzResearch.WordTrace]
  refine ⟨131703114566054395024914055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175604152754739193366552073 131703114566054395024914055)
  ·
    refine ⟨197554671849081592537371083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131703114566054395024914055 197554671849081592537371083)
    ·
      refine ⟨296332007773622388806056625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197554671849081592537371083 296332007773622388806056625)
      ·
        refine ⟨222249005830216791604542469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296332007773622388806056625 222249005830216791604542469)
        ·
          refine ⟨41671688593165648425851713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222249005830216791604542469 41671688593165648425851713)
          ·
            refine ⟨31253766444874236319388785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41671688593165648425851713 31253766444874236319388785)
            ·
              refine ⟨23440324833655677239541589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31253766444874236319388785 23440324833655677239541589)
              ·
                refine ⟨137345653322201233825439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23440324833655677239541589 137345653322201233825439)
                ·
                  rfl

theorem cell23_7221952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 9].length) (baseStart_7221952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221952 prefixEnd_7221952 := by exact prefixLift 7221952
  have htrace : WordTrace (prefixWord ++ tailWord_7221952) baseStart_7221952 baseEnd_7221952 := by
    simpa [prefixWord, tailWord_7221952, baseEnd_7221952] using wordTrace_append hprefix tailTrace_7221952
  have hstable : (prefixWord ++ tailWord_7221952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221952).length < 2 ^ (prefixWord ++ tailWord_7221952).sum := by decide
  have hdescent : baseEnd_7221952 < baseStart_7221952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221966 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_7221966 : Nat := 118140960795 + 7221966 * 2 ^ 59
def prefixEnd_7221966 : Nat := 4983230072969 + 3 ^ 40 * 7221966 * 2
def baseEnd_7221966 : Nat := 3708339828428596258511789

theorem tailTrace_7221966 : CollatzResearch.WordTrace tailWord_7221966 prefixEnd_7221966 3708339828428596258511789 := by
  unfold tailWord_7221966
  simp only [CollatzResearch.WordTrace]
  refine ⟨32925842469257258805104719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175604493169372046960558501 32925842469257258805104719)
  ·
    refine ⟨49388763703885888207657079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32925842469257258805104719 49388763703885888207657079)
    ·
      refine ⟨74083145555828832311485619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49388763703885888207657079 74083145555828832311485619)
      ·
        refine ⟨111124718333743248467228429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74083145555828832311485619 111124718333743248467228429)
        ·
          refine ⟨41671769375153718175210661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111124718333743248467228429 41671769375153718175210661)
          ·
            refine ⟨7813456757841322157851999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41671769375153718175210661 7813456757841322157851999)
            ·
              refine ⟨11720185136761983236777999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813456757841322157851999 11720185136761983236777999)
              ·
                refine ⟨17580277705142974855166999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11720185136761983236777999 17580277705142974855166999)
                ·
                  refine ⟨26370416557714462282750499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17580277705142974855166999 26370416557714462282750499)
                  ·
                    refine ⟨39555624836571693424125749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26370416557714462282750499 39555624836571693424125749)
                    ·
                      refine ⟨3708339828428596258511789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39555624836571693424125749 3708339828428596258511789)
                      ·
                        rfl

theorem cell23_7221966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_7221966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221966 prefixEnd_7221966 := by exact prefixLift 7221966
  have htrace : WordTrace (prefixWord ++ tailWord_7221966) baseStart_7221966 baseEnd_7221966 := by
    simpa [prefixWord, tailWord_7221966, baseEnd_7221966] using wordTrace_append hprefix tailTrace_7221966
  have hstable : (prefixWord ++ tailWord_7221966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221966).length < 2 ^ (prefixWord ++ tailWord_7221966).sum := by decide
  have hdescent : baseEnd_7221966 < baseStart_7221966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222049 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7222049 : Nat := 118140960795 + 7222049 * 2 ^ 59
def prefixEnd_7222049 : Nat := 4983230072969 + 3 ^ 40 * 7222049 * 2
def baseEnd_7222049 : Nat := 3708382447322919433773907

theorem tailTrace_7222049 : CollatzResearch.WordTrace tailWord_7222049 prefixEnd_7222049 3708382447322919433773907 := by
  unfold tailWord_7222049
  simp only [CollatzResearch.WordTrace]
  refine ⟨263409767012757375616109201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175606511341838250410739467 263409767012757375616109201)
  ·
    refine ⟨197557325259568031712081901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263409767012757375616109201 197557325259568031712081901)
    ·
      refine ⟨74083996972338011892030713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197557325259568031712081901 74083996972338011892030713)
      ·
        refine ⟨55562997729253508919023035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74083996972338011892030713 55562997729253508919023035)
        ·
          refine ⟨83344496593880263378534553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55562997729253508919023035 83344496593880263378534553)
          ·
            refine ⟨62508372445410197533900915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83344496593880263378534553 62508372445410197533900915)
            ·
              refine ⟨93762558668115296300851373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62508372445410197533900915 93762558668115296300851373)
              ·
                refine ⟨35160959500543236112819265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93762558668115296300851373 35160959500543236112819265)
                ·
                  refine ⟨26370719625407427084614449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35160959500543236112819265 26370719625407427084614449)
                  ·
                    refine ⟨19778039719055570313460837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26370719625407427084614449 19778039719055570313460837)
                    ·
                      refine ⟨3708382447322919433773907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19778039719055570313460837 3708382447322919433773907)
                      ·
                        rfl

theorem cell23_7222049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7222049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222049 prefixEnd_7222049 := by exact prefixLift 7222049
  have htrace : WordTrace (prefixWord ++ tailWord_7222049) baseStart_7222049 baseEnd_7222049 := by
    simpa [prefixWord, tailWord_7222049, baseEnd_7222049] using wordTrace_append hprefix tailTrace_7222049
  have hstable : (prefixWord ++ tailWord_7222049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222049).length < 2 ^ (prefixWord ++ tailWord_7222049).sum := by decide
  have hdescent : baseEnd_7222049 < baseStart_7222049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222089 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_7222089 : Nat := 118140960795 + 7222089 * 2 ^ 59
def prefixEnd_7222089 : Nat := 4983230072969 + 3 ^ 40 * 7222089 * 2
def baseEnd_7222089 : Nat := 1236134328849699759091241

theorem tailTrace_7222089 : CollatzResearch.WordTrace tailWord_7222089 prefixEnd_7222089 1236134328849699759091241 := by
  unfold tailWord_7222089
  simp only [CollatzResearch.WordTrace]
  refine ⟨263411225932612462447565321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175607483955074974965043547 263411225932612462447565321)
  ·
    refine ⟨197558419449459346835673991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263411225932612462447565321 197558419449459346835673991)
    ·
      refine ⟨296337629174189020253510987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197558419449459346835673991 296337629174189020253510987)
      ·
        refine ⟨444506443761283530380266481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296337629174189020253510987 444506443761283530380266481)
        ·
          refine ⟨333379832820962647785199861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444506443761283530380266481 333379832820962647785199861)
          ·
            refine ⟨31254359326965248229862487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333379832820962647785199861 31254359326965248229862487)
            ·
              refine ⟨46881538990447872344793731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31254359326965248229862487 46881538990447872344793731)
              ·
                refine ⟨70322308485671808517190597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46881538990447872344793731 70322308485671808517190597)
                ·
                  refine ⟨13185432841063464096973237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70322308485671808517190597 13185432841063464096973237)
                  ·
                    refine ⟨1236134328849699759091241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13185432841063464096973237 1236134328849699759091241)
                    ·
                      rfl

theorem cell23_7222089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_7222089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222089 prefixEnd_7222089 := by exact prefixLift 7222089
  have htrace : WordTrace (prefixWord ++ tailWord_7222089) baseStart_7222089 baseEnd_7222089 := by
    simpa [prefixWord, tailWord_7222089, baseEnd_7222089] using wordTrace_append hprefix tailTrace_7222089
  have hstable : (prefixWord ++ tailWord_7222089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222089).length < 2 ^ (prefixWord ++ tailWord_7222089).sum := by decide
  have hdescent : baseEnd_7222089 < baseStart_7222089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222230 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_7222230 : Nat := 118140960795 + 7222230 * 2 ^ 59
def prefixEnd_7222230 : Nat := 4983230072969 + 3 ^ 40 * 7222230 * 2
def baseEnd_7222230 : Nat := 1236158462440461075203525

theorem tailTrace_7222230 : CollatzResearch.WordTrace tailWord_7222230 prefixEnd_7222230 1236158462440461075203525 := by
  unfold tailWord_7222230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16463523039068852720528009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175610912416734429018965429 16463523039068852720528009)
  ·
    refine ⟨12347642279301639540396007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16463523039068852720528009 12347642279301639540396007)
    ·
      refine ⟨18521463418952459310594011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12347642279301639540396007 18521463418952459310594011)
      ·
        refine ⟨27782195128428688965891017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18521463418952459310594011 27782195128428688965891017)
        ·
          refine ⟨20836646346321516724418263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27782195128428688965891017 20836646346321516724418263)
          ·
            refine ⟨31254969519482275086627395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20836646346321516724418263 31254969519482275086627395)
            ·
              refine ⟨46882454279223412629941093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31254969519482275086627395 46882454279223412629941093)
              ·
                refine ⟨8790460177354389868113955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46882454279223412629941093 8790460177354389868113955)
                ·
                  refine ⟨13185690266031584802170933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8790460177354389868113955 13185690266031584802170933)
                  ·
                    refine ⟨1236158462440461075203525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13185690266031584802170933 1236158462440461075203525)
                    ·
                      rfl

theorem cell23_7222230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_7222230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222230 prefixEnd_7222230 := by exact prefixLift 7222230
  have htrace : WordTrace (prefixWord ++ tailWord_7222230) baseStart_7222230 baseEnd_7222230 := by
    simpa [prefixWord, tailWord_7222230, baseEnd_7222230] using wordTrace_append hprefix tailTrace_7222230
  have hstable : (prefixWord ++ tailWord_7222230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222230).length < 2 ^ (prefixWord ++ tailWord_7222230).sum := by decide
  have hdescent : baseEnd_7222230 < baseStart_7222230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222233 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 4]
def baseStart_7222233 : Nat := 118140960795 + 7222233 * 2 ^ 59
def prefixEnd_7222233 : Nat := 4983230072969 + 3 ^ 40 * 7222233 * 2
def baseEnd_7222233 : Nat := 3708476927763346713873061

theorem tailTrace_7222233 : CollatzResearch.WordTrace tailWord_7222233 prefixEnd_7222233 3708476927763346713873061 := by
  unfold tailWord_7222233
  simp only [CollatzResearch.WordTrace]
  refine ⟨263416478044090775040807353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175610985362727183360538235 263416478044090775040807353)
  ·
    refine ⟨197562358533068081280605515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263416478044090775040807353 197562358533068081280605515)
    ·
      refine ⟨296343537799602121920908273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197562358533068081280605515 296343537799602121920908273)
      ·
        refine ⟨222257653349701591440681205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296343537799602121920908273 222257653349701591440681205)
        ·
          refine ⟨20836655001534524197563863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222257653349701591440681205 20836655001534524197563863)
          ·
            refine ⟨31254982502301786296345795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20836655001534524197563863 31254982502301786296345795)
            ·
              refine ⟨46882473753452679444518693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31254982502301786296345795 46882473753452679444518693)
              ·
                refine ⟨8790463828772377395847255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46882473753452679444518693 8790463828772377395847255)
                ·
                  refine ⟨13185695743158566093770883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8790463828772377395847255 13185695743158566093770883)
                  ·
                    refine ⟨19778543614737849140656325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13185695743158566093770883 19778543614737849140656325)
                    ·
                      refine ⟨3708476927763346713873061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19778543614737849140656325 3708476927763346713873061)
                      ·
                        rfl

theorem cell23_7222233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_7222233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222233 prefixEnd_7222233 := by exact prefixLift 7222233
  have htrace : WordTrace (prefixWord ++ tailWord_7222233) baseStart_7222233 baseEnd_7222233 := by
    simpa [prefixWord, tailWord_7222233, baseEnd_7222233] using wordTrace_append hprefix tailTrace_7222233
  have hstable : (prefixWord ++ tailWord_7222233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222233).length < 2 ^ (prefixWord ++ tailWord_7222233).sum := by decide
  have hdescent : baseEnd_7222233 < baseStart_7222233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222261 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7222261 : Nat := 118140960795 + 7222261 * 2 ^ 59
def prefixEnd_7222261 : Nat := 4983230072969 + 3 ^ 40 * 7222261 * 2
def baseEnd_7222261 : Nat := 3708491305221672604322933

theorem tailTrace_7222261 : CollatzResearch.WordTrace tailWord_7222261 prefixEnd_7222261 3708491305221672604322933 := by
  unfold tailWord_7222261
  simp only [CollatzResearch.WordTrace]
  refine ⟨263417499287989335822826637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175611666191992890548551091 263417499287989335822826637)
  ·
    refine ⟨98781562232996000933559989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263417499287989335822826637 98781562232996000933559989)
    ·
      refine ⟨9260771459343375087521249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98781562232996000933559989 9260771459343375087521249)
      ·
        refine ⟨6945578594507531315640937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9260771459343375087521249 6945578594507531315640937)
        ·
          refine ⟨5209183945880648486730703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6945578594507531315640937 5209183945880648486730703)
          ·
            refine ⟨7813775918820972730096055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209183945880648486730703 7813775918820972730096055)
            ·
              refine ⟨11720663878231459095144083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813775918820972730096055 11720663878231459095144083)
              ·
                refine ⟨17580995817347188642716125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11720663878231459095144083 17580995817347188642716125)
                ·
                  refine ⟨6592873431505195741018547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17580995817347188642716125 6592873431505195741018547)
                  ·
                    refine ⟨9889310147257793611527821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6592873431505195741018547 9889310147257793611527821)
                    ·
                      refine ⟨3708491305221672604322933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889310147257793611527821 3708491305221672604322933)
                      ·
                        rfl

theorem cell23_7222261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7222261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222261 prefixEnd_7222261 := by exact prefixLift 7222261
  have htrace : WordTrace (prefixWord ++ tailWord_7222261) baseStart_7222261 baseEnd_7222261 := by
    simpa [prefixWord, tailWord_7222261, baseEnd_7222261] using wordTrace_append hprefix tailTrace_7222261
  have hstable : (prefixWord ++ tailWord_7222261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222261).length < 2 ^ (prefixWord ++ tailWord_7222261).sum := by decide
  have hdescent : baseEnd_7222261 < baseStart_7222261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222300 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_7222300 : Nat := 118140960795 + 7222300 * 2 ^ 59
def prefixEnd_7222300 : Nat := 4983230072969 + 3 ^ 40 * 7222300 * 2
def baseEnd_7222300 : Nat := 3708511330967197951735253

theorem tailTrace_7222300 : CollatzResearch.WordTrace tailWord_7222300 prefixEnd_7222300 3708511330967197951735253 := by
  unfold tailWord_7222300
  simp only [CollatzResearch.WordTrace]
  refine ⟨131709460867424022741748177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175612614489898696988997569 131709460867424022741748177)
  ·
    refine ⟨98782095650568017056311133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131709460867424022741748177 98782095650568017056311133)
    ·
      refine ⟨37043285868963006396116675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98782095650568017056311133 37043285868963006396116675)
      ·
        refine ⟨55564928803444509594175013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37043285868963006396116675 55564928803444509594175013)
        ·
          refine ⟨10418424150645845548907815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55564928803444509594175013 10418424150645845548907815)
          ·
            refine ⟨15627636225968768323361723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418424150645845548907815 15627636225968768323361723)
            ·
              refine ⟨23441454338953152485042585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15627636225968768323361723 23441454338953152485042585)
              ·
                refine ⟨17581090754214864363781939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23441454338953152485042585 17581090754214864363781939)
                ·
                  refine ⟨26371636131322296545672909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17581090754214864363781939 26371636131322296545672909)
                  ·
                    refine ⟨9889363549245861204627341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26371636131322296545672909 9889363549245861204627341)
                    ·
                      refine ⟨3708511330967197951735253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889363549245861204627341 3708511330967197951735253)
                      ·
                        rfl

theorem cell23_7222300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_7222300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222300 prefixEnd_7222300 := by exact prefixLift 7222300
  have htrace : WordTrace (prefixWord ++ tailWord_7222300) baseStart_7222300 baseEnd_7222300 := by
    simpa [prefixWord, tailWord_7222300, baseEnd_7222300] using wordTrace_append hprefix tailTrace_7222300
  have hstable : (prefixWord ++ tailWord_7222300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222300).length < 2 ^ (prefixWord ++ tailWord_7222300).sum := by decide
  have hdescent : baseEnd_7222300 < baseStart_7222300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222304 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7222304 : Nat := 118140960795 + 7222304 * 2 ^ 59
def prefixEnd_7222304 : Nat := 4983230072969 + 3 ^ 40 * 7222304 * 2
def baseEnd_7222304 : Nat := 3708513384889815936085235

theorem tailTrace_7222304 : CollatzResearch.WordTrace tailWord_7222304 prefixEnd_7222304 3708513384889815936085235 := by
  unfold tailWord_7222304
  simp only [CollatzResearch.WordTrace]
  refine ⟨131709533813416777083320983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175612711751222369444427977 131709533813416777083320983)
  ·
    refine ⟨197564300720125165624981475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131709533813416777083320983 197564300720125165624981475)
    ·
      refine ⟨296346451080187748437472213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197564300720125165624981475 296346451080187748437472213)
      ·
        refine ⟨6945619947191900354003255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 296346451080187748437472213 6945619947191900354003255)
        ·
          refine ⟨10418429920787850531004883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945619947191900354003255 10418429920787850531004883)
          ·
            refine ⟨15627644881181775796507325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418429920787850531004883 15627644881181775796507325)
            ·
              refine ⟨5860366830443165923690247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15627644881181775796507325 5860366830443165923690247)
              ·
                refine ⟨8790550245664748885535371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5860366830443165923690247 8790550245664748885535371)
                ·
                  refine ⟨13185825368497123328303057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8790550245664748885535371 13185825368497123328303057)
                  ·
                    refine ⟨9889369026372842496227293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13185825368497123328303057 9889369026372842496227293)
                    ·
                      refine ⟨3708513384889815936085235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889369026372842496227293 3708513384889815936085235)
                      ·
                        rfl

theorem cell23_7222304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7222304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222304 prefixEnd_7222304 := by exact prefixLift 7222304
  have htrace : WordTrace (prefixWord ++ tailWord_7222304) baseStart_7222304 baseEnd_7222304 := by
    simpa [prefixWord, tailWord_7222304, baseEnd_7222304] using wordTrace_append hprefix tailTrace_7222304
  have hstable : (prefixWord ++ tailWord_7222304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222304).length < 2 ^ (prefixWord ++ tailWord_7222304).sum := by decide
  have hdescent : baseEnd_7222304 < baseStart_7222304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222316 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_7222316 : Nat := 118140960795 + 7222316 * 2 ^ 59
def prefixEnd_7222316 : Nat := 4983230072969 + 3 ^ 40 * 7222316 * 2
def baseEnd_7222316 : Nat := 1236173182219223296378393

theorem tailTrace_7222316 : CollatzResearch.WordTrace tailWord_7222316 prefixEnd_7222316 1236173182219223296378393 := by
  unfold tailWord_7222316
  simp only [CollatzResearch.WordTrace]
  refine ⟨131709752651395040108039401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175613003535193386810719201 131709752651395040108039401)
  ·
    refine ⟨98782314488546280081029551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131709752651395040108039401 98782314488546280081029551)
    ·
      refine ⟨148173471732819420121544327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98782314488546280081029551 148173471732819420121544327)
      ·
        refine ⟨222260207599229130182316491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148173471732819420121544327 222260207599229130182316491)
        ·
          refine ⟨333390311398843695273474737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222260207599229130182316491 333390311398843695273474737)
          ·
            refine ⟨250042733549132771455106053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333390311398843695273474737 250042733549132771455106053)
            ·
              refine ⟨46883012540462394647832385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250042733549132771455106053 46883012540462394647832385)
              ·
                refine ⟨35162259405346795985874289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46883012540462394647832385 35162259405346795985874289)
                ·
                  refine ⟨26371694554010096989405717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35162259405346795985874289 26371694554010096989405717)
                  ·
                    refine ⟨1236173182219223296378393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26371694554010096989405717 1236173182219223296378393)
                    ·
                      rfl

theorem cell23_7222316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_7222316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222316 prefixEnd_7222316 := by exact prefixLift 7222316
  have htrace : WordTrace (prefixWord ++ tailWord_7222316) baseStart_7222316 baseEnd_7222316 := by
    simpa [prefixWord, tailWord_7222316, baseEnd_7222316] using wordTrace_append hprefix tailTrace_7222316
  have hstable : (prefixWord ++ tailWord_7222316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222316).length < 2 ^ (prefixWord ++ tailWord_7222316).sum := by decide
  have hdescent : baseEnd_7222316 < baseStart_7222316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222323 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 5, 4, 2]
def baseStart_7222323 : Nat := 118140960795 + 7222323 * 2 ^ 59
def prefixEnd_7222323 : Nat := 4983230072969 + 3 ^ 40 * 7222323 * 2
def baseEnd_7222323 : Nat := 3708523141022251361747647

theorem tailTrace_7222323 : CollatzResearch.WordTrace tailWord_7222323 prefixEnd_7222323 3708523141022251361747647 := by
  unfold tailWord_7222323
  simp only [CollatzResearch.WordTrace]
  refine ⟨263419760613764720411583623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175613173742509813607722415 263419760613764720411583623)
  ·
    refine ⟨395129640920647080617375435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263419760613764720411583623 395129640920647080617375435)
    ·
      refine ⟨592694461380970620926063153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395129640920647080617375435 592694461380970620926063153)
      ·
        refine ⟨444520846035727965694547365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592694461380970620926063153 444520846035727965694547365)
        ·
          refine ⟨83347658631698993567727631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444520846035727965694547365 83347658631698993567727631)
          ·
            refine ⟨125021487947548490351591447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83347658631698993567727631 125021487947548490351591447)
            ·
              refine ⟨187532231921322735527387171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125021487947548490351591447 187532231921322735527387171)
              ·
                refine ⟨281298347881984103291080757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187532231921322735527387171 281298347881984103291080757)
                ·
                  refine ⟨26371720113936009683538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281298347881984103291080757 26371720113936009683538821)
                  ·
                    refine ⟨4944697521363001815663529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26371720113936009683538821 4944697521363001815663529)
                    ·
                      refine ⟨3708523141022251361747647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944697521363001815663529 3708523141022251361747647)
                      ·
                        rfl

theorem cell23_7222323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4, 2].length) (baseStart_7222323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222323 prefixEnd_7222323 := by exact prefixLift 7222323
  have htrace : WordTrace (prefixWord ++ tailWord_7222323) baseStart_7222323 baseEnd_7222323 := by
    simpa [prefixWord, tailWord_7222323, baseEnd_7222323] using wordTrace_append hprefix tailTrace_7222323
  have hstable : (prefixWord ++ tailWord_7222323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222323).length < 2 ^ (prefixWord ++ tailWord_7222323).sum := by decide
  have hdescent : baseEnd_7222323 < baseStart_7222323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222333 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_7222333 : Nat := 118140960795 + 7222333 * 2 ^ 59
def prefixEnd_7222333 : Nat := 4983230072969 + 3 ^ 40 * 7222333 * 2
def baseEnd_7222333 : Nat := 1236176091942932107540867

theorem tailTrace_7222333 : CollatzResearch.WordTrace tailWord_7222333 prefixEnd_7222333 1236176091942932107540867 := by
  unfold tailWord_7222333
  simp only [CollatzResearch.WordTrace]
  refine ⟨263420125343728492119447653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175613416895818994746298435 263420125343728492119447653)
  ·
    refine ⟨49391273501949092272396435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263420125343728492119447653 49391273501949092272396435)
    ·
      refine ⟨74086910252923638408594653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49391273501949092272396435 74086910252923638408594653)
      ·
        refine ⟨27782591344846364403222995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74086910252923638408594653 27782591344846364403222995)
        ·
          refine ⟨41673887017269546604834493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27782591344846364403222995 41673887017269546604834493)
          ·
            refine ⟨15627707631476079976812935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41673887017269546604834493 15627707631476079976812935)
            ·
              refine ⟨23441561447214119965219403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15627707631476079976812935 23441561447214119965219403)
              ·
                refine ⟨35162342170821179947829105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23441561447214119965219403 35162342170821179947829105)
                ·
                  refine ⟨26371756628115884960871829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35162342170821179947829105 26371756628115884960871829)
                  ·
                    refine ⟨1236176091942932107540867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26371756628115884960871829 1236176091942932107540867)
                    ·
                      rfl

theorem cell23_7222333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_7222333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222333 prefixEnd_7222333 := by exact prefixLift 7222333
  have htrace : WordTrace (prefixWord ++ tailWord_7222333) baseStart_7222333 baseEnd_7222333 := by
    simpa [prefixWord, tailWord_7222333, baseEnd_7222333] using wordTrace_append hprefix tailTrace_7222333
  have hstable : (prefixWord ++ tailWord_7222333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222333).length < 2 ^ (prefixWord ++ tailWord_7222333).sum := by decide
  have hdescent : baseEnd_7222333 < baseStart_7222333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222346 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_7222346 : Nat := 118140960795 + 7222346 * 2 ^ 59
def prefixEnd_7222346 : Nat := 4983230072969 + 3 ^ 40 * 7222346 * 2
def baseEnd_7222346 : Nat := 412059439008589419084449

theorem tailTrace_7222346 : CollatzResearch.WordTrace tailWord_7222346 prefixEnd_7222346 412059439008589419084449 := by
  unfold tailWord_7222346
  simp only [CollatzResearch.WordTrace]
  refine ⟨65855149873170348834917723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175613732995120930226447261 65855149873170348834917723)
  ·
    refine ⟨98782724809755523252376585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65855149873170348834917723 98782724809755523252376585)
    ·
      refine ⟨74087043607316642439282439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98782724809755523252376585 74087043607316642439282439)
      ·
        refine ⟨111130565410974963658923659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74087043607316642439282439 111130565410974963658923659)
        ·
          refine ⟨166695848116462445488385489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111130565410974963658923659 166695848116462445488385489)
          ·
            refine ⟨125021886087346834116289117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166695848116462445488385489 125021886087346834116289117)
            ·
              refine ⟨46883207282755062793608419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125021886087346834116289117 46883207282755062793608419)
              ·
                refine ⟨70324810924132594190412629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46883207282755062793608419 70324810924132594190412629)
                ·
                  refine ⟨412059439008589419084449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70324810924132594190412629 412059439008589419084449)
                  ·
                    rfl

theorem cell23_7222346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_7222346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222346 prefixEnd_7222346 := by exact prefixLift 7222346
  have htrace : WordTrace (prefixWord ++ tailWord_7222346) baseStart_7222346 baseEnd_7222346 := by
    simpa [prefixWord, tailWord_7222346, baseEnd_7222346] using wordTrace_append hprefix tailTrace_7222346
  have hstable : (prefixWord ++ tailWord_7222346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222346).length < 2 ^ (prefixWord ++ tailWord_7222346).sum := by decide
  have hdescent : baseEnd_7222346 < baseStart_7222346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222370 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7222370 : Nat := 118140960795 + 7222370 * 2 ^ 59
def prefixEnd_7222370 : Nat := 4983230072969 + 3 ^ 40 * 7222370 * 2
def baseEnd_7222370 : Nat := 3708547274613012677859931

theorem tailTrace_7222370 : CollatzResearch.WordTrace tailWord_7222370 prefixEnd_7222370 3708547274613012677859931 := by
  unfold tailWord_7222370
  simp only [CollatzResearch.WordTrace]
  refine ⟨65855368711148611859636141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175614316563062964959029709 65855368711148611859636141)
  ·
    refine ⟨24695763266680729447363553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65855368711148611859636141 24695763266680729447363553)
    ·
      refine ⟨18521822450010547085522665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24695763266680729447363553 18521822450010547085522665)
      ·
        refine ⟨13891366837507910314141999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18521822450010547085522665 13891366837507910314141999)
        ·
          refine ⟨20837050256261865471212999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891366837507910314141999 20837050256261865471212999)
          ·
            refine ⟨31255575384392798206819499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20837050256261865471212999 31255575384392798206819499)
            ·
              refine ⟨46883363076589197310229249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31255575384392798206819499 46883363076589197310229249)
              ·
                refine ⟨35162522307441897982671937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46883363076589197310229249 35162522307441897982671937)
                ·
                  refine ⟨26371891730581423487003953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35162522307441897982671937 26371891730581423487003953)
                  ·
                    refine ⟨19778918797936067615252965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26371891730581423487003953 19778918797936067615252965)
                    ·
                      refine ⟨3708547274613012677859931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19778918797936067615252965 3708547274613012677859931)
                      ·
                        rfl

theorem cell23_7222370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7222370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222370 prefixEnd_7222370 := by exact prefixLift 7222370
  have htrace : WordTrace (prefixWord ++ tailWord_7222370) baseStart_7222370 baseEnd_7222370 := by
    simpa [prefixWord, tailWord_7222370, baseEnd_7222370] using wordTrace_append hprefix tailTrace_7222370
  have hstable : (prefixWord ++ tailWord_7222370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222370).length < 2 ^ (prefixWord ++ tailWord_7222370).sum := by decide
  have hdescent : baseEnd_7222370 < baseStart_7222370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222373 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_7222373 : Nat := 118140960795 + 7222373 * 2 ^ 59
def prefixEnd_7222373 : Nat := 4983230072969 + 3 ^ 40 * 7222373 * 2
def baseEnd_7222373 : Nat := 3708548815054976166122417

theorem tailTrace_7222373 : CollatzResearch.WordTrace tailWord_7222373 prefixEnd_7222373 3708548815054976166122417 := by
  unfold tailWord_7222373
  simp only [CollatzResearch.WordTrace]
  refine ⟨263421584263583578950903773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175614389509055719300602515 263421584263583578950903773)
  ·
    refine ⟨98783094098843842106588915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263421584263583578950903773 98783094098843842106588915)
    ·
      refine ⟨148174641148265763159883373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98783094098843842106588915 148174641148265763159883373)
      ·
        refine ⟨55565490430599661184956265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148174641148265763159883373 55565490430599661184956265)
        ·
          refine ⟨41674117822949745888717199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55565490430599661184956265 41674117822949745888717199)
          ·
            refine ⟨62511176734424618833075799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41674117822949745888717199 62511176734424618833075799)
            ·
              refine ⟨93766765101636928249613699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62511176734424618833075799 93766765101636928249613699)
              ·
                refine ⟨140650147652455392374420549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93766765101636928249613699 140650147652455392374420549)
                ·
                  refine ⟨26371902684835386070203853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140650147652455392374420549 26371902684835386070203853)
                  ·
                    refine ⟨9889463506813269776326445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26371902684835386070203853 9889463506813269776326445)
                    ·
                      refine ⟨3708548815054976166122417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889463506813269776326445 3708548815054976166122417)
                      ·
                        rfl

theorem cell23_7222373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_7222373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222373 prefixEnd_7222373 := by exact prefixLift 7222373
  have htrace : WordTrace (prefixWord ++ tailWord_7222373) baseStart_7222373 baseEnd_7222373 := by
    simpa [prefixWord, tailWord_7222373, baseEnd_7222373] using wordTrace_append hprefix tailTrace_7222373
  have hstable : (prefixWord ++ tailWord_7222373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222373).length < 2 ^ (prefixWord ++ tailWord_7222373).sum := by decide
  have hdescent : baseEnd_7222373 < baseStart_7222373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222390 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7222390 : Nat := 118140960795 + 7222390 * 2 ^ 59
def prefixEnd_7222390 : Nat := 4983230072969 + 3 ^ 40 * 7222390 * 2
def baseEnd_7222390 : Nat := 3708557544226102599609839

theorem tailTrace_7222390 : CollatzResearch.WordTrace tailWord_7222390 prefixEnd_7222390 3708557544226102599609839 := by
  unfold tailWord_7222390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16463887769032624428392039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175614802869681327236181749 16463887769032624428392039)
  ·
    refine ⟨24695831653548936642588059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16463887769032624428392039 24695831653548936642588059)
    ·
      refine ⟨37043747480323404963882089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24695831653548936642588059 37043747480323404963882089)
      ·
        refine ⟨27782810610242553722911567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37043747480323404963882089 27782810610242553722911567)
        ·
          refine ⟨41674215915363830584367351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27782810610242553722911567 41674215915363830584367351)
          ·
            refine ⟨62511323873045745876551027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41674215915363830584367351 62511323873045745876551027)
            ·
              refine ⟨93766985809568618814826541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62511323873045745876551027 93766985809568618814826541)
              ·
                refine ⟨35162619678588232055559953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93766985809568618814826541 35162619678588232055559953)
                ·
                  refine ⟨26371964758941174041669965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35162619678588232055559953 26371964758941174041669965)
                  ·
                    refine ⟨9889486784602940265626237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26371964758941174041669965 9889486784602940265626237)
                    ·
                      refine ⟨3708557544226102599609839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889486784602940265626237 3708557544226102599609839)
                      ·
                        rfl

theorem cell23_7222390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7222390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222390 prefixEnd_7222390 := by exact prefixLift 7222390
  have htrace : WordTrace (prefixWord ++ tailWord_7222390) baseStart_7222390 baseEnd_7222390 := by
    simpa [prefixWord, tailWord_7222390, baseEnd_7222390] using wordTrace_append hprefix tailTrace_7222390
  have hstable : (prefixWord ++ tailWord_7222390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222390).length < 2 ^ (prefixWord ++ tailWord_7222390).sum := by decide
  have hdescent : baseEnd_7222390 < baseStart_7222390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222463 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_7222463 : Nat := 118140960795 + 7222463 * 2 ^ 59
def prefixEnd_7222463 : Nat := 4983230072969 + 3 ^ 40 * 7222463 * 2
def baseEnd_7222463 : Nat := 3708595028313880813997003

theorem tailTrace_7222463 : CollatzResearch.WordTrace tailWord_7222463 prefixEnd_7222463 3708595028313880813997003 := by
  unfold tailWord_7222463
  simp only [CollatzResearch.WordTrace]
  refine ⟨263424866833257524321680043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175616577888838349547786695 263424866833257524321680043)
  ·
    refine ⟨395137300249886286482520065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263424866833257524321680043 395137300249886286482520065)
    ·
      refine ⟨296352975187414714861890049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395137300249886286482520065 296352975187414714861890049)
      ·
        refine ⟨222264731390561036146417537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296352975187414714861890049 222264731390561036146417537)
        ·
          refine ⟨166698548542920777109813153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222264731390561036146417537 166698548542920777109813153)
          ·
            refine ⟨125023911407190582832359865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166698548542920777109813153 125023911407190582832359865)
            ·
              refine ⟨93767933555392937124269899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125023911407190582832359865 93767933555392937124269899)
              ·
                refine ⟨140651900333089405686404849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93767933555392937124269899 140651900333089405686404849)
                ·
                  refine ⟨105488925249817054264803637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140651900333089405686404849 105488925249817054264803637)
                  ·
                    refine ⟨9889586742170348837325341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105488925249817054264803637 9889586742170348837325341)
                    ·
                      refine ⟨3708595028313880813997003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889586742170348837325341 3708595028313880813997003)
                      ·
                        rfl

theorem cell23_7222463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_7222463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222463 prefixEnd_7222463 := by exact prefixLift 7222463
  have htrace : WordTrace (prefixWord ++ tailWord_7222463) baseStart_7222463 baseEnd_7222463 := by
    simpa [prefixWord, tailWord_7222463, baseEnd_7222463] using wordTrace_append hprefix tailTrace_7222463
  have hstable : (prefixWord ++ tailWord_7222463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222463).length < 2 ^ (prefixWord ++ tailWord_7222463).sum := by decide
  have hdescent : baseEnd_7222463 < baseStart_7222463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222490 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2]
def baseStart_7222490 : Nat := 118140960795 + 7222490 * 2 ^ 59
def prefixEnd_7222490 : Nat := 4983230072969 + 3 ^ 40 * 7222490 * 2
def baseEnd_7222490 : Nat := 3708608892291552208359379

theorem tailTrace_7222490 : CollatzResearch.WordTrace tailWord_7222490 prefixEnd_7222490 3708608892291552208359379 := by
  unfold tailWord_7222490
  simp only [CollatzResearch.WordTrace]
  refine ⟨65856462901039926983228231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175617234402773138621941949 65856462901039926983228231)
  ·
    refine ⟨98784694351559890474842347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65856462901039926983228231 98784694351559890474842347)
    ·
      refine ⟨148177041527339835712263521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98784694351559890474842347 148177041527339835712263521)
      ·
        refine ⟨111132781145504876784197641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148177041527339835712263521 111132781145504876784197641)
        ·
          refine ⟨83349585859128657588148231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111132781145504876784197641 83349585859128657588148231)
          ·
            refine ⟨125024378788692986382222347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83349585859128657588148231 125024378788692986382222347)
            ·
              refine ⟨187536568183039479573333521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125024378788692986382222347 187536568183039479573333521)
              ·
                refine ⟨140652426137279609680000141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187536568183039479573333521 140652426137279609680000141)
                ·
                  refine ⟨52744659801479853630000053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140652426137279609680000141 52744659801479853630000053)
                  ·
                    refine ⟨4944811856388736277812505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52744659801479853630000053 4944811856388736277812505)
                    ·
                      refine ⟨3708608892291552208359379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944811856388736277812505 3708608892291552208359379)
                      ·
                        rfl

theorem cell23_7222490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_7222490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222490 prefixEnd_7222490 := by exact prefixLift 7222490
  have htrace : WordTrace (prefixWord ++ tailWord_7222490) baseStart_7222490 baseEnd_7222490 := by
    simpa [prefixWord, tailWord_7222490, baseEnd_7222490] using wordTrace_append hprefix tailTrace_7222490
  have hstable : (prefixWord ++ tailWord_7222490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222490).length < 2 ^ (prefixWord ++ tailWord_7222490).sum := by decide
  have hdescent : baseEnd_7222490 < baseStart_7222490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222514 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7222514 : Nat := 118140960795 + 7222514 * 2 ^ 59
def prefixEnd_7222514 : Nat := 4983230072969 + 3 ^ 40 * 7222514 * 2
def baseEnd_7222514 : Nat := 3708621215827260114459269

theorem tailTrace_7222514 : CollatzResearch.WordTrace tailWord_7222514 prefixEnd_7222514 3708621215827260114459269 := by
  unfold tailWord_7222514
  simp only [CollatzResearch.WordTrace]
  refine ⟨65856681739018190007946649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175617817970715173354524397 65856681739018190007946649)
  ·
    refine ⟨49392511304263642505959987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65856681739018190007946649 49392511304263642505959987)
    ·
      refine ⟨74088766956395463758939981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49392511304263642505959987 74088766956395463758939981)
      ·
        refine ⟨27783287608648298909602493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74088766956395463758939981 27783287608648298909602493)
        ·
          refine ⟨10418732853243112091100935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27783287608648298909602493 10418732853243112091100935)
          ·
            refine ⟨15628099279864668136651403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418732853243112091100935 15628099279864668136651403)
            ·
              refine ⟨23442148919797002204977105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15628099279864668136651403 23442148919797002204977105)
              ·
                refine ⟨17581611689847751653732829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23442148919797002204977105 17581611689847751653732829)
                ·
                  refine ⟨6593104383692906870149811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17581611689847751653732829 6593104383692906870149811)
                  ·
                    refine ⟨9889656575539360305224717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6593104383692906870149811 9889656575539360305224717)
                    ·
                      refine ⟨3708621215827260114459269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889656575539360305224717 3708621215827260114459269)
                      ·
                        rfl

theorem cell23_7222514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7222514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222514 prefixEnd_7222514 := by exact prefixLift 7222514
  have htrace : WordTrace (prefixWord ++ tailWord_7222514) baseStart_7222514 baseEnd_7222514 := by
    simpa [prefixWord, tailWord_7222514, baseEnd_7222514] using wordTrace_append hprefix tailTrace_7222514
  have hstable : (prefixWord ++ tailWord_7222514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222514).length < 2 ^ (prefixWord ++ tailWord_7222514).sum := by decide
  have hdescent : baseEnd_7222514 < baseStart_7222514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222537 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 5, 2, 2]
def baseStart_7222537 : Nat := 118140960795 + 7222537 * 2 ^ 59
def prefixEnd_7222537 : Nat := 4983230072969 + 3 ^ 40 * 7222537 * 2
def baseEnd_7222537 : Nat := 3708633025882313524471663

theorem tailTrace_7222537 : CollatzResearch.WordTrace tailWord_7222537 prefixEnd_7222537 3708633025882313524471663 := by
  unfold tailWord_7222537
  simp only [CollatzResearch.WordTrace]
  refine ⟨263427565834989434959873865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175618377223326289973249243 263427565834989434959873865)
  ·
    refine ⟨197570674376242076219905399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263427565834989434959873865 197570674376242076219905399)
    ·
      refine ⟨296356011564363114329858099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197570674376242076219905399 296356011564363114329858099)
      ·
        refine ⟨444534017346544671494787149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296356011564363114329858099 444534017346544671494787149)
        ·
          refine ⟨166700256504954251810545181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444534017346544671494787149 166700256504954251810545181)
          ·
            refine ⟨62512596189357844428954443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166700256504954251810545181 62512596189357844428954443)
            ·
              refine ⟨93768894284036766643431665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62512596189357844428954443 93768894284036766643431665)
              ·
                refine ⟨70326670713027574982573749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93768894284036766643431665 70326670713027574982573749)
                ·
                  refine ⟨6593125379346335154616289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70326670713027574982573749 6593125379346335154616289)
                  ·
                    refine ⟨4944844034509751365962217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593125379346335154616289 4944844034509751365962217)
                    ·
                      refine ⟨3708633025882313524471663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944844034509751365962217 3708633025882313524471663)
                      ·
                        rfl

theorem cell23_7222537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 2, 2].length) (baseStart_7222537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222537 prefixEnd_7222537 := by exact prefixLift 7222537
  have htrace : WordTrace (prefixWord ++ tailWord_7222537) baseStart_7222537 baseEnd_7222537 := by
    simpa [prefixWord, tailWord_7222537, baseEnd_7222537] using wordTrace_append hprefix tailTrace_7222537
  have hstable : (prefixWord ++ tailWord_7222537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222537).length < 2 ^ (prefixWord ++ tailWord_7222537).sum := by decide
  have hdescent : baseEnd_7222537 < baseStart_7222537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222554 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2]
def baseStart_7222554 : Nat := 118140960795 + 7222554 * 2 ^ 59
def prefixEnd_7222554 : Nat := 4983230072969 + 3 ^ 40 * 7222554 * 2
def baseEnd_7222554 : Nat := 3708641755053439957959085

theorem tailTrace_7222554 : CollatzResearch.WordTrace tailWord_7222554 prefixEnd_7222554 3708641755053439957959085 := by
  unfold tailWord_7222554
  simp only [CollatzResearch.WordTrace]
  refine ⟨65857046468981961715810679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175618790583951897908828477 65857046468981961715810679)
  ·
    refine ⟨98785569703472942573716019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65857046468981961715810679 98785569703472942573716019)
    ·
      refine ⟨148178354555209413860574029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98785569703472942573716019 148178354555209413860574029)
      ·
        refine ⟨55566882958203530197715261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148178354555209413860574029 55566882958203530197715261)
        ·
          refine ⟨20837581109326323824143223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55566882958203530197715261 20837581109326323824143223)
          ·
            refine ⟨31256371663989485736214835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20837581109326323824143223 31256371663989485736214835)
            ·
              refine ⟨46884557495984228604322253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31256371663989485736214835 46884557495984228604322253)
              ·
                refine ⟨17581709060994085726620845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46884557495984228604322253 17581709060994085726620845)
                ·
                  refine ⟨6593140897872782147482817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17581709060994085726620845 6593140897872782147482817)
                  ·
                    refine ⟨4944855673404586610612113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593140897872782147482817 4944855673404586610612113)
                    ·
                      refine ⟨3708641755053439957959085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944855673404586610612113 3708641755053439957959085)
                      ·
                        rfl

theorem cell23_7222554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_7222554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222554 prefixEnd_7222554 := by exact prefixLift 7222554
  have htrace : WordTrace (prefixWord ++ tailWord_7222554) baseStart_7222554 baseEnd_7222554 := by
    simpa [prefixWord, tailWord_7222554, baseEnd_7222554] using wordTrace_append hprefix tailTrace_7222554
  have hstable : (prefixWord ++ tailWord_7222554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222554).length < 2 ^ (prefixWord ++ tailWord_7222554).sum := by decide
  have hdescent : baseEnd_7222554 < baseStart_7222554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222557 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7222557 : Nat := 118140960795 + 7222557 * 2 ^ 59
def prefixEnd_7222557 : Nat := 4983230072969 + 3 ^ 40 * 7222557 * 2
def baseEnd_7222557 : Nat := 3708643295495403446221571

theorem tailTrace_7222557 : CollatzResearch.WordTrace tailWord_7222557 prefixEnd_7222557 3708643295495403446221571 := by
  unfold tailWord_7222557
  simp only [CollatzResearch.WordTrace]
  refine ⟨263428295294916978375601925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175618863529944652250401283 263428295294916978375601925)
  ·
    refine ⟨49392805367796933445425361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263428295294916978375601925 49392805367796933445425361)
    ·
      refine ⟨37044604025847700084069021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49392805367796933445425361 37044604025847700084069021)
      ·
        refine ⟨13891726509692887531525883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37044604025847700084069021 13891726509692887531525883)
        ·
          refine ⟨20837589764539331297288825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891726509692887531525883 20837589764539331297288825)
          ·
            refine ⟨15628192323404498472966619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20837589764539331297288825 15628192323404498472966619)
            ·
              refine ⟨23442288485106747709449929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15628192323404498472966619 23442288485106747709449929)
              ·
                refine ⟨17581716363830060782087447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23442288485106747709449929 17581716363830060782087447)
                ·
                  refine ⟨26372574545745091173131171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17581716363830060782087447 26372574545745091173131171)
                  ·
                    refine ⟨39558861818617636759696757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26372574545745091173131171 39558861818617636759696757)
                    ·
                      refine ⟨3708643295495403446221571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39558861818617636759696757 3708643295495403446221571)
                      ·
                        rfl

theorem cell23_7222557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7222557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222557 prefixEnd_7222557 := by exact prefixLift 7222557
  have htrace : WordTrace (prefixWord ++ tailWord_7222557) baseStart_7222557 baseEnd_7222557 := by
    simpa [prefixWord, tailWord_7222557, baseEnd_7222557] using wordTrace_append hprefix tailTrace_7222557
  have hstable : (prefixWord ++ tailWord_7222557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222557).length < 2 ^ (prefixWord ++ tailWord_7222557).sum := by decide
  have hdescent : baseEnd_7222557 < baseStart_7222557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222564 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_7222564 : Nat := 118140960795 + 7222564 * 2 ^ 59
def prefixEnd_7222564 : Nat := 4983230072969 + 3 ^ 40 * 7222564 * 2
def baseEnd_7222564 : Nat := 1236215629953328306278013

theorem tailTrace_7222564 : CollatzResearch.WordTrace tailWord_7222564 prefixEnd_7222564 1236215629953328306278013 := by
  unfold tailWord_7222564
  simp only [CollatzResearch.WordTrace]
  refine ⟨131714275302945809285553373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175619033737261079047404497 131714275302945809285553373)
  ·
    refine ⟨49392853238604678482082515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131714275302945809285553373 49392853238604678482082515)
    ·
      refine ⟨74089279857907017723123773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49392853238604678482082515 74089279857907017723123773)
      ·
        refine ⟨27783479946715131646171415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74089279857907017723123773 27783479946715131646171415)
        ·
          refine ⟨41675219920072697469257123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27783479946715131646171415 41675219920072697469257123)
          ·
            refine ⟨62512829880109046203885685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41675219920072697469257123 62512829880109046203885685)
            ·
              refine ⟨5860577801260223081614283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62512829880109046203885685 5860577801260223081614283)
              ·
                refine ⟨8790866701890334622421425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5860577801260223081614283 8790866701890334622421425)
                ·
                  refine ⟨6593150026417750966816069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8790866701890334622421425 6593150026417750966816069)
                  ·
                    refine ⟨1236215629953328306278013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593150026417750966816069 1236215629953328306278013)
                    ·
                      rfl

theorem cell23_7222564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_7222564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222564 prefixEnd_7222564 := by exact prefixLift 7222564
  have htrace : WordTrace (prefixWord ++ tailWord_7222564) baseStart_7222564 baseEnd_7222564 := by
    simpa [prefixWord, tailWord_7222564, baseEnd_7222564] using wordTrace_append hprefix tailTrace_7222564
  have hstable : (prefixWord ++ tailWord_7222564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222564).length < 2 ^ (prefixWord ++ tailWord_7222564).sum := by decide
  have hdescent : baseEnd_7222564 < baseStart_7222564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222577 : List Nat := [1, 2, 2, 3, 3, 3, 2, 7]
def baseStart_7222577 : Nat := 118140960795 + 7222577 * 2 ^ 59
def prefixEnd_7222577 : Nat := 4983230072969 + 3 ^ 40 * 7222577 * 2
def baseEnd_7222577 : Nat := 137357539448462717332277

theorem tailTrace_7222577 : CollatzResearch.WordTrace tailWord_7222577 prefixEnd_7222577 137357539448462717332277 := by
  unfold tailWord_7222577
  simp only [CollatzResearch.WordTrace]
  refine ⟨263429024754844521791329985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175619349836563014527553323 263429024754844521791329985)
  ·
    refine ⟨197571768566133391343497489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263429024754844521791329985 197571768566133391343497489)
    ·
      refine ⟨148178826424600043507623117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197571768566133391343497489 148178826424600043507623117)
      ·
        refine ⟨55567059909225016315358669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148178826424600043507623117 55567059909225016315358669)
        ·
          refine ⟨20837647465959381118259501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55567059909225016315358669 20837647465959381118259501)
          ·
            refine ⟨7814117799734767919347313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20837647465959381118259501 7814117799734767919347313)
            ·
              refine ⟨5860588349801075939510485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7814117799734767919347313 5860588349801075939510485)
              ·
                refine ⟨137357539448462717332277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5860588349801075939510485 137357539448462717332277)
                ·
                  rfl

theorem cell23_7222577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 7].length) (baseStart_7222577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222577 prefixEnd_7222577 := by exact prefixLift 7222577
  have htrace : WordTrace (prefixWord ++ tailWord_7222577) baseStart_7222577 baseEnd_7222577 := by
    simpa [prefixWord, tailWord_7222577, baseEnd_7222577] using wordTrace_append hprefix tailTrace_7222577
  have hstable : (prefixWord ++ tailWord_7222577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222577).length < 2 ^ (prefixWord ++ tailWord_7222577).sum := by decide
  have hdescent : baseEnd_7222577 < baseStart_7222577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222582 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7222582 : Nat := 118140960795 + 7222582 * 2 ^ 59
def prefixEnd_7222582 : Nat := 4983230072969 + 3 ^ 40 * 7222582 * 2
def baseEnd_7222582 : Nat := 3708656132511765848408957

theorem tailTrace_7222582 : CollatzResearch.WordTrace tailWord_7222582 prefixEnd_7222582 3708656132511765848408957 := by
  unfold tailWord_7222582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464325444989150477828875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175619471413217605096841333 16464325444989150477828875)
  ·
    refine ⟨24696488167483725716743313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16464325444989150477828875 24696488167483725716743313)
    ·
      refine ⟨18522366125612794287557485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24696488167483725716743313 18522366125612794287557485)
      ·
        refine ⟨6945887297104797857834057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18522366125612794287557485 6945887297104797857834057)
        ·
          refine ⟨5209415472828598393375543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6945887297104797857834057 5209415472828598393375543)
          ·
            refine ⟨7814123209242897590063315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209415472828598393375543 7814123209242897590063315)
            ·
              refine ⟨11721184813864346385094973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814123209242897590063315 11721184813864346385094973)
              ·
                refine ⟨4395444305199129894410615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11721184813864346385094973 4395444305199129894410615)
                ·
                  refine ⟨6593166457798694841615923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395444305199129894410615 6593166457798694841615923)
                  ·
                    refine ⟨9889749686698042262423885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6593166457798694841615923 9889749686698042262423885)
                    ·
                      refine ⟨3708656132511765848408957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9889749686698042262423885 3708656132511765848408957)
                      ·
                        rfl

theorem cell23_7222582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7222582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222582 prefixEnd_7222582 := by exact prefixLift 7222582
  have htrace : WordTrace (prefixWord ++ tailWord_7222582) baseStart_7222582 baseEnd_7222582 := by
    simpa [prefixWord, tailWord_7222582, baseEnd_7222582] using wordTrace_append hprefix tailTrace_7222582
  have hstable : (prefixWord ++ tailWord_7222582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222582).length < 2 ^ (prefixWord ++ tailWord_7222582).sum := by decide
  have hdescent : baseEnd_7222582 < baseStart_7222582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222588 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_7222588 : Nat := 118140960795 + 7222588 * 2 ^ 59
def prefixEnd_7222588 : Nat := 4983230072969 + 3 ^ 40 * 7222588 * 2
def baseEnd_7222588 : Nat := 3708659213395692824933929

theorem tailTrace_7222588 : CollatzResearch.WordTrace tailWord_7222588 prefixEnd_7222588 3708659213395692824933929 := by
  unfold tailWord_7222588
  simp only [CollatzResearch.WordTrace]
  refine ⟨131714712978902335334990209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175619617305203113779986945 131714712978902335334990209)
  ·
    refine ⟨98786034734176751501242657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131714712978902335334990209 98786034734176751501242657)
    ·
      refine ⟨74089526050632563625931993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98786034734176751501242657 74089526050632563625931993)
      ·
        refine ⟨55567144537974422719448995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74089526050632563625931993 55567144537974422719448995)
        ·
          refine ⟨83350716806961634079173493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55567144537974422719448995 83350716806961634079173493)
          ·
            refine ⟨7814129700652653194922515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83350716806961634079173493 7814129700652653194922515)
            ·
              refine ⟨11721194550978979792383773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814129700652653194922515 11721194550978979792383773)
              ·
                refine ⟨4395447956617117422143915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11721194550978979792383773 4395447956617117422143915)
                ·
                  refine ⟨6593171934925676133215873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395447956617117422143915 6593171934925676133215873)
                  ·
                    refine ⟨4944878951194257099911905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593171934925676133215873 4944878951194257099911905)
                    ·
                      refine ⟨3708659213395692824933929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944878951194257099911905 3708659213395692824933929)
                      ·
                        rfl

theorem cell23_7222588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_7222588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222588 prefixEnd_7222588 := by exact prefixLift 7222588
  have htrace : WordTrace (prefixWord ++ tailWord_7222588) baseStart_7222588 baseEnd_7222588 := by
    simpa [prefixWord, tailWord_7222588, baseEnd_7222588] using wordTrace_append hprefix tailTrace_7222588
  have hstable : (prefixWord ++ tailWord_7222588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222588).length < 2 ^ (prefixWord ++ tailWord_7222588).sum := by decide
  have hdescent : baseEnd_7222588 < baseStart_7222588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222605 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7222605 : Nat := 118140960795 + 7222605 * 2 ^ 59
def prefixEnd_7222605 : Nat := 4983230072969 + 3 ^ 40 * 7222605 * 2
def baseEnd_7222605 : Nat := 3708667942566819258421351

theorem tailTrace_7222605 : CollatzResearch.WordTrace tailWord_7222605 prefixEnd_7222605 3708667942566819258421351 := by
  unfold tailWord_7222605
  simp only [CollatzResearch.WordTrace]
  refine ⟨263430045998743082573349269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175620030665828721715566179 263430045998743082573349269)
  ·
    refine ⟨12348283406191081995625747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263430045998743082573349269 12348283406191081995625747)
    ·
      refine ⟨18522425109286622993438621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348283406191081995625747 18522425109286622993438621)
      ·
        refine ⟨6945909415982483622539483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18522425109286622993438621 6945909415982483622539483)
        ·
          refine ⟨10418864123973725433809225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945909415982483622539483 10418864123973725433809225)
          ·
            refine ⟨7814148092980294075356919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10418864123973725433809225 7814148092980294075356919)
            ·
              refine ⟨11721222139470441113035379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814148092980294075356919 11721222139470441113035379)
              ·
                refine ⟨17581833209205661669553069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11721222139470441113035379 17581833209205661669553069)
                ·
                  refine ⟨6593187453452123126082401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17581833209205661669553069 6593187453452123126082401)
                  ·
                    refine ⟨4944890590089092344561801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593187453452123126082401 4944890590089092344561801)
                    ·
                      refine ⟨3708667942566819258421351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944890590089092344561801 3708667942566819258421351)
                      ·
                        rfl

theorem cell23_7222605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7222605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222605 prefixEnd_7222605 := by exact prefixLift 7222605
  have htrace : WordTrace (prefixWord ++ tailWord_7222605) baseStart_7222605 baseEnd_7222605 := by
    simpa [prefixWord, tailWord_7222605, baseEnd_7222605] using wordTrace_append hprefix tailTrace_7222605
  have hstable : (prefixWord ++ tailWord_7222605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222605).length < 2 ^ (prefixWord ++ tailWord_7222605).sum := by decide
  have hdescent : baseEnd_7222605 < baseStart_7222605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222610 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7222610 : Nat := 118140960795 + 7222610 * 2 ^ 59
def prefixEnd_7222610 : Nat := 4983230072969 + 3 ^ 40 * 7222610 * 2
def baseEnd_7222610 : Nat := 3708670509970091738858827

theorem tailTrace_7222610 : CollatzResearch.WordTrace tailWord_7222610 prefixEnd_7222610 3708670509970091738858827 := by
  unfold tailWord_7222610
  simp only [CollatzResearch.WordTrace]
  refine ⟨65857557090931242106820321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175620152242483312284854189 65857557090931242106820321)
  ·
    refine ⟨49393167818198431580115241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65857557090931242106820321 49393167818198431580115241)
    ·
      refine ⟨37044875863648823685086431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49393167818198431580115241 37044875863648823685086431)
      ·
        refine ⟨55567313795473235527629647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37044875863648823685086431 55567313795473235527629647)
        ·
          refine ⟨83350970693209853291444471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55567313795473235527629647 83350970693209853291444471)
          ·
            refine ⟨125026456039814779937166707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83350970693209853291444471 125026456039814779937166707)
            ·
              refine ⟨187539684059722169905750061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125026456039814779937166707 187539684059722169905750061)
              ·
                refine ⟨70327381522395813714656273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187539684059722169905750061 70327381522395813714656273)
                ·
                  refine ⟨52745536141796860285992205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70327381522395813714656273 52745536141796860285992205)
                  ·
                    refine ⟨19779576053173822607247077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52745536141796860285992205 19779576053173822607247077)
                    ·
                      refine ⟨3708670509970091738858827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19779576053173822607247077 3708670509970091738858827)
                      ·
                        rfl

theorem cell23_7222610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7222610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222610 prefixEnd_7222610 := by exact prefixLift 7222610
  have htrace : WordTrace (prefixWord ++ tailWord_7222610) baseStart_7222610 baseEnd_7222610 := by
    simpa [prefixWord, tailWord_7222610, baseEnd_7222610] using wordTrace_append hprefix tailTrace_7222610
  have hstable : (prefixWord ++ tailWord_7222610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222610).length < 2 ^ (prefixWord ++ tailWord_7222610).sum := by decide
  have hdescent : baseEnd_7222610 < baseStart_7222610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222667 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 5]
def baseStart_7222667 : Nat := 118140960795 + 7222667 * 2 ^ 59
def prefixEnd_7222667 : Nat := 4983230072969 + 3 ^ 40 * 7222667 * 2
def baseEnd_7222667 : Nat := 412077753151933112871785

theorem tailTrace_7222667 : CollatzResearch.WordTrace tailWord_7222667 prefixEnd_7222667 412077753151933112871785 := by
  unfold tailWord_7222667
  simp only [CollatzResearch.WordTrace]
  refine ⟨263432307324518467162106255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175621538216345644774737503 263432307324518467162106255)
  ·
    refine ⟨395148460986777700743159383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263432307324518467162106255 395148460986777700743159383)
    ·
      refine ⟨592722691480166551114739075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395148460986777700743159383 592722691480166551114739075)
      ·
        refine ⟨889084037220249826672108613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592722691480166551114739075 889084037220249826672108613)
        ·
          refine ⟨166703256978796842501020365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 889084037220249826672108613 166703256978796842501020365)
          ·
            refine ⟨62513721367048815937882637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166703256978796842501020365 62513721367048815937882637)
            ·
              refine ⟨23442645512643305976705989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62513721367048815937882637 23442645512643305976705989)
              ·
                refine ⟨4395496033620619870632373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23442645512643305976705989 4395496033620619870632373)
                ·
                  refine ⟨412077753151933112871785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4395496033620619870632373 412077753151933112871785)
                  ·
                    rfl

theorem cell23_7222667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 5].length) (baseStart_7222667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222667 prefixEnd_7222667 := by exact prefixLift 7222667
  have htrace : WordTrace (prefixWord ++ tailWord_7222667) baseStart_7222667 baseEnd_7222667 := by
    simpa [prefixWord, tailWord_7222667, baseEnd_7222667] using wordTrace_append hprefix tailTrace_7222667
  have hstable : (prefixWord ++ tailWord_7222667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222667).length < 2 ^ (prefixWord ++ tailWord_7222667).sum := by decide
  have hdescent : baseEnd_7222667 < baseStart_7222667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222684 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 7]
def baseStart_7222684 : Nat := 118140960795 + 7222684 * 2 ^ 59
def prefixEnd_7222684 : Nat := 4983230072969 + 3 ^ 40 * 7222684 * 2
def baseEnd_7222684 : Nat := 412078723059836049925943

theorem tailTrace_7222684 : CollatzResearch.WordTrace tailWord_7222684 prefixEnd_7222684 412078723059836049925943 := by
  unfold tailWord_7222684
  simp only [CollatzResearch.WordTrace]
  refine ⟨131716463682728439532737553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175621951576971252710316737 131716463682728439532737553)
  ·
    refine ⟨98787347762046329649553165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131716463682728439532737553 98787347762046329649553165)
    ·
      refine ⟨37045255410767373618582437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98787347762046329649553165 37045255410767373618582437)
      ·
        refine ⟨6945985389518882553484207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37045255410767373618582437 6945985389518882553484207)
        ·
          refine ⟨10418978084278323830226311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945985389518882553484207 10418978084278323830226311)
          ·
            refine ⟨15628467126417485745339467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418978084278323830226311 15628467126417485745339467)
            ·
              refine ⟨23442700689626228618009201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15628467126417485745339467 23442700689626228618009201)
              ·
                refine ⟨17582025517219671463506901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23442700689626228618009201 17582025517219671463506901)
                ·
                  refine ⟨412078723059836049925943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17582025517219671463506901 412078723059836049925943)
                  ·
                    rfl

theorem cell23_7222684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_7222684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222684 prefixEnd_7222684 := by exact prefixLift 7222684
  have htrace : WordTrace (prefixWord ++ tailWord_7222684) baseStart_7222684 baseEnd_7222684 := by
    simpa [prefixWord, tailWord_7222684, baseEnd_7222684] using wordTrace_append hprefix tailTrace_7222684
  have hstable : (prefixWord ++ tailWord_7222684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222684).length < 2 ^ (prefixWord ++ tailWord_7222684).sum := by decide
  have hdescent : baseEnd_7222684 < baseStart_7222684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222701 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 5]
def baseStart_7222701 : Nat := 118140960795 + 7222701 * 2 ^ 59
def prefixEnd_7222701 : Nat := 4983230072969 + 3 ^ 40 * 7222701 * 2
def baseEnd_7222701 : Nat := 412079692967738986980101

theorem tailTrace_7222701 : CollatzResearch.WordTrace tailWord_7222701 prefixEnd_7222701 412079692967738986980101 := by
  unfold tailWord_7222701
  simp only [CollatzResearch.WordTrace]
  refine ⟨263433547406395290968843957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175622364937596860645895971 263433547406395290968843957)
  ·
    refine ⟨24696895069349558528329121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263433547406395290968843957 24696895069349558528329121)
    ·
      refine ⟨18522671302012168896246841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24696895069349558528329121 18522671302012168896246841)
      ·
        refine ⟨13892003476509126672185131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18522671302012168896246841 13892003476509126672185131)
        ·
          refine ⟨20838005214763690008277697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13892003476509126672185131 20838005214763690008277697)
          ·
            refine ⟨15628503911072767506208273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20838005214763690008277697 15628503911072767506208273)
            ·
              refine ⟨11721377933304575629656205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15628503911072767506208273 11721377933304575629656205)
              ·
                refine ⟨4395516724989215861121077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11721377933304575629656205 4395516724989215861121077)
                ·
                  refine ⟨412079692967738986980101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4395516724989215861121077 412079692967738986980101)
                  ·
                    rfl

theorem cell23_7222701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_7222701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222701 prefixEnd_7222701 := by exact prefixLift 7222701
  have htrace : WordTrace (prefixWord ++ tailWord_7222701) baseStart_7222701 baseEnd_7222701 := by
    simpa [prefixWord, tailWord_7222701, baseEnd_7222701] using wordTrace_append hprefix tailTrace_7222701
  have hstable : (prefixWord ++ tailWord_7222701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222701).length < 2 ^ (prefixWord ++ tailWord_7222701).sum := by decide
  have hdescent : baseEnd_7222701 < baseStart_7222701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222717 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7222717 : Nat := 118140960795 + 7222717 * 2 ^ 59
def prefixEnd_7222717 : Nat := 4983230072969 + 3 ^ 40 * 7222717 * 2
def baseEnd_7222717 : Nat := 3708725452400122820220835

theorem tailTrace_7222717 : CollatzResearch.WordTrace tailWord_7222717 prefixEnd_7222717 3708725452400122820220835 := by
  unfold tailWord_7222717
  simp only [CollatzResearch.WordTrace]
  refine ⟨263434130974337325701426405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175622753982891550467617603 263434130974337325701426405)
  ·
    refine ⟨49393899557688248569017451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263434130974337325701426405 49393899557688248569017451)
    ·
      refine ⟨74090849336532372853526177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49393899557688248569017451 74090849336532372853526177)
      ·
        refine ⟨55568137002399279640144633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74090849336532372853526177 55568137002399279640144633)
        ·
          refine ⟨41676102751799459730108475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55568137002399279640144633 41676102751799459730108475)
          ·
            refine ⟨62514154127699189595162713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41676102751799459730108475 62514154127699189595162713)
            ·
              refine ⟨46885615595774392196372035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62514154127699189595162713 46885615595774392196372035)
              ·
                refine ⟨70328423393661588294558053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46885615595774392196372035 70328423393661588294558053)
                ·
                  refine ⟨13186579386311547805229635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70328423393661588294558053 13186579386311547805229635)
                  ·
                    refine ⟨19779869079467321707844453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13186579386311547805229635 19779869079467321707844453)
                    ·
                      refine ⟨3708725452400122820220835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19779869079467321707844453 3708725452400122820220835)
                      ·
                        rfl

theorem cell23_7222717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7222717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222717 prefixEnd_7222717 := by exact prefixLift 7222717
  have htrace : WordTrace (prefixWord ++ tailWord_7222717) baseStart_7222717 baseEnd_7222717 := by
    simpa [prefixWord, tailWord_7222717, baseEnd_7222717] using wordTrace_append hprefix tailTrace_7222717
  have hstable : (prefixWord ++ tailWord_7222717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222717).length < 2 ^ (prefixWord ++ tailWord_7222717).sum := by decide
  have hdescent : baseEnd_7222717 < baseStart_7222717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222720 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_7222720 : Nat := 118140960795 + 7222720 * 2 ^ 59
def prefixEnd_7222720 : Nat := 4983230072969 + 3 ^ 40 * 7222720 * 2
def baseEnd_7222720 : Nat := 3708726992842086308483321

theorem tailTrace_7222720 : CollatzResearch.WordTrace tailWord_7222720 prefixEnd_7222720 3708726992842086308483321 := by
  unfold tailWord_7222720
  simp only [CollatzResearch.WordTrace]
  refine ⟨131717120196663228606892807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175622826928884304809190409 131717120196663228606892807)
  ·
    refine ⟨197575680294994842910339211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131717120196663228606892807 197575680294994842910339211)
    ·
      refine ⟨296363520442492264365508817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197575680294994842910339211 296363520442492264365508817)
      ·
        refine ⟨222272640331869198274131613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296363520442492264365508817 222272640331869198274131613)
        ·
          refine ⟨83352240124450949352799355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222272640331869198274131613 83352240124450949352799355)
          ·
            refine ⟨125028360186676424029199033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83352240124450949352799355 125028360186676424029199033)
            ·
              refine ⟨93771270140007318021899275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125028360186676424029199033 93771270140007318021899275)
              ·
                refine ⟨140656905210010977032848913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93771270140007318021899275 140656905210010977032848913)
                ·
                  refine ⟨105492678907508232774636685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140656905210010977032848913 105492678907508232774636685)
                  ·
                    refine ⟨39559754590315587290488757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105492678907508232774636685 39559754590315587290488757)
                    ·
                      refine ⟨3708726992842086308483321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39559754590315587290488757 3708726992842086308483321)
                      ·
                        rfl

theorem cell23_7222720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_7222720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222720 prefixEnd_7222720 := by exact prefixLift 7222720
  have htrace : WordTrace (prefixWord ++ tailWord_7222720) baseStart_7222720 baseEnd_7222720 := by
    simpa [prefixWord, tailWord_7222720, baseEnd_7222720] using wordTrace_append hprefix tailTrace_7222720
  have hstable : (prefixWord ++ tailWord_7222720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222720).length < 2 ^ (prefixWord ++ tailWord_7222720).sum := by decide
  have hdescent : baseEnd_7222720 < baseStart_7222720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222734 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_7222734 : Nat := 118140960795 + 7222734 * 2 ^ 59
def prefixEnd_7222734 : Nat := 4983230072969 + 3 ^ 40 * 7222734 * 2
def baseEnd_7222734 : Nat := 3708734181571249253708257

theorem tailTrace_7222734 : CollatzResearch.WordTrace tailWord_7222734 prefixEnd_7222734 3708734181571249253708257 := by
  unfold tailWord_7222734
  simp only [CollatzResearch.WordTrace]
  refine ⟨32929343876909467200599407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175623167343517158403196837 32929343876909467200599407)
  ·
    refine ⟨49394015815364200800899111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32929343876909467200599407 49394015815364200800899111)
    ·
      refine ⟨74091023723046301201348667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49394015815364200800899111 74091023723046301201348667)
      ·
        refine ⟨111136535584569451802023001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74091023723046301201348667 111136535584569451802023001)
        ·
          refine ⟨83352401688427088851517251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111136535584569451802023001 83352401688427088851517251)
          ·
            refine ⟨125028602532640633277275877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83352401688427088851517251 125028602532640633277275877)
            ·
              refine ⟨23442862974870118739489227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125028602532640633277275877 23442862974870118739489227)
              ·
                refine ⟨35164294462305178109233841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23442862974870118739489227 35164294462305178109233841)
                ·
                  refine ⟨26373220846728883581925381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35164294462305178109233841 26373220846728883581925381)
                  ·
                    refine ⟨4944978908761665671611009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26373220846728883581925381 4944978908761665671611009)
                    ·
                      refine ⟨3708734181571249253708257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4944978908761665671611009 3708734181571249253708257)
                      ·
                        rfl

theorem cell23_7222734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_7222734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222734 prefixEnd_7222734 := by exact prefixLift 7222734
  have htrace : WordTrace (prefixWord ++ tailWord_7222734) baseStart_7222734 baseEnd_7222734 := by
    simpa [prefixWord, tailWord_7222734, baseEnd_7222734] using wordTrace_append hprefix tailTrace_7222734
  have hstable : (prefixWord ++ tailWord_7222734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222734).length < 2 ^ (prefixWord ++ tailWord_7222734).sum := by decide
  have hdescent : baseEnd_7222734 < baseStart_7222734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222757 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 8]
def baseStart_7222757 : Nat := 118140960795 + 7222757 * 2 ^ 59
def prefixEnd_7222757 : Nat := 4983230072969 + 3 ^ 40 * 7222757 * 2
def baseEnd_7222757 : Nat := 412082887958478073746739

theorem tailTrace_7222757 : CollatzResearch.WordTrace tailWord_7222757 prefixEnd_7222757 412082887958478073746739 := by
  unfold tailWord_7222757
  simp only [CollatzResearch.WordTrace]
  refine ⟨263435589894192412532882525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175623726596128275021921683 263435589894192412532882525)
  ·
    refine ⟨98788346210322154699830947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263435589894192412532882525 98788346210322154699830947)
    ·
      refine ⟨148182519315483232049746421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98788346210322154699830947 148182519315483232049746421)
      ·
        refine ⟨13892111185826553004663727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148182519315483232049746421 13892111185826553004663727)
        ·
          refine ⟨20838166778739829506995591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13892111185826553004663727 20838166778739829506995591)
          ·
            refine ⟨31257250168109744260493387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20838166778739829506995591 31257250168109744260493387)
            ·
              refine ⟨46885875252164616390740081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31257250168109744260493387 46885875252164616390740081)
              ·
                refine ⟨35164406439123462293055061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46885875252164616390740081 35164406439123462293055061)
                ·
                  refine ⟨412082887958478073746739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35164406439123462293055061 412082887958478073746739)
                  ·
                    rfl

theorem cell23_7222757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_7222757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222757 prefixEnd_7222757 := by exact prefixLift 7222757
  have htrace : WordTrace (prefixWord ++ tailWord_7222757) baseStart_7222757 baseEnd_7222757 := by
    simpa [prefixWord, tailWord_7222757, baseEnd_7222757] using wordTrace_append hprefix tailTrace_7222757
  have hstable : (prefixWord ++ tailWord_7222757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222757).length < 2 ^ (prefixWord ++ tailWord_7222757).sum := by decide
  have hdescent : baseEnd_7222757 < baseStart_7222757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222791 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 6]
def baseStart_7222791 : Nat := 118140960795 + 7222791 * 2 ^ 59
def prefixEnd_7222791 : Nat := 4983230072969 + 3 ^ 40 * 7222791 * 2
def baseEnd_7222791 : Nat := 412084827774283947855055

theorem tailTrace_7222791 : CollatzResearch.WordTrace tailWord_7222791 prefixEnd_7222791 412084827774283947855055 := by
  unfold tailWord_7222791
  simp only [CollatzResearch.WordTrace]
  refine ⟨263436829976069236339620227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175624553317379490893080151 263436829976069236339620227)
  ·
    refine ⟨395155244964103854509430341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263436829976069236339620227 395155244964103854509430341)
    ·
      refine ⟨74091608430769472720518189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395155244964103854509430341 74091608430769472720518189)
      ·
        refine ⟨27784353161538552270194321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74091608430769472720518189 27784353161538552270194321)
        ·
          refine ⟨20838264871153914202645741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27784353161538552270194321 20838264871153914202645741)
          ·
            refine ⟨7814349326682717825992153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20838264871153914202645741 7814349326682717825992153)
            ·
              refine ⟨5860761995012038369494115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7814349326682717825992153 5860761995012038369494115)
              ·
                refine ⟨8791142992518057554241173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5860761995012038369494115 8791142992518057554241173)
                ·
                  refine ⟨412084827774283947855055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8791142992518057554241173 412084827774283947855055)
                  ·
                    rfl

theorem cell23_7222791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 6].length) (baseStart_7222791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222791 prefixEnd_7222791 := by exact prefixLift 7222791
  have htrace : WordTrace (prefixWord ++ tailWord_7222791) baseStart_7222791 baseEnd_7222791 := by
    simpa [prefixWord, tailWord_7222791, baseEnd_7222791] using wordTrace_append hprefix tailTrace_7222791
  have hstable : (prefixWord ++ tailWord_7222791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222791).length < 2 ^ (prefixWord ++ tailWord_7222791).sum := by decide
  have hdescent : baseEnd_7222791 < baseStart_7222791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_7222800 : Nat := 118140960795 + 7222800 * 2 ^ 59
def prefixEnd_7222800 : Nat := 4983230072969 + 3 ^ 40 * 7222800 * 2
def baseEnd_7222800 : Nat := 1236256023764815331827651

theorem tailTrace_7222800 : CollatzResearch.WordTrace tailWord_7222800 prefixEnd_7222800 1236256023764815331827651 := by
  unfold tailWord_7222800
  simp only [CollatzResearch.WordTrace]
  refine ⟨131718579116518315438348927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175624772155357753917798569 131718579116518315438348927)
  ·
    refine ⟨197577868674777473157523391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131718579116518315438348927 197577868674777473157523391)
    ·
      refine ⟨296366803012166209736285087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197577868674777473157523391 296366803012166209736285087)
      ·
        refine ⟨444550204518249314604427631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296366803012166209736285087 444550204518249314604427631)
        ·
          refine ⟨666825306777373971906641447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444550204518249314604427631 666825306777373971906641447)
          ·
            refine ⟨1000237960166060957859962171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666825306777373971906641447 1000237960166060957859962171)
            ·
              refine ⟨1500356940249091436789943257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000237960166060957859962171 1500356940249091436789943257)
              ·
                refine ⟨1125267705186818577592457443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500356940249091436789943257 1125267705186818577592457443)
                ·
                  refine ⟨1687901557780227866388686165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125267705186818577592457443 1687901557780227866388686165)
                  ·
                    refine ⟨1236256023764815331827651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1687901557780227866388686165 1236256023764815331827651)
                    ·
                      rfl

theorem cell23_7222800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_7222800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222800 prefixEnd_7222800 := by exact prefixLift 7222800
  have htrace : WordTrace (prefixWord ++ tailWord_7222800) baseStart_7222800 baseEnd_7222800 := by
    simpa [prefixWord, tailWord_7222800, baseEnd_7222800] using wordTrace_append hprefix tailTrace_7222800
  have hstable : (prefixWord ++ tailWord_7222800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222800).length < 2 ^ (prefixWord ++ tailWord_7222800).sum := by decide
  have hdescent : baseEnd_7222800 < baseStart_7222800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222817 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_7222817 : Nat := 118140960795 + 7222817 * 2 ^ 59
def prefixEnd_7222817 : Nat := 4983230072969 + 3 ^ 40 * 7222817 * 2
def baseEnd_7222817 : Nat := 1236258933488524142990125

theorem tailTrace_7222817 : CollatzResearch.WordTrace tailWord_7222817 prefixEnd_7222817 1236258933488524142990125 := by
  unfold tailWord_7222817
  simp only [CollatzResearch.WordTrace]
  refine ⟨263437778273975042780066705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175625185515983361853377803 263437778273975042780066705)
  ·
    refine ⟨197578333705481282085050029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263437778273975042780066705 197578333705481282085050029)
    ·
      refine ⟨74091875139555480781893761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197578333705481282085050029 74091875139555480781893761)
      ·
        refine ⟨55568906354666610586420321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74091875139555480781893761 55568906354666610586420321)
        ·
          refine ⟨41676679765999957939815241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55568906354666610586420321 41676679765999957939815241)
          ·
            refine ⟨31257509824499968454861431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41676679765999957939815241 31257509824499968454861431)
            ·
              refine ⟨46886264736749952682292147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31257509824499968454861431 46886264736749952682292147)
              ·
                refine ⟨70329397105124929023438221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46886264736749952682292147 70329397105124929023438221)
                ·
                  refine ⟨26373523914421848383789333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70329397105124929023438221 26373523914421848383789333)
                  ·
                    refine ⟨1236258933488524142990125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26373523914421848383789333 1236258933488524142990125)
                    ·
                      rfl

theorem cell23_7222817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_7222817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222817 prefixEnd_7222817 := by exact prefixLift 7222817
  have htrace : WordTrace (prefixWord ++ tailWord_7222817) baseStart_7222817 baseEnd_7222817 := by
    simpa [prefixWord, tailWord_7222817, baseEnd_7222817] using wordTrace_append hprefix tailTrace_7222817
  have hstable : (prefixWord ++ tailWord_7222817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222817).length < 2 ^ (prefixWord ++ tailWord_7222817).sum := by decide
  have hdescent : baseEnd_7222817 < baseStart_7222817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222835 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 1, 1, 3]
def baseStart_7222835 : Nat := 118140960795 + 7222835 * 2 ^ 59
def prefixEnd_7222835 : Nat := 4983230072969 + 3 ^ 40 * 7222835 * 2
def baseEnd_7222835 : Nat := 3708786043117353358545293

theorem tailTrace_7222835 : CollatzResearch.WordTrace tailWord_7222835 prefixEnd_7222835 3708786043117353358545293 := by
  unfold tailWord_7222835
  simp only [CollatzResearch.WordTrace]
  refine ⟨263438434787909831854221959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175625623191939887902814639 263438434787909831854221959)
  ·
    refine ⟨395157652181864747781332939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263438434787909831854221959 395157652181864747781332939)
    ·
      refine ⟨592736478272797121671999409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395157652181864747781332939 592736478272797121671999409)
      ·
        refine ⟨444552358704597841253999557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592736478272797121671999409 444552358704597841253999557)
        ·
          refine ⟨83353567257112095235124917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444552358704597841253999557 83353567257112095235124917)
          ·
            refine ⟨7814396930354258928292961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83353567257112095235124917 7814396930354258928292961)
            ·
              refine ⟨5860797697765694196219721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7814396930354258928292961 5860797697765694196219721)
              ·
                refine ⟨4395598273324270647164791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860797697765694196219721 4395598273324270647164791)
                ·
                  refine ⟨6593397409986405970747187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395598273324270647164791 6593397409986405970747187)
                  ·
                    refine ⟨9890096114979608956120781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6593397409986405970747187 9890096114979608956120781)
                    ·
                      refine ⟨3708786043117353358545293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9890096114979608956120781 3708786043117353358545293)
                      ·
                        rfl

theorem cell23_7222835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 1, 3].length) (baseStart_7222835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222835 prefixEnd_7222835 := by exact prefixLift 7222835
  have htrace : WordTrace (prefixWord ++ tailWord_7222835) baseStart_7222835 baseEnd_7222835 := by
    simpa [prefixWord, tailWord_7222835, baseEnd_7222835] using wordTrace_append hprefix tailTrace_7222835
  have hstable : (prefixWord ++ tailWord_7222835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222835).length < 2 ^ (prefixWord ++ tailWord_7222835).sum := by decide
  have hdescent : baseEnd_7222835 < baseStart_7222835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222847 : List Nat := [1, 1, 2, 2, 3, 3, 3, 8]
def baseStart_7222847 : Nat := 118140960795 + 7222847 * 2 ^ 59
def prefixEnd_7222847 : Nat := 4983230072969 + 3 ^ 40 * 7222847 * 2
def baseEnd_7222847 : Nat := 137362674255007678207231

theorem tailTrace_7222847 : CollatzResearch.WordTrace tailWord_7222847 prefixEnd_7222847 137362674255007678207231 := by
  unfold tailWord_7222847
  simp only [CollatzResearch.WordTrace]
  refine ⟨263438872463866357903658795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175625914975910905269105863 263438872463866357903658795)
  ·
    refine ⟨395158308695799536855488193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263438872463866357903658795 395158308695799536855488193)
    ·
      refine ⟨296368731521849652641616145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395158308695799536855488193 296368731521849652641616145)
      ·
        refine ⟨222276548641387239481212109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296368731521849652641616145 222276548641387239481212109)
        ·
          refine ⟨83353705740520214805454541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222276548641387239481212109 83353705740520214805454541)
          ·
            refine ⟨31257639652695080552045453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83353705740520214805454541 31257639652695080552045453)
            ·
              refine ⟨11721614869760655207017045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31257639652695080552045453 11721614869760655207017045)
              ·
                refine ⟨137362674255007678207231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11721614869760655207017045 137362674255007678207231)
                ·
                  rfl

theorem cell23_7222847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 8].length) (baseStart_7222847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222847 prefixEnd_7222847 := by exact prefixLift 7222847
  have htrace : WordTrace (prefixWord ++ tailWord_7222847) baseStart_7222847 baseEnd_7222847 := by
    simpa [prefixWord, tailWord_7222847, baseEnd_7222847] using wordTrace_append hprefix tailTrace_7222847
  have hstable : (prefixWord ++ tailWord_7222847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222847).length < 2 ^ (prefixWord ++ tailWord_7222847).sum := by decide
  have hdescent : baseEnd_7222847 < baseStart_7222847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222897 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_7222897 : Nat := 118140960795 + 7222897 * 2 ^ 59
def prefixEnd_7222897 : Nat := 4983230072969 + 3 ^ 40 * 7222897 * 2
def baseEnd_7222897 : Nat := 3708817878917932115970007

theorem tailTrace_7222897 : CollatzResearch.WordTrace tailWord_7222897 prefixEnd_7222897 3708817878917932115970007 := by
  unfold tailWord_7222897
  simp only [CollatzResearch.WordTrace]
  refine ⟨263440696113685216442978945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175627130742456810961985963 263440696113685216442978945)
  ·
    refine ⟨197580522085263912332234209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263440696113685216442978945 197580522085263912332234209)
    ·
      refine ⟨148185391563947934249175657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197580522085263912332234209 148185391563947934249175657)
      ·
        refine ⟨111139043672960950686881743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148185391563947934249175657 111139043672960950686881743)
        ·
          refine ⟨166708565509441426030322615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111139043672960950686881743 166708565509441426030322615)
          ·
            refine ⟨250062848264162139045483923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166708565509441426030322615 250062848264162139045483923)
            ·
              refine ⟨375094272396243208568225885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250062848264162139045483923 375094272396243208568225885)
              ·
                refine ⟨140660352148591203213084707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375094272396243208568225885 140660352148591203213084707)
                ·
                  refine ⟨210990528222886804819627061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140660352148591203213084707 210990528222886804819627061)
                  ·
                    refine ⟨19780362020895637951840037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 210990528222886804819627061 19780362020895637951840037)
                    ·
                      refine ⟨3708817878917932115970007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19780362020895637951840037 3708817878917932115970007)
                      ·
                        rfl

theorem cell23_7222897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_7222897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222897 prefixEnd_7222897 := by exact prefixLift 7222897
  have htrace : WordTrace (prefixWord ++ tailWord_7222897) baseStart_7222897 baseEnd_7222897 := by
    simpa [prefixWord, tailWord_7222897, baseEnd_7222897] using wordTrace_append hprefix tailTrace_7222897
  have hstable : (prefixWord ++ tailWord_7222897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222897).length < 2 ^ (prefixWord ++ tailWord_7222897).sum := by decide
  have hdescent : baseEnd_7222897 < baseStart_7222897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222907 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 2, 6]
def baseStart_7222907 : Nat := 118140960795 + 7222907 * 2 ^ 59
def prefixEnd_7222907 : Nat := 4983230072969 + 3 ^ 40 * 7222907 * 2
def baseEnd_7222907 : Nat := 1236274337908159025614987

theorem tailTrace_7222907 : CollatzResearch.WordTrace tailWord_7222907 prefixEnd_7222907 1236274337908159025614987 := by
  unfold tailWord_7222907
  simp only [CollatzResearch.WordTrace]
  refine ⟨263441060843648988150842975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175627373895765992100561983 263441060843648988150842975)
  ·
    refine ⟨395161591265473482226264463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263441060843648988150842975 395161591265473482226264463)
    ·
      refine ⟨592742386898210223339396695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395161591265473482226264463 592742386898210223339396695)
      ·
        refine ⟨889113580347315335009095043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592742386898210223339396695 889113580347315335009095043)
        ·
          refine ⟨1333670370520973002513642565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889113580347315335009095043 1333670370520973002513642565)
          ·
            refine ⟨250063194472682437971307981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1333670370520973002513642565 250063194472682437971307981)
            ·
              refine ⟨93773697927255914239240493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250063194472682437971307981 93773697927255914239240493)
              ·
                refine ⟨35165136722720967839715185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93773697927255914239240493 35165136722720967839715185)
                ·
                  refine ⟨26373852542040725879786389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35165136722720967839715185 26373852542040725879786389)
                  ·
                    refine ⟨1236274337908159025614987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26373852542040725879786389 1236274337908159025614987)
                    ·
                      rfl

theorem cell23_7222907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_7222907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222907 prefixEnd_7222907 := by exact prefixLift 7222907
  have htrace : WordTrace (prefixWord ++ tailWord_7222907) baseStart_7222907 baseEnd_7222907 := by
    simpa [prefixWord, tailWord_7222907, baseEnd_7222907] using wordTrace_append hprefix tailTrace_7222907
  have hstable : (prefixWord ++ tailWord_7222907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222907).length < 2 ^ (prefixWord ++ tailWord_7222907).sum := by decide
  have hdescent : baseEnd_7222907 < baseStart_7222907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222947 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_7222947 : Nat := 118140960795 + 7222947 * 2 ^ 59
def prefixEnd_7222947 : Nat := 4983230072969 + 3 ^ 40 * 7222947 * 2
def baseEnd_7222947 : Nat := 3708843552950656920344777

theorem tailTrace_7222947 : CollatzResearch.WordTrace tailWord_7222947 prefixEnd_7222947 3708843552950656920344777 := by
  unfold tailWord_7222947
  simp only [CollatzResearch.WordTrace]
  refine ⟨263442519763504074982299095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175628346509002716654866063 263442519763504074982299095)
  ·
    refine ⟨395163779645256112473448643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263442519763504074982299095 395163779645256112473448643)
    ·
      refine ⟨592745669467884168710172965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395163779645256112473448643 592745669467884168710172965)
      ·
        refine ⟨111139813025228281633157431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 592745669467884168710172965 111139813025228281633157431)
        ·
          refine ⟨166709719537842422449736147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111139813025228281633157431 166709719537842422449736147)
          ·
            refine ⟨250064579306763633674604221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166709719537842422449736147 250064579306763633674604221)
            ·
              refine ⟨93774217240036362627976583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250064579306763633674604221 93774217240036362627976583)
              ·
                refine ⟨140661325860054543941964875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93774217240036362627976583 140661325860054543941964875)
                ·
                  refine ⟨210991988790081815912947313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140661325860054543941964875 210991988790081815912947313)
                  ·
                    refine ⟨158243991592561361934710485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210991988790081815912947313 158243991592561361934710485)
                    ·
                      refine ⟨3708843552950656920344777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158243991592561361934710485 3708843552950656920344777)
                      ·
                        rfl

theorem cell23_7222947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_7222947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222947 prefixEnd_7222947 := by exact prefixLift 7222947
  have htrace : WordTrace (prefixWord ++ tailWord_7222947) baseStart_7222947 baseEnd_7222947 := by
    simpa [prefixWord, tailWord_7222947, baseEnd_7222947] using wordTrace_append hprefix tailTrace_7222947
  have hstable : (prefixWord ++ tailWord_7222947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222947).length < 2 ^ (prefixWord ++ tailWord_7222947).sum := by decide
  have hdescent : baseEnd_7222947 < baseStart_7222947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222948 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_7222948 : Nat := 118140960795 + 7222948 * 2 ^ 59
def prefixEnd_7222948 : Nat := 4983230072969 + 3 ^ 40 * 7222948 * 2
def baseEnd_7222948 : Nat := 3708844066431311416432273

theorem tailTrace_7222948 : CollatzResearch.WordTrace tailWord_7222948 prefixEnd_7222948 3708844066431311416432273 := by
  unfold tailWord_7222948
  simp only [CollatzResearch.WordTrace]
  refine ⟨131721278118250226076542749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175628370824333634768723665 131721278118250226076542749)
  ·
    refine ⟨49395479294343834778703531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131721278118250226076542749 49395479294343834778703531)
    ·
      refine ⟨74093218941515752168055297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49395479294343834778703531 74093218941515752168055297)
      ·
        refine ⟨55569914206136814126041473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74093218941515752168055297 55569914206136814126041473)
        ·
          refine ⟨41677435654602610594531105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55569914206136814126041473 41677435654602610594531105)
          ·
            refine ⟨31258076740951957945898329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41677435654602610594531105 31258076740951957945898329)
            ·
              refine ⟨23443557555713968459423747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31258076740951957945898329 23443557555713968459423747)
              ·
                refine ⟨35165336333570952689135621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23443557555713968459423747 35165336333570952689135621)
                ·
                  refine ⟨6593500562544553629212929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35165336333570952689135621 6593500562544553629212929)
                  ·
                    refine ⟨4945125421908415221909697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593500562544553629212929 4945125421908415221909697)
                    ·
                      refine ⟨3708844066431311416432273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945125421908415221909697 3708844066431311416432273)
                      ·
                        rfl

theorem cell23_7222948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_7222948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222948 prefixEnd_7222948 := by exact prefixLift 7222948
  have htrace : WordTrace (prefixWord ++ tailWord_7222948) baseStart_7222948 baseEnd_7222948 := by
    simpa [prefixWord, tailWord_7222948, baseEnd_7222948] using wordTrace_append hprefix tailTrace_7222948
  have hstable : (prefixWord ++ tailWord_7222948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222948).length < 2 ^ (prefixWord ++ tailWord_7222948).sum := by decide
  have hdescent : baseEnd_7222948 < baseStart_7222948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7222982 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7222982 : Nat := 118140960795 + 7222982 * 2 ^ 59
def prefixEnd_7222982 : Nat := 4983230072969 + 3 ^ 40 * 7222982 * 2
def baseEnd_7222982 : Nat := 3708861524773564283407117

theorem tailTrace_7222982 : CollatzResearch.WordTrace tailWord_7222982 prefixEnd_7222982 3708861524773564283407117 := by
  unfold tailWord_7222982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232618634949289873744475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175629197545584850639882133 8232618634949289873744475)
  ·
    refine ⟨12348927952423934810616713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8232618634949289873744475 12348927952423934810616713)
    ·
      refine ⟨9261695964317951107962535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12348927952423934810616713 9261695964317951107962535)
      ·
        refine ⟨13892543946476926661943803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9261695964317951107962535 13892543946476926661943803)
        ·
          refine ⟨20838815919715389992915705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13892543946476926661943803 20838815919715389992915705)
          ·
            refine ⟨15629111939786542494686779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20838815919715389992915705 15629111939786542494686779)
            ·
              refine ⟨23443667909679813742030169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15629111939786542494686779 23443667909679813742030169)
              ·
                refine ⟨17582750932259860306522627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23443667909679813742030169 17582750932259860306522627)
                ·
                  refine ⟨26374126398389790459783941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17582750932259860306522627 26374126398389790459783941)
                  ·
                    refine ⟨4945148699698085711209489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26374126398389790459783941 4945148699698085711209489)
                    ·
                      refine ⟨3708861524773564283407117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945148699698085711209489 3708861524773564283407117)
                      ·
                        rfl

theorem cell23_7222982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7222982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7222982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7222982 prefixEnd_7222982 := by exact prefixLift 7222982
  have htrace : WordTrace (prefixWord ++ tailWord_7222982) baseStart_7222982 baseEnd_7222982 := by
    simpa [prefixWord, tailWord_7222982, baseEnd_7222982] using wordTrace_append hprefix tailTrace_7222982
  have hstable : (prefixWord ++ tailWord_7222982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7222982).length < 2 ^ (prefixWord ++ tailWord_7222982).sum := by decide
  have hdescent : baseEnd_7222982 < baseStart_7222982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7222982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223005 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 5]
def baseStart_7223005 : Nat := 118140960795 + 7223005 * 2 ^ 59
def prefixEnd_7223005 : Nat := 4983230072969 + 3 ^ 40 * 7223005 * 2
def baseEnd_7223005 : Nat := 412097037203179743713279

theorem tailTrace_7223005 : CollatzResearch.WordTrace tailWord_7223005 prefixEnd_7223005 412097037203179743713279 := by
  unfold tailWord_7223005
  simp only [CollatzResearch.WordTrace]
  refine ⟨263444635197293950887910469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175629756798195967258606979 263444635197293950887910469)
  ·
    refine ⟨49395869099492615791483213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263444635197293950887910469 49395869099492615791483213)
    ·
      refine ⟨18523450912309730921806205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49395869099492615791483213 18523450912309730921806205)
      ·
        refine ⟨6946294092116149095677327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18523450912309730921806205 6946294092116149095677327)
        ·
          refine ⟨10419441138174223643515991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6946294092116149095677327 10419441138174223643515991)
          ·
            refine ⟨15629161707261335465273987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10419441138174223643515991 15629161707261335465273987)
            ·
              refine ⟨23443742560892003197910981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15629161707261335465273987 23443742560892003197910981)
              ·
                refine ⟨4395701730167250599608309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23443742560892003197910981 4395701730167250599608309)
                ·
                  refine ⟨412097037203179743713279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4395701730167250599608309 412097037203179743713279)
                  ·
                    rfl

theorem cell23_7223005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_7223005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223005 prefixEnd_7223005 := by exact prefixLift 7223005
  have htrace : WordTrace (prefixWord ++ tailWord_7223005) baseStart_7223005 baseEnd_7223005 := by
    simpa [prefixWord, tailWord_7223005, baseEnd_7223005] using wordTrace_append hprefix tailTrace_7223005
  have hstable : (prefixWord ++ tailWord_7223005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223005).length < 2 ^ (prefixWord ++ tailWord_7223005).sum := by decide
  have hdescent : baseEnd_7223005 < baseStart_7223005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223038 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_7223038 : Nat := 118140960795 + 7223038 * 2 ^ 59
def prefixEnd_7223038 : Nat := 4983230072969 + 3 ^ 40 * 7223038 * 2
def baseEnd_7223038 : Nat := 3708890279690216064306859

theorem tailTrace_7223038 : CollatzResearch.WordTrace tailWord_7223038 prefixEnd_7223038 3708890279690216064306859 := by
  unfold tailWord_7223038
  simp only [CollatzResearch.WordTrace]
  refine ⟨32930729850771799690482721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175630559204116265015907845 32930729850771799690482721)
  ·
    refine ⟨24698047388078849767862041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32930729850771799690482721 24698047388078849767862041)
    ·
      refine ⟨18523535541059137325896531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24698047388078849767862041 18523535541059137325896531)
      ·
        refine ⟨27785303311588705988844797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523535541059137325896531 27785303311588705988844797)
        ·
          refine ⟨10419488741845764745816799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27785303311588705988844797 10419488741845764745816799)
          ·
            refine ⟨15629233112768647118725199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10419488741845764745816799 15629233112768647118725199)
            ·
              refine ⟨23443849669152970678087799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15629233112768647118725199 23443849669152970678087799)
              ·
                refine ⟨35165774503729456017131699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23443849669152970678087799 35165774503729456017131699)
                ·
                  refine ⟨52748661755594184025697549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35165774503729456017131699 52748661755594184025697549)
                  ·
                    refine ⟨19780748158347819009636581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52748661755594184025697549 19780748158347819009636581)
                    ·
                      refine ⟨3708890279690216064306859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19780748158347819009636581 3708890279690216064306859)
                      ·
                        rfl

theorem cell23_7223038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_7223038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223038 prefixEnd_7223038 := by exact prefixLift 7223038
  have htrace : WordTrace (prefixWord ++ tailWord_7223038) baseStart_7223038 baseEnd_7223038 := by
    simpa [prefixWord, tailWord_7223038, baseEnd_7223038] using wordTrace_append hprefix tailTrace_7223038
  have hstable : (prefixWord ++ tailWord_7223038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223038).length < 2 ^ (prefixWord ++ tailWord_7223038).sum := by decide
  have hdescent : baseEnd_7223038 < baseStart_7223038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223061 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 6]
def baseStart_7223061 : Nat := 118140960795 + 7223061 * 2 ^ 59
def prefixEnd_7223061 : Nat := 4983230072969 + 3 ^ 40 * 7223061 * 2
def baseEnd_7223061 : Nat := 412100232193918830479917

theorem tailTrace_7223061 : CollatzResearch.WordTrace tailWord_7223061 prefixEnd_7223061 412100232193918830479917 := by
  unfold tailWord_7223061
  simp only [CollatzResearch.WordTrace]
  refine ⟨263446677685091072451949037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175631118456727381634632691 263446677685091072451949037)
  ·
    refine ⟨98792504131909152169480889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263446677685091072451949037 98792504131909152169480889)
    ·
      refine ⟨74094378098931864127110667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98792504131909152169480889 74094378098931864127110667)
      ·
        refine ⟨111141567148397796190666001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74094378098931864127110667 111141567148397796190666001)
        ·
          refine ⟨83356175361298347142999501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111141567148397796190666001 83356175361298347142999501)
          ·
            refine ⟨31258565760486880178624813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83356175361298347142999501 31258565760486880178624813)
            ·
              refine ⟨11721962160182580066984305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31258565760486880178624813 11721962160182580066984305)
              ·
                refine ⟨8791471620136935050238229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11721962160182580066984305 8791471620136935050238229)
                ·
                  refine ⟨412100232193918830479917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8791471620136935050238229 412100232193918830479917)
                  ·
                    rfl

theorem cell23_7223061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_7223061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223061 prefixEnd_7223061 := by exact prefixLift 7223061
  have htrace : WordTrace (prefixWord ++ tailWord_7223061) baseStart_7223061 baseEnd_7223061 := by
    simpa [prefixWord, tailWord_7223061, baseEnd_7223061] using wordTrace_append hprefix tailTrace_7223061
  have hstable : (prefixWord ++ tailWord_7223061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223061).length < 2 ^ (prefixWord ++ tailWord_7223061).sum := by decide
  have hdescent : baseEnd_7223061 < baseStart_7223061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223064 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7223064 : Nat := 118140960795 + 7223064 * 2 ^ 59
def prefixEnd_7223064 : Nat := 4983230072969 + 3 ^ 40 * 7223064 * 2
def baseEnd_7223064 : Nat := 3708903630187232962581739

theorem tailTrace_7223064 : CollatzResearch.WordTrace tailWord_7223064 prefixEnd_7223064 3708903630187232962581739 := by
  unfold tailWord_7223064
  simp only [CollatzResearch.WordTrace]
  refine ⟨131723393552040101982154123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175631191402720135976205497 131723393552040101982154123)
  ·
    refine ⟨197585090328060152973231185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131723393552040101982154123 197585090328060152973231185)
    ·
      refine ⟨148188817746045114729923389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197585090328060152973231185 148188817746045114729923389)
      ·
        refine ⟨55570806654766918023721271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148188817746045114729923389 55570806654766918023721271)
        ·
          refine ⟨83356209982150377035581907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55570806654766918023721271 83356209982150377035581907)
          ·
            refine ⟨125034314973225565553372861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83356209982150377035581907 125034314973225565553372861)
            ·
              refine ⟨46887868114959587082514823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125034314973225565553372861 46887868114959587082514823)
              ·
                refine ⟨70331802172439380623772235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46887868114959587082514823 70331802172439380623772235)
                ·
                  refine ⟨105497703258659070935658353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70331802172439380623772235 105497703258659070935658353)
                  ·
                    refine ⟨79123277443994303201743765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105497703258659070935658353 79123277443994303201743765)
                    ·
                      refine ⟨3708903630187232962581739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79123277443994303201743765 3708903630187232962581739)
                      ·
                        rfl

theorem cell23_7223064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7223064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223064 prefixEnd_7223064 := by exact prefixLift 7223064
  have htrace : WordTrace (prefixWord ++ tailWord_7223064) baseStart_7223064 baseEnd_7223064 := by
    simpa [prefixWord, tailWord_7223064, baseEnd_7223064] using wordTrace_append hprefix tailTrace_7223064
  have hstable : (prefixWord ++ tailWord_7223064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223064).length < 2 ^ (prefixWord ++ tailWord_7223064).sum := by decide
  have hdescent : baseEnd_7223064 < baseStart_7223064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223098 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2]
def baseStart_7223098 : Nat := 118140960795 + 7223098 * 2 ^ 59
def prefixEnd_7223098 : Nat := 4983230072969 + 3 ^ 40 * 7223098 * 2
def baseEnd_7223098 : Nat := 3708921088529485829556583

theorem tailTrace_7223098 : CollatzResearch.WordTrace tailWord_7223098 prefixEnd_7223098 3708921088529485829556583 := by
  unfold tailWord_7223098
  simp only [CollatzResearch.WordTrace]
  refine ⟨65862006796489256942761487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175632018123971351847363965 65862006796489256942761487)
  ·
    refine ⟨98793010194733885414142231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65862006796489256942761487 98793010194733885414142231)
    ·
      refine ⟨148189515292100828121213347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98793010194733885414142231 148189515292100828121213347)
      ·
        refine ⟨222284272938151242181820021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148189515292100828121213347 222284272938151242181820021)
        ·
          refine ⟨20839150587951678954545627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222284272938151242181820021 20839150587951678954545627)
          ·
            refine ⟨31258725881927518431818441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20839150587951678954545627 31258725881927518431818441)
            ·
              refine ⟨23444044411445638823863831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31258725881927518431818441 23444044411445638823863831)
              ·
                refine ⟨35166066617168458235795747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23444044411445638823863831 35166066617168458235795747)
                ·
                  refine ⟨52749099925752687353693621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35166066617168458235795747 52749099925752687353693621)
                  ·
                    refine ⟨4945228118039314439408777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52749099925752687353693621 4945228118039314439408777)
                    ·
                      refine ⟨3708921088529485829556583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945228118039314439408777 3708921088529485829556583)
                      ·
                        rfl

theorem cell23_7223098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_7223098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223098 prefixEnd_7223098 := by exact prefixLift 7223098
  have htrace : WordTrace (prefixWord ++ tailWord_7223098) baseStart_7223098 baseEnd_7223098 := by
    simpa [prefixWord, tailWord_7223098, baseEnd_7223098] using wordTrace_append hprefix tailTrace_7223098
  have hstable : (prefixWord ++ tailWord_7223098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223098).length < 2 ^ (prefixWord ++ tailWord_7223098).sum := by decide
  have hdescent : baseEnd_7223098 < baseStart_7223098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223141 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7223141 : Nat := 118140960795 + 7223141 * 2 ^ 59
def prefixEnd_7223141 : Nat := 4983230072969 + 3 ^ 40 * 7223141 * 2
def baseEnd_7223141 : Nat := 3708943168197629161318885

theorem tailTrace_7223141 : CollatzResearch.WordTrace tailWord_7223141 prefixEnd_7223141 3708943168197629161318885 := by
  unfold tailWord_7223141
  simp only [CollatzResearch.WordTrace]
  refine ⟨263449595524801246114861277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175633063683200830743240851 263449595524801246114861277)
  ·
    refine ⟨98793598321800467293072979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263449595524801246114861277 98793598321800467293072979)
    ·
      refine ⟨148190397482700700939609469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98793598321800467293072979 148190397482700700939609469)
      ·
        refine ⟨55571399056012762852353551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148190397482700700939609469 55571399056012762852353551)
        ·
          refine ⟨83357098584019144278530327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55571399056012762852353551 83357098584019144278530327)
          ·
            refine ⟨125035647876028716417795491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83357098584019144278530327 125035647876028716417795491)
            ·
              refine ⟨187553471814043074626693237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125035647876028716417795491 187553471814043074626693237)
              ·
                refine ⟨17583137982566538246252491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187553471814043074626693237 17583137982566538246252491)
                ·
                  refine ⟨26374706973849807369378737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17583137982566538246252491 26374706973849807369378737)
                  ·
                    refine ⟨19781030230387355527034053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26374706973849807369378737 19781030230387355527034053)
                    ·
                      refine ⟨3708943168197629161318885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19781030230387355527034053 3708943168197629161318885)
                      ·
                        rfl

theorem cell23_7223141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7223141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223141 prefixEnd_7223141 := by exact prefixLift 7223141
  have htrace : WordTrace (prefixWord ++ tailWord_7223141) baseStart_7223141 baseEnd_7223141 := by
    simpa [prefixWord, tailWord_7223141, baseEnd_7223141] using wordTrace_append hprefix tailTrace_7223141
  have hstable : (prefixWord ++ tailWord_7223141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223141).length < 2 ^ (prefixWord ++ tailWord_7223141).sum := by decide
  have hdescent : baseEnd_7223141 < baseStart_7223141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223148 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_7223148 : Nat := 118140960795 + 7223148 * 2 ^ 59
def prefixEnd_7223148 : Nat := 4983230072969 + 3 ^ 40 * 7223148 * 2
def baseEnd_7223148 : Nat := 3708946762562210633931353

theorem tailTrace_7223148 : CollatzResearch.WordTrace tailWord_7223148 prefixEnd_7223148 3708946762562210633931353 := by
  unfold tailWord_7223148
  simp only [CollatzResearch.WordTrace]
  refine ⟨131724925417887943155183049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175633233890517257540244065 131724925417887943155183049)
  ·
    refine ⟨98793694063415957366387287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131724925417887943155183049 98793694063415957366387287)
    ·
      refine ⟨148190541095123936049580931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98793694063415957366387287 148190541095123936049580931)
      ·
        refine ⟨222285811642685904074371397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148190541095123936049580931 222285811642685904074371397)
        ·
          refine ⟨41678589683003607013944637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222285811642685904074371397 41678589683003607013944637)
          ·
            refine ⟨15629471131126352630229239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41678589683003607013944637 15629471131126352630229239)
            ·
              refine ⟨23444206696689528945343859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15629471131126352630229239 23444206696689528945343859)
              ·
                refine ⟨35166310045034293418015789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23444206696689528945343859 35166310045034293418015789)
                ·
                  refine ⟨13187366266887860031755921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35166310045034293418015789 13187366266887860031755921)
                  ·
                    refine ⟨9890524700165895023816941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13187366266887860031755921 9890524700165895023816941)
                    ·
                      refine ⟨3708946762562210633931353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9890524700165895023816941 3708946762562210633931353)
                      ·
                        rfl

theorem cell23_7223148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_7223148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223148 prefixEnd_7223148 := by exact prefixLift 7223148
  have htrace : WordTrace (prefixWord ++ tailWord_7223148) baseStart_7223148 baseEnd_7223148 := by
    simpa [prefixWord, tailWord_7223148, baseEnd_7223148] using wordTrace_append hprefix tailTrace_7223148
  have hstable : (prefixWord ++ tailWord_7223148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223148).length < 2 ^ (prefixWord ++ tailWord_7223148).sum := by decide
  have hdescent : baseEnd_7223148 < baseStart_7223148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223231 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_7223231 : Nat := 118140960795 + 7223231 * 2 ^ 59
def prefixEnd_7223231 : Nat := 4983230072969 + 3 ^ 40 * 7223231 * 2
def baseEnd_7223231 : Nat := 3708989381456533809193471

theorem tailTrace_7223231 : CollatzResearch.WordTrace tailWord_7223231 prefixEnd_7223231 3708989381456533809193471 := by
  unfold tailWord_7223231
  simp only [CollatzResearch.WordTrace]
  refine ⟨263452878094475191485637547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175635252062983460990425031 263452878094475191485637547)
  ·
    refine ⟨395179317141712787228456321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263452878094475191485637547 395179317141712787228456321)
    ·
      refine ⟨296384487856284590421342241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395179317141712787228456321 296384487856284590421342241)
      ·
        refine ⟨222288365892213442816006681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296384487856284590421342241 222288365892213442816006681)
        ·
          refine ⟨166716274419160082112005011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222288365892213442816006681 166716274419160082112005011)
          ·
            refine ⟨250074411628740123168007517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166716274419160082112005011 250074411628740123168007517)
            ·
              refine ⟨93777904360777546188002819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250074411628740123168007517 93777904360777546188002819)
              ·
                refine ⟨140666856541166319282004229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93777904360777546188002819 140666856541166319282004229)
                ·
                  refine ⟨26375035601468684865375793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140666856541166319282004229 26375035601468684865375793)
                  ·
                    refine ⟨19781276701101513649031845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26375035601468684865375793 19781276701101513649031845)
                    ·
                      refine ⟨3708989381456533809193471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19781276701101513649031845 3708989381456533809193471)
                      ·
                        rfl

theorem cell23_7223231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_7223231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223231 prefixEnd_7223231 := by exact prefixLift 7223231
  have htrace : WordTrace (prefixWord ++ tailWord_7223231) baseStart_7223231 baseEnd_7223231 := by
    simpa [prefixWord, tailWord_7223231, baseEnd_7223231] using wordTrace_append hprefix tailTrace_7223231
  have hstable : (prefixWord ++ tailWord_7223231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223231).length < 2 ^ (prefixWord ++ tailWord_7223231).sum := by decide
  have hdescent : baseEnd_7223231 < baseStart_7223231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223308 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7223308 : Nat := 118140960795 + 7223308 * 2 ^ 59
def prefixEnd_7223308 : Nat := 4983230072969 + 3 ^ 40 * 7223308 * 2
def baseEnd_7223308 : Nat := 3709028919466930007930617

theorem tailTrace_7223308 : CollatzResearch.WordTrace tailWord_7223308 prefixEnd_7223308 3709028919466930007930617 := by
  unfold tailWord_7223308
  simp only [CollatzResearch.WordTrace]
  refine ⟨131727843257598116818095289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175637124343464155757460385 131727843257598116818095289)
  ·
    refine ⟨98795882443198587613571467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131727843257598116818095289 98795882443198587613571467)
    ·
      refine ⟨148193823664797881420357201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98795882443198587613571467 148193823664797881420357201)
      ·
        refine ⟨111145367748598411065267901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148193823664797881420357201 111145367748598411065267901)
        ·
          refine ⟨41679512905724404149475463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111145367748598411065267901 41679512905724404149475463)
          ·
            refine ⟨62519269358586606224213195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41679512905724404149475463 62519269358586606224213195)
            ·
              refine ⟨93778904037879909336319793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62519269358586606224213195 93778904037879909336319793)
              ·
                refine ⟨70334178028409932002239845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93778904037879909336319793 70334178028409932002239845)
                ·
                  refine ⟨13187658380326862250419971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70334178028409932002239845 13187658380326862250419971)
                  ·
                    refine ⟨19781487570490293375629957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13187658380326862250419971 19781487570490293375629957)
                    ·
                      refine ⟨3709028919466930007930617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19781487570490293375629957 3709028919466930007930617)
                      ·
                        rfl

theorem cell23_7223308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7223308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223308 prefixEnd_7223308 := by exact prefixLift 7223308
  have htrace : WordTrace (prefixWord ++ tailWord_7223308) baseStart_7223308 baseEnd_7223308 := by
    simpa [prefixWord, tailWord_7223308, baseEnd_7223308] using wordTrace_append hprefix tailTrace_7223308
  have hstable : (prefixWord ++ tailWord_7223308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223308).length < 2 ^ (prefixWord ++ tailWord_7223308).sum := by decide
  have hdescent : baseEnd_7223308 < baseStart_7223308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223321 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_7223321 : Nat := 118140960795 + 7223321 * 2 ^ 59
def prefixEnd_7223321 : Nat := 4983230072969 + 3 ^ 40 * 7223321 * 2
def baseEnd_7223321 : Nat := 3709035594715438457068057

theorem tailTrace_7223321 : CollatzResearch.WordTrace tailWord_7223321 prefixEnd_7223321 3709035594715438457068057 := by
  unfold tailWord_7223321
  simp only [CollatzResearch.WordTrace]
  refine ⟨263456160664149136856413817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175637440442766091237609211 263456160664149136856413817)
  ·
    refine ⟨197592120498111852642310363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263456160664149136856413817 197592120498111852642310363)
    ·
      refine ⟨296388180747167778963465545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197592120498111852642310363 296388180747167778963465545)
      ·
        refine ⟨222291135560375834222599159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296388180747167778963465545 222291135560375834222599159)
        ·
          refine ⟨333436703340563751333898739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222291135560375834222599159 333436703340563751333898739)
          ·
            refine ⟨500155055010845627000848109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333436703340563751333898739 500155055010845627000848109)
            ·
              refine ⟨187558145629067110125318041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500155055010845627000848109 187558145629067110125318041)
              ·
                refine ⟨140668609221800332593988531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187558145629067110125318041 140668609221800332593988531)
                ·
                  refine ⟨211002913832700498890982797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140668609221800332593988531 211002913832700498890982797)
                  ·
                    refine ⟨79126092687262687084118549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211002913832700498890982797 79126092687262687084118549)
                    ·
                      refine ⟨3709035594715438457068057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79126092687262687084118549 3709035594715438457068057)
                      ·
                        rfl

theorem cell23_7223321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_7223321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223321 prefixEnd_7223321 := by exact prefixLift 7223321
  have htrace : WordTrace (prefixWord ++ tailWord_7223321) baseStart_7223321 baseEnd_7223321 := by
    simpa [prefixWord, tailWord_7223321, baseEnd_7223321] using wordTrace_append hprefix tailTrace_7223321
  have hstable : (prefixWord ++ tailWord_7223321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223321).length < 2 ^ (prefixWord ++ tailWord_7223321).sum := by decide
  have hdescent : baseEnd_7223321 < baseStart_7223321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223325 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7223325 : Nat := 118140960795 + 7223325 * 2 ^ 59
def prefixEnd_7223325 : Nat := 4983230072969 + 3 ^ 40 * 7223325 * 2
def baseEnd_7223325 : Nat := 3709037648638056441418039

theorem tailTrace_7223325 : CollatzResearch.WordTrace tailWord_7223325 prefixEnd_7223325 3709037648638056441418039 := by
  unfold tailWord_7223325
  simp only [CollatzResearch.WordTrace]
  refine ⟨263456306556134645539559429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175637537704089763693039619 263456306556134645539559429)
  ·
    refine ⟨49398057479275246038667393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263456306556134645539559429 49398057479275246038667393)
    ·
      refine ⟨37048543109456434529000545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49398057479275246038667393 37048543109456434529000545)
      ·
        refine ⟨27786407332092325896750409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37048543109456434529000545 27786407332092325896750409)
        ·
          refine ⟨20839805499069244422562807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27786407332092325896750409 20839805499069244422562807)
          ·
            refine ⟨31259708248603866633844211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20839805499069244422562807 31259708248603866633844211)
            ·
              refine ⟨46889562372905799950766317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31259708248603866633844211 46889562372905799950766317)
              ·
                refine ⟨17583585889839674981537369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46889562372905799950766317 17583585889839674981537369)
                ·
                  refine ⟨13187689417379756236153027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17583585889839674981537369 13187689417379756236153027)
                  ·
                    refine ⟨19781534126069634354229541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13187689417379756236153027 19781534126069634354229541)
                    ·
                      refine ⟨3709037648638056441418039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19781534126069634354229541 3709037648638056441418039)
                      ·
                        rfl

theorem cell23_7223325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7223325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223325 prefixEnd_7223325 := by exact prefixLift 7223325
  have htrace : WordTrace (prefixWord ++ tailWord_7223325) baseStart_7223325 baseEnd_7223325 := by
    simpa [prefixWord, tailWord_7223325, baseEnd_7223325] using wordTrace_append hprefix tailTrace_7223325
  have hstable : (prefixWord ++ tailWord_7223325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223325).length < 2 ^ (prefixWord ++ tailWord_7223325).sum := by decide
  have hdescent : baseEnd_7223325 < baseStart_7223325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223345 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_7223345 : Nat := 118140960795 + 7223345 * 2 ^ 59
def prefixEnd_7223345 : Nat := 4983230072969 + 3 ^ 40 * 7223345 * 2
def baseEnd_7223345 : Nat := 3709047918251146363167947

theorem tailTrace_7223345 : CollatzResearch.WordTrace tailWord_7223345 prefixEnd_7223345 3709047918251146363167947 := by
  unfold tailWord_7223345
  simp only [CollatzResearch.WordTrace]
  refine ⟨263457036016062188955287489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175638024010708125970191659 263457036016062188955287489)
  ·
    refine ⟨197592777012046641716465617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263457036016062188955287489 197592777012046641716465617)
    ·
      refine ⟨148194582759034981287349213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197592777012046641716465617 148194582759034981287349213)
      ·
        refine ⟨55572968534638117982755955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148194582759034981287349213 55572968534638117982755955)
        ·
          refine ⟨83359452801957176974133933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55572968534638117982755955 83359452801957176974133933)
          ·
            refine ⟨31259794800733941365300225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83359452801957176974133933 31259794800733941365300225)
            ·
              refine ⟨23444846100550456023975169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31259794800733941365300225 23444846100550456023975169)
              ·
                refine ⟨17583634575412842017981377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23444846100550456023975169 17583634575412842017981377)
                ·
                  refine ⟨13187725931559631513486033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17583634575412842017981377 13187725931559631513486033)
                  ·
                    refine ⟨9890794448669723635114525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13187725931559631513486033 9890794448669723635114525)
                    ·
                      refine ⟨3709047918251146363167947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9890794448669723635114525 3709047918251146363167947)
                      ·
                        rfl

theorem cell23_7223345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_7223345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223345 prefixEnd_7223345 := by exact prefixLift 7223345
  have htrace : WordTrace (prefixWord ++ tailWord_7223345) baseStart_7223345 baseEnd_7223345 := by
    simpa [prefixWord, tailWord_7223345, baseEnd_7223345] using wordTrace_append hprefix tailTrace_7223345
  have hstable : (prefixWord ++ tailWord_7223345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223345).length < 2 ^ (prefixWord ++ tailWord_7223345).sum := by decide
  have hdescent : baseEnd_7223345 < baseStart_7223345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223375 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 3]
def baseStart_7223375 : Nat := 118140960795 + 7223375 * 2 ^ 59
def prefixEnd_7223375 : Nat := 4983230072969 + 3 ^ 40 * 7223375 * 2
def baseEnd_7223375 : Nat := 3709063322670781245792809

theorem tailTrace_7223375 : CollatzResearch.WordTrace tailWord_7223375 prefixEnd_7223375 3709063322670781245792809 := by
  unfold tailWord_7223375
  simp only [CollatzResearch.WordTrace]
  refine ⟨263458130205953504078879579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175638753470635669385919719 263458130205953504078879579)
  ·
    refine ⟨395187195308930256118319369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263458130205953504078879579 395187195308930256118319369)
    ·
      refine ⟨296390396481697692088739527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395187195308930256118319369 296390396481697692088739527)
      ·
        refine ⟨444585594722546538133109291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296390396481697692088739527 444585594722546538133109291)
        ·
          refine ⟨666878392083819807199663937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444585594722546538133109291 666878392083819807199663937)
          ·
            refine ⟨500158794062864855399747953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666878392083819807199663937 500158794062864855399747953)
            ·
              refine ⟨375119095547148641549810965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500158794062864855399747953 375119095547148641549810965)
              ·
                refine ⟨17583707603772592572647389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 375119095547148641549810965 17583707603772592572647389)
                ·
                  refine ⟨6593890351414722214742771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17583707603772592572647389 6593890351414722214742771)
                  ·
                    refine ⟨9890835527122083322114157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6593890351414722214742771 9890835527122083322114157)
                    ·
                      refine ⟨3709063322670781245792809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9890835527122083322114157 3709063322670781245792809)
                      ·
                        rfl

theorem cell23_7223375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_7223375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223375 prefixEnd_7223375 := by exact prefixLift 7223375
  have htrace : WordTrace (prefixWord ++ tailWord_7223375) baseStart_7223375 baseEnd_7223375 := by
    simpa [prefixWord, tailWord_7223375, baseEnd_7223375] using wordTrace_append hprefix tailTrace_7223375
  have hstable : (prefixWord ++ tailWord_7223375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223375).length < 2 ^ (prefixWord ++ tailWord_7223375).sum := by decide
  have hdescent : baseEnd_7223375 < baseStart_7223375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223385 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 1, 5, 2]
def baseStart_7223385 : Nat := 118140960795 + 7223385 * 2 ^ 59
def prefixEnd_7223385 : Nat := 4983230072969 + 3 ^ 40 * 7223385 * 2
def baseEnd_7223385 : Nat := 3709068457477326206667763

theorem tailTrace_7223385 : CollatzResearch.WordTrace tailWord_7223385 prefixEnd_7223385 3709068457477326206667763 := by
  unfold tailWord_7223385
  simp only [CollatzResearch.WordTrace]
  refine ⟨263458494935917275786743609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175638996623944850524495739 263458494935917275786743609)
  ·
    refine ⟨197593871201937956840057707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263458494935917275786743609 197593871201937956840057707)
    ·
      refine ⟨296390806802906935260086561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197593871201937956840057707 296390806802906935260086561)
      ·
        refine ⟨222293105102180201445064921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296390806802906935260086561 222293105102180201445064921)
        ·
          refine ⟨166719828826635151083798691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222293105102180201445064921 166719828826635151083798691)
          ·
            refine ⟨250079743239952726625698037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166719828826635151083798691 250079743239952726625698037)
            ·
              refine ⟨23444975928745568121159191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250079743239952726625698037 23444975928745568121159191)
              ·
                refine ⟨35167463893118352181738787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23444975928745568121159191 35167463893118352181738787)
                ·
                  refine ⟨52751195839677528272608181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35167463893118352181738787 52751195839677528272608181)
                  ·
                    refine ⟨4945424609969768275557017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52751195839677528272608181 4945424609969768275557017)
                    ·
                      refine ⟨3709068457477326206667763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945424609969768275557017 3709068457477326206667763)
                      ·
                        rfl

theorem cell23_7223385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_7223385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223385 prefixEnd_7223385 := by exact prefixLift 7223385
  have htrace : WordTrace (prefixWord ++ tailWord_7223385) baseStart_7223385 baseEnd_7223385 := by
    simpa [prefixWord, tailWord_7223385, baseEnd_7223385] using wordTrace_append hprefix tailTrace_7223385
  have hstable : (prefixWord ++ tailWord_7223385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223385).length < 2 ^ (prefixWord ++ tailWord_7223385).sum := by decide
  have hdescent : baseEnd_7223385 < baseStart_7223385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223432 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7223432 : Nat := 118140960795 + 7223432 * 2 ^ 59
def prefixEnd_7223432 : Nat := 4983230072969 + 3 ^ 40 * 7223432 * 2
def baseEnd_7223432 : Nat := 3709092591068087522780047

theorem tailTrace_7223432 : CollatzResearch.WordTrace tailWord_7223432 prefixEnd_7223432 3709092591068087522780047 := by
  unfold tailWord_7223432
  simp only [CollatzResearch.WordTrace]
  refine ⟨131730104583373501406852275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175640139444498001875803033 131730104583373501406852275)
  ·
    refine ⟨197595156875060252110278413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131730104583373501406852275 197595156875060252110278413)
    ·
      refine ⟨74098183828147594541354405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197595156875060252110278413 74098183828147594541354405)
      ·
        refine ⟨13893409467777673976503951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74098183828147594541354405 13893409467777673976503951)
        ·
          refine ⟨20840114201666510964755927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13893409467777673976503951 20840114201666510964755927)
          ·
            refine ⟨31260171302499766447133891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20840114201666510964755927 31260171302499766447133891)
            ·
              refine ⟨46890256953749649670700837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31260171302499766447133891 46890256953749649670700837)
              ·
                refine ⟨8791923178828059313256407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46890256953749649670700837 8791923178828059313256407)
                ·
                  refine ⟨13187884768242088969884611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791923178828059313256407 13187884768242088969884611)
                  ·
                    refine ⟨19781827152363133454826917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13187884768242088969884611 19781827152363133454826917)
                    ·
                      refine ⟨3709092591068087522780047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19781827152363133454826917 3709092591068087522780047)
                      ·
                        rfl

theorem cell23_7223432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7223432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223432 prefixEnd_7223432 := by exact prefixLift 7223432
  have htrace : WordTrace (prefixWord ++ tailWord_7223432) baseStart_7223432 baseEnd_7223432 := by
    simpa [prefixWord, tailWord_7223432, baseEnd_7223432] using wordTrace_append hprefix tailTrace_7223432
  have hstable : (prefixWord ++ tailWord_7223432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223432).length < 2 ^ (prefixWord ++ tailWord_7223432).sum := by decide
  have hdescent : baseEnd_7223432 < baseStart_7223432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
