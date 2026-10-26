import V185TrunkScan22Chunk023

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_213438 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_213438 : Nat := 118140960795 + 213438 * 2 ^ 59
def prefixEnd_213438 : Nat := 4983230072969 + 3 ^ 40 * 213438 * 2
def baseEnd_213438 : Nat := 73064189289627437695615

theorem tailTrace_213438 : CollatzResearch.WordTrace tailWord_213438 prefixEnd_213438 73064189289627437695615 := by
  unfold tailWord_213438
  simp only [CollatzResearch.WordTrace]
  refine ⟨973090425094756644174121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5189815600505368768928645 973090425094756644174121)
  ·
    refine ⟨729817818821067483130591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 973090425094756644174121 729817818821067483130591)
    ·
      refine ⟨1094726728231601224695887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729817818821067483130591 1094726728231601224695887)
      ·
        refine ⟨1642090092347401837043831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094726728231601224695887 1642090092347401837043831)
        ·
          refine ⟨2463135138521102755565747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642090092347401837043831 2463135138521102755565747)
          ·
            refine ⟨3694702707781654133348621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463135138521102755565747 3694702707781654133348621)
            ·
              refine ⟨1385513515418120300005733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3694702707781654133348621 1385513515418120300005733)
              ·
                refine ⟨259783784140897556251075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1385513515418120300005733 259783784140897556251075)
                ·
                  refine ⟨389675676211346334376613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259783784140897556251075 389675676211346334376613)
                  ·
                    refine ⟨73064189289627437695615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389675676211346334376613 73064189289627437695615)
                    ·
                      rfl

theorem cell22_213438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_213438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213438 prefixEnd_213438 := by exact prefixLift 213438
  have htrace : WordTrace (prefixWord ++ tailWord_213438) baseStart_213438 baseEnd_213438 := by
    simpa [prefixWord, tailWord_213438, baseEnd_213438] using wordTrace_append hprefix tailTrace_213438
  have hstable : (prefixWord ++ tailWord_213438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213438).length < 2 ^ (prefixWord ++ tailWord_213438).sum := by decide
  have hdescent : baseEnd_213438 < baseStart_213438 := by decide
  rcases family_descends (prefixWord ++ tailWord_213438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213517 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_213517 : Nat := 118140960795 + 213517 * 2 ^ 59
def prefixEnd_213517 : Nat := 4983230072969 + 3 ^ 40 * 213517 * 2
def baseEnd_213517 : Nat := 73091232604097564970373

theorem tailTrace_213517 : CollatzResearch.WordTrace tailWord_213517 prefixEnd_213517 73091232604097564970373 := by
  unfold tailWord_213517
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787604767471849645518805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5191736511647899763679203 7787604767471849645518805)
  ·
    refine ⟨182521986737621476066847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7787604767471849645518805 182521986737621476066847)
    ·
      refine ⟨273782980106432214100271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182521986737621476066847 273782980106432214100271)
      ·
        refine ⟨410674470159648321150407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273782980106432214100271 410674470159648321150407)
        ·
          refine ⟨616011705239472481725611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410674470159648321150407 616011705239472481725611)
          ·
            refine ⟨924017557859208722588417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616011705239472481725611 924017557859208722588417)
            ·
              refine ⟨693013168394406541941313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924017557859208722588417 693013168394406541941313)
              ·
                refine ⟨519759876295804906455985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693013168394406541941313 519759876295804906455985)
                ·
                  refine ⟨389819907221853679841989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519759876295804906455985 389819907221853679841989)
                  ·
                    refine ⟨73091232604097564970373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389819907221853679841989 73091232604097564970373)
                    ·
                      rfl

theorem cell22_213517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_213517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213517 prefixEnd_213517 := by exact prefixLift 213517
  have htrace : WordTrace (prefixWord ++ tailWord_213517) baseStart_213517 baseEnd_213517 := by
    simpa [prefixWord, tailWord_213517, baseEnd_213517] using wordTrace_append hprefix tailTrace_213517
  have hstable : (prefixWord ++ tailWord_213517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213517).length < 2 ^ (prefixWord ++ tailWord_213517).sum := by decide
  have hdescent : baseEnd_213517 < baseStart_213517 := by decide
  rcases family_descends (prefixWord ++ tailWord_213517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213541 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_213541 : Nat := 118140960795 + 213541 * 2 ^ 59
def prefixEnd_213541 : Nat := 4983230072969 + 3 ^ 40 * 213541 * 2
def baseEnd_213541 : Nat := 73099448294569502370299

theorem tailTrace_213541 : CollatzResearch.WordTrace tailWord_213541 prefixEnd_213541 73099448294569502370299 := by
  unfold tailWord_213541
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788480119384901744392477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5192320079589934496261651 7788480119384901744392477)
  ·
    refine ⟨2920680044769338154147179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7788480119384901744392477 2920680044769338154147179)
    ·
      refine ⟨4381020067154007231220769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920680044769338154147179 4381020067154007231220769)
      ·
        refine ⟨3285765050365505423415577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4381020067154007231220769 3285765050365505423415577)
        ·
          refine ⟨2464323787774129067561683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3285765050365505423415577 2464323787774129067561683)
          ·
            refine ⟨3696485681661193601342525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464323787774129067561683 3696485681661193601342525)
            ·
              refine ⟨1386182130622947600503447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3696485681661193601342525 1386182130622947600503447)
              ·
                refine ⟨2079273195934421400755171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386182130622947600503447 2079273195934421400755171)
                ·
                  refine ⟨3118909793901632101132757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079273195934421400755171 3118909793901632101132757)
                  ·
                    refine ⟨73099448294569502370299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3118909793901632101132757 73099448294569502370299)
                    ·
                      rfl

theorem cell22_213541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_213541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213541 prefixEnd_213541 := by exact prefixLift 213541
  have htrace : WordTrace (prefixWord ++ tailWord_213541) baseStart_213541 baseEnd_213541 := by
    simpa [prefixWord, tailWord_213541, baseEnd_213541] using wordTrace_append hprefix tailTrace_213541
  have hstable : (prefixWord ++ tailWord_213541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213541).length < 2 ^ (prefixWord ++ tailWord_213541).sum := by decide
  have hdescent : baseEnd_213541 < baseStart_213541 := by decide
  rcases family_descends (prefixWord ++ tailWord_213541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213549 : List Nat := [1, 5, 4, 1, 1, 1, 3, 6]
def baseStart_213549 : Nat := 118140960795 + 213549 * 2 ^ 59
def prefixEnd_213549 : Nat := 4983230072969 + 3 ^ 40 * 213549 * 2
def baseEnd_213549 : Nat := 8122465206451127574475

theorem tailTrace_213549 : CollatzResearch.WordTrace tailWord_213549 prefixEnd_213549 8122465206451127574475 := by
  unfold tailWord_213549
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788771903355919110683701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5192514602237279407122467 7788771903355919110683701)
  ·
    refine ⟨730197365939617416626597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7788771903355919110683701 730197365939617416626597)
    ·
      refine ⟨136912006113678265617487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 730197365939617416626597 136912006113678265617487)
      ·
        refine ⟨205368009170517398426231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136912006113678265617487 205368009170517398426231)
        ·
          refine ⟨308052013755776097639347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205368009170517398426231 308052013755776097639347)
          ·
            refine ⟨462078020633664146459021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308052013755776097639347 462078020633664146459021)
            ·
              refine ⟨173279257737624054922133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462078020633664146459021 173279257737624054922133)
              ·
                refine ⟨8122465206451127574475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173279257737624054922133 8122465206451127574475)
                ·
                  rfl

theorem cell22_213549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 6].length) (baseStart_213549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213549 prefixEnd_213549 := by exact prefixLift 213549
  have htrace : WordTrace (prefixWord ++ tailWord_213549) baseStart_213549 baseEnd_213549 := by
    simpa [prefixWord, tailWord_213549, baseEnd_213549] using wordTrace_append hprefix tailTrace_213549
  have hstable : (prefixWord ++ tailWord_213549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213549).length < 2 ^ (prefixWord ++ tailWord_213549).sum := by decide
  have hdescent : baseEnd_213549 < baseStart_213549 := by decide
  rcases family_descends (prefixWord ++ tailWord_213549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213588 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_213588 : Nat := 118140960795 + 213588 * 2 ^ 59
def prefixEnd_213588 : Nat := 4983230072969 + 3 ^ 40 * 213588 * 2
def baseEnd_213588 : Nat := 24371845785025682148385

theorem tailTrace_213588 : CollatzResearch.WordTrace tailWord_213588 prefixEnd_213588 24371845785025682148385 := by
  unfold tailWord_213588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895097175107314385676709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5193462900143085847568945 3895097175107314385676709)
  ·
    refine ⟨730330720332621447314383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3895097175107314385676709 730330720332621447314383)
    ·
      refine ⟨1095496080498932170971575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730330720332621447314383 1095496080498932170971575)
      ·
        refine ⟨1643244120748398256457363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095496080498932170971575 1643244120748398256457363)
        ·
          refine ⟨2464866181122597384686045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643244120748398256457363 2464866181122597384686045)
          ·
            refine ⟨924324817920974019257267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2464866181122597384686045 924324817920974019257267)
            ·
              refine ⟨1386487226881461028885901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924324817920974019257267 1386487226881461028885901)
              ·
                refine ⟨519932710080547885832213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1386487226881461028885901 519932710080547885832213)
                ·
                  refine ⟨24371845785025682148385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 519932710080547885832213 24371845785025682148385)
                  ·
                    rfl

theorem cell22_213588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_213588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213588 prefixEnd_213588 := by exact prefixLift 213588
  have htrace : WordTrace (prefixWord ++ tailWord_213588) baseStart_213588 baseEnd_213588 := by
    simpa [prefixWord, tailWord_213588, baseEnd_213588] using wordTrace_append hprefix tailTrace_213588
  have hstable : (prefixWord ++ tailWord_213588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213588).length < 2 ^ (prefixWord ++ tailWord_213588).sum := by decide
  have hdescent : baseEnd_213588 < baseStart_213588 := by decide
  rcases family_descends (prefixWord ++ tailWord_213588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213650 : List Nat := [3, 2, 3, 1, 2, 2, 2, 7]
def baseStart_213650 : Nat := 118140960795 + 213650 * 2 ^ 59
def prefixEnd_213650 : Nat := 4983230072969 + 3 ^ 40 * 213650 * 2
def baseEnd_213650 : Nat := 8126306802458839043885

theorem tailTrace_213650 : CollatzResearch.WordTrace tailWord_213650 prefixEnd_213650 8126306802458839043885 := by
  unfold tailWord_213650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948113918997503340027601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5194970450660008906740269 1948113918997503340027601)
  ·
    refine ⟨1461085439248127505020701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1948113918997503340027601 1461085439248127505020701)
    ·
      refine ⟨547907039718047814382763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1461085439248127505020701 547907039718047814382763)
      ·
        refine ⟨821860559577071721574145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547907039718047814382763 821860559577071721574145)
        ·
          refine ⟨616395419682803791180609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821860559577071721574145 616395419682803791180609)
          ·
            refine ⟨462296564762102843385457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616395419682803791180609 462296564762102843385457)
            ·
              refine ⟨346722423571577132539093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462296564762102843385457 346722423571577132539093)
              ·
                refine ⟨8126306802458839043885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 346722423571577132539093 8126306802458839043885)
                ·
                  rfl

theorem cell22_213650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_213650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213650 prefixEnd_213650 := by exact prefixLift 213650
  have htrace : WordTrace (prefixWord ++ tailWord_213650) baseStart_213650 baseEnd_213650 := by
    simpa [prefixWord, tailWord_213650, baseEnd_213650] using wordTrace_append hprefix tailTrace_213650
  have hstable : (prefixWord ++ tailWord_213650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213650).length < 2 ^ (prefixWord ++ tailWord_213650).sum := by decide
  have hdescent : baseEnd_213650 < baseStart_213650 := by decide
  rcases family_descends (prefixWord ++ tailWord_213650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213682 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_213682 : Nat := 118140960795 + 213682 * 2 ^ 59
def prefixEnd_213682 : Nat := 4983230072969 + 3 ^ 40 * 213682 * 2
def baseEnd_213682 : Nat := 73147715476092134594867

theorem tailTrace_213682 : CollatzResearch.WordTrace tailWord_213682 prefixEnd_213682 73147715476092134594867 := by
  unfold tailWord_213682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948405702968520706318825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5195748541249388550183533 1948405702968520706318825)
  ·
    refine ⟨1461304277226390529739119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1948405702968520706318825 1461304277226390529739119)
    ·
      refine ⟨2191956415839585794608679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461304277226390529739119 2191956415839585794608679)
      ·
        refine ⟨3287934623759378691913019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191956415839585794608679 3287934623759378691913019)
        ·
          refine ⟨4931901935639068037869529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287934623759378691913019 4931901935639068037869529)
          ·
            refine ⟨3698926451729301028402147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4931901935639068037869529 3698926451729301028402147)
            ·
              refine ⟨5548389677593951542603221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698926451729301028402147 5548389677593951542603221)
              ·
                refine ⟨130040383068608239279763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5548389677593951542603221 130040383068608239279763)
                ·
                  refine ⟨195060574602912358919645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130040383068608239279763 195060574602912358919645)
                  ·
                    refine ⟨73147715476092134594867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195060574602912358919645 73147715476092134594867)
                    ·
                      rfl

theorem cell22_213682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_213682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213682 prefixEnd_213682 := by exact prefixLift 213682
  have htrace : WordTrace (prefixWord ++ tailWord_213682) baseStart_213682 baseEnd_213682 := by
    simpa [prefixWord, tailWord_213682, baseEnd_213682] using wordTrace_append hprefix tailTrace_213682
  have hstable : (prefixWord ++ tailWord_213682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213682).length < 2 ^ (prefixWord ++ tailWord_213682).sum := by decide
  have hdescent : baseEnd_213682 < baseStart_213682 := by decide
  rcases family_descends (prefixWord ++ tailWord_213682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213695 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 5]
def baseStart_213695 : Nat := 118140960795 + 213695 * 2 ^ 59
def prefixEnd_213695 : Nat := 4983230072969 + 3 ^ 40 * 213695 * 2
def baseEnd_213695 : Nat := 24384055213921478006609

theorem tailTrace_213695 : CollatzResearch.WordTrace tailWord_213695 prefixEnd_213695 24384055213921478006609 := by
  unfold tailWord_213695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794096960826986045498539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5196064640551324030332359 7794096960826986045498539)
  ·
    refine ⟨11691145441240479068247809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7794096960826986045498539 11691145441240479068247809)
    ·
      refine ⟨8768359080930359301185857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11691145441240479068247809 8768359080930359301185857)
      ·
        refine ⟨6576269310697769475889393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8768359080930359301185857 6576269310697769475889393)
        ·
          refine ⟨4932201983023327106917045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576269310697769475889393 4932201983023327106917045)
          ·
            refine ⟨462393935908436916273473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4932201983023327106917045 462393935908436916273473)
            ·
              refine ⟨346795451931327687205105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462393935908436916273473 346795451931327687205105)
              ·
                refine ⟨260096588948495765403829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346795451931327687205105 260096588948495765403829)
                ·
                  refine ⟨24384055213921478006609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260096588948495765403829 24384055213921478006609)
                  ·
                    rfl

theorem cell22_213695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 5].length) (baseStart_213695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213695 prefixEnd_213695 := by exact prefixLift 213695
  have htrace : WordTrace (prefixWord ++ tailWord_213695) baseStart_213695 baseEnd_213695 := by
    simpa [prefixWord, tailWord_213695, baseEnd_213695] using wordTrace_append hprefix tailTrace_213695
  have hstable : (prefixWord ++ tailWord_213695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213695).length < 2 ^ (prefixWord ++ tailWord_213695).sum := by decide
  have hdescent : baseEnd_213695 < baseStart_213695 := by decide
  rcases family_descends (prefixWord ++ tailWord_213695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213710 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_213710 : Nat := 118140960795 + 213710 * 2 ^ 59
def prefixEnd_213710 : Nat := 4983230072969 + 3 ^ 40 * 213710 * 2
def baseEnd_213710 : Nat := 73157300448309394894781

theorem tailTrace_213710 : CollatzResearch.WordTrace tailWord_213710 prefixEnd_213710 73157300448309394894781 := by
  unfold tailWord_213710
  simp only [CollatzResearch.WordTrace]
  refine ⟨974330506971580450911823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5196429370515095738196389 974330506971580450911823)
  ·
    refine ⟨1461495760457370676367735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974330506971580450911823 1461495760457370676367735)
    ·
      refine ⟨2192243640686056014551603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461495760457370676367735 2192243640686056014551603)
      ·
        refine ⟨3288365461029084021827405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192243640686056014551603 3288365461029084021827405)
        ·
          refine ⟨1233137047885906508185277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3288365461029084021827405 1233137047885906508185277)
          ·
            refine ⟨462426392957214940569479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1233137047885906508185277 462426392957214940569479)
            ·
              refine ⟨693639589435822410854219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462426392957214940569479 693639589435822410854219)
              ·
                refine ⟨1040459384153733616281329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693639589435822410854219 1040459384153733616281329)
                ·
                  refine ⟨780344538115300212210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040459384153733616281329 780344538115300212210997)
                  ·
                    refine ⟨73157300448309394894781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 780344538115300212210997 73157300448309394894781)
                    ·
                      rfl

theorem cell22_213710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_213710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213710 prefixEnd_213710 := by exact prefixLift 213710
  have htrace : WordTrace (prefixWord ++ tailWord_213710) baseStart_213710 baseEnd_213710 := by
    simpa [prefixWord, tailWord_213710, baseEnd_213710] using wordTrace_append hprefix tailTrace_213710
  have hstable : (prefixWord ++ tailWord_213710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213710).length < 2 ^ (prefixWord ++ tailWord_213710).sum := by decide
  have hdescent : baseEnd_213710 < baseStart_213710 := by decide
  rcases family_descends (prefixWord ++ tailWord_213710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213742 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_213742 : Nat := 118140960795 + 213742 * 2 ^ 59
def prefixEnd_213742 : Nat := 4983230072969 + 3 ^ 40 * 213742 * 2
def baseEnd_213742 : Nat := 73168254702271978094683

theorem tailTrace_213742 : CollatzResearch.WordTrace tailWord_213742 prefixEnd_213742 73168254702271978094683 := by
  unfold tailWord_213742
  simp only [CollatzResearch.WordTrace]
  refine ⟨974476398957089134057435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5197207461104475381639653 974476398957089134057435)
  ·
    refine ⟨1461714598435633701086153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974476398957089134057435 1461714598435633701086153)
    ·
      refine ⟨1096285948826725275814615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1461714598435633701086153 1096285948826725275814615)
      ·
        refine ⟨1644428923240087913721923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096285948826725275814615 1644428923240087913721923)
        ·
          refine ⟨2466643384860131870582885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644428923240087913721923 2466643384860131870582885)
          ·
            refine ⟨462495634661274725734291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2466643384860131870582885 462495634661274725734291)
            ·
              refine ⟨693743451991912088601437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462495634661274725734291 693743451991912088601437)
              ·
                refine ⟨260153794496967033225539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693743451991912088601437 260153794496967033225539)
                ·
                  refine ⟨390230691745450549838309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260153794496967033225539 390230691745450549838309)
                  ·
                    refine ⟨73168254702271978094683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390230691745450549838309 73168254702271978094683)
                    ·
                      rfl

theorem cell22_213742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_213742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213742 prefixEnd_213742 := by exact prefixLift 213742
  have htrace : WordTrace (prefixWord ++ tailWord_213742) baseStart_213742 baseEnd_213742 := by
    simpa [prefixWord, tailWord_213742, baseEnd_213742] using wordTrace_append hprefix tailTrace_213742
  have hstable : (prefixWord ++ tailWord_213742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213742).length < 2 ^ (prefixWord ++ tailWord_213742).sum := by decide
  have hdescent : baseEnd_213742 < baseStart_213742 := by decide
  rcases family_descends (prefixWord ++ tailWord_213742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213877 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_213877 : Nat := 118140960795 + 213877 * 2 ^ 59
def prefixEnd_213877 : Nat := 4983230072969 + 3 ^ 40 * 213877 * 2
def baseEnd_213877 : Nat := 73214467961176625969269

theorem tailTrace_213877 : CollatzResearch.WordTrace tailWord_213877 prefixEnd_213877 73214467961176625969269 := by
  unfold tailWord_213877
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800735046167631128623885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5200490030778420752415923 7800735046167631128623885)
  ·
    refine ⟨2925275642312861673233957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7800735046167631128623885 2925275642312861673233957)
    ·
      refine ⟨548489182933661563731367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2925275642312861673233957 548489182933661563731367)
      ·
        refine ⟨822733774400492345597051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548489182933661563731367 822733774400492345597051)
        ·
          refine ⟨1234100661600738518395577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822733774400492345597051 1234100661600738518395577)
          ·
            refine ⟨925575496200553888796683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234100661600738518395577 925575496200553888796683)
            ·
              refine ⟨1388363244300830833195025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925575496200553888796683 1388363244300830833195025)
              ·
                refine ⟨1041272433225623124896269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388363244300830833195025 1041272433225623124896269)
                ·
                  refine ⟨390477162459608671836101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041272433225623124896269 390477162459608671836101)
                  ·
                    refine ⟨73214467961176625969269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390477162459608671836101 73214467961176625969269)
                    ·
                      rfl

theorem cell22_213877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_213877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213877 prefixEnd_213877 := by exact prefixLift 213877
  have htrace : WordTrace (prefixWord ++ tailWord_213877) baseStart_213877 baseEnd_213877 := by
    simpa [prefixWord, tailWord_213877, baseEnd_213877] using wordTrace_append hprefix tailTrace_213877
  have hstable : (prefixWord ++ tailWord_213877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213877).length < 2 ^ (prefixWord ++ tailWord_213877).sum := by decide
  have hdescent : baseEnd_213877 < baseStart_213877 := by decide
  rcases family_descends (prefixWord ++ tailWord_213877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213909 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 4]
def baseStart_213909 : Nat := 118140960795 + 213909 * 2 ^ 59
def prefixEnd_213909 : Nat := 4983230072969 + 3 ^ 40 * 213909 * 2
def baseEnd_213909 : Nat := 24408474071713069723057

theorem tailTrace_213909 : CollatzResearch.WordTrace tailWord_213909 prefixEnd_213909 24408474071713069723057 := by
  unfold tailWord_213909
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801902182051700593788781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5201268121367800395859187 7801902182051700593788781)
  ·
    refine ⟨2925713318269387722670793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7801902182051700593788781 2925713318269387722670793)
    ·
      refine ⟨2194284988702040792003095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2925713318269387722670793 2194284988702040792003095)
      ·
        refine ⟨3291427483053061188004643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194284988702040792003095 3291427483053061188004643)
        ·
          refine ⟨4937141224579591782006965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291427483053061188004643 4937141224579591782006965)
          ·
            refine ⟨462856989804336729563153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4937141224579591782006965 462856989804336729563153)
            ·
              refine ⟨347142742353252547172365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462856989804336729563153 347142742353252547172365)
              ·
                refine ⟨130178528382469705189637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347142742353252547172365 130178528382469705189637)
                ·
                  refine ⟨24408474071713069723057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130178528382469705189637 24408474071713069723057)
                  ·
                    rfl

theorem cell22_213909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_213909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213909 prefixEnd_213909 := by exact prefixLift 213909
  have htrace : WordTrace (prefixWord ++ tailWord_213909) baseStart_213909 baseEnd_213909 := by
    simpa [prefixWord, tailWord_213909, baseEnd_213909] using wordTrace_append hprefix tailTrace_213909
  have hstable : (prefixWord ++ tailWord_213909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213909).length < 2 ^ (prefixWord ++ tailWord_213909).sum := by decide
  have hdescent : baseEnd_213909 < baseStart_213909 := by decide
  rcases family_descends (prefixWord ++ tailWord_213909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213941 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_213941 : Nat := 118140960795 + 213941 * 2 ^ 59
def prefixEnd_213941 : Nat := 4983230072969 + 3 ^ 40 * 213941 * 2
def baseEnd_213941 : Nat := 73236376469101792369073

theorem tailTrace_213941 : CollatzResearch.WordTrace tailWord_213941 prefixEnd_213941 73236376469101792369073 := by
  unfold tailWord_213941
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803069317935770058953677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5202046211957180039302451 7803069317935770058953677)
  ·
    refine ⟨2926150994225913772107629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7803069317935770058953677 2926150994225913772107629)
    ·
      refine ⟨1097306622834717664540361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2926150994225913772107629 1097306622834717664540361)
      ·
        refine ⟨822979967126038248405271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097306622834717664540361 822979967126038248405271)
        ·
          refine ⟨1234469950689057372607907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822979967126038248405271 1234469950689057372607907)
          ·
            refine ⟨1851704926033586058911861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234469950689057372607907 1851704926033586058911861)
            ·
              refine ⟨173597336815648693022987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1851704926033586058911861 173597336815648693022987)
              ·
                refine ⟨260396005223473039534481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173597336815648693022987 260396005223473039534481)
                ·
                  refine ⟨195297003917604779650861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260396005223473039534481 195297003917604779650861)
                  ·
                    refine ⟨73236376469101792369073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195297003917604779650861 73236376469101792369073)
                    ·
                      rfl

theorem cell22_213941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_213941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213941 prefixEnd_213941 := by exact prefixLift 213941
  have htrace : WordTrace (prefixWord ++ tailWord_213941) baseStart_213941 baseEnd_213941 := by
    simpa [prefixWord, tailWord_213941, baseEnd_213941] using wordTrace_append hprefix tailTrace_213941
  have hstable : (prefixWord ++ tailWord_213941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213941).length < 2 ^ (prefixWord ++ tailWord_213941).sum := by decide
  have hdescent : baseEnd_213941 < baseStart_213941 := by decide
  rcases family_descends (prefixWord ++ tailWord_213941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213995 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_213995 : Nat := 118140960795 + 213995 * 2 ^ 59
def prefixEnd_213995 : Nat := 4983230072969 + 3 ^ 40 * 213995 * 2
def baseEnd_213995 : Nat := 73254861772663651518907

theorem tailTrace_213995 : CollatzResearch.WordTrace tailWord_213995 prefixEnd_213995 73254861772663651518907 := by
  unfold tailWord_213995
  simp only [CollatzResearch.WordTrace]
  refine ⟨7805038859740137281419439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5203359239826758187612959 7805038859740137281419439)
  ·
    refine ⟨11707558289610205922129159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7805038859740137281419439 11707558289610205922129159)
    ·
      refine ⟨17561337434415308883193739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11707558289610205922129159 17561337434415308883193739)
      ·
        refine ⟨26342006151622963324790609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17561337434415308883193739 26342006151622963324790609)
        ·
          refine ⟨19756504613717222493592957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26342006151622963324790609 19756504613717222493592957)
          ·
            refine ⟨7408689230143958435097359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19756504613717222493592957 7408689230143958435097359)
            ·
              refine ⟨11113033845215937652646039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408689230143958435097359 11113033845215937652646039)
              ·
                refine ⟨16669550767823906478969059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11113033845215937652646039 16669550767823906478969059)
                ·
                  refine ⟨25004326151735859718453589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16669550767823906478969059 25004326151735859718453589)
                  ·
                    refine ⟨73254861772663651518907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 25004326151735859718453589 73254861772663651518907)
                    ·
                      rfl

theorem cell22_213995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_213995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213995 prefixEnd_213995 := by exact prefixLift 213995
  have htrace : WordTrace (prefixWord ++ tailWord_213995) baseStart_213995 baseEnd_213995 := by
    simpa [prefixWord, tailWord_213995, baseEnd_213995] using wordTrace_append hprefix tailTrace_213995
  have hstable : (prefixWord ++ tailWord_213995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213995).length < 2 ^ (prefixWord ++ tailWord_213995).sum := by decide
  have hdescent : baseEnd_213995 < baseStart_213995 := by decide
  rcases family_descends (prefixWord ++ tailWord_213995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213999 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 5]
def baseStart_213999 : Nat := 118140960795 + 213999 * 2 ^ 59
def prefixEnd_213999 : Nat := 4983230072969 + 3 ^ 40 * 213999 * 2
def baseEnd_213999 : Nat := 24418743684802991472965

theorem tailTrace_213999 : CollatzResearch.WordTrace tailWord_213999 prefixEnd_213999 24418743684802991472965 := by
  unfold tailWord_213999
  simp only [CollatzResearch.WordTrace]
  refine ⟨7805184751725645964565051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5203456501150430643043367 7805184751725645964565051)
  ·
    refine ⟨11707777127588468946847577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7805184751725645964565051 11707777127588468946847577)
    ·
      refine ⟨8780832845691351710135683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11707777127588468946847577 8780832845691351710135683)
      ·
        refine ⟨13171249268537027565203525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8780832845691351710135683 13171249268537027565203525)
        ·
          refine ⟨2469609237850692668475661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13171249268537027565203525 2469609237850692668475661)
          ·
            refine ⟨926103464194009750678373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2469609237850692668475661 926103464194009750678373)
            ·
              refine ⟨173644399536376828252195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 926103464194009750678373 173644399536376828252195)
              ·
                refine ⟨260466599304565242378293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173644399536376828252195 260466599304565242378293)
                ·
                  refine ⟨24418743684802991472965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260466599304565242378293 24418743684802991472965)
                  ·
                    rfl

theorem cell22_213999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 5].length) (baseStart_213999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213999 prefixEnd_213999 := by exact prefixLift 213999
  have htrace : WordTrace (prefixWord ++ tailWord_213999) baseStart_213999 baseEnd_213999 := by
    simpa [prefixWord, tailWord_213999, baseEnd_213999] using wordTrace_append hprefix tailTrace_213999
  have hstable : (prefixWord ++ tailWord_213999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213999).length < 2 ^ (prefixWord ++ tailWord_213999).sum := by decide
  have hdescent : baseEnd_213999 < baseStart_213999 := by decide
  rcases family_descends (prefixWord ++ tailWord_213999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214042 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_214042 : Nat := 118140960795 + 214042 * 2 ^ 59
def prefixEnd_214042 : Nat := 4983230072969 + 3 ^ 40 * 214042 * 2
def baseEnd_214042 : Nat := 73270950833171195593763

theorem tailTrace_214042 : CollatzResearch.WordTrace tailWord_214042 prefixEnd_214042 73270950833171195593763 := by
  unfold tailWord_214042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951688272642466077095095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5204502060379909538920253 1951688272642466077095095)
  ·
    refine ⟨2927532408963699115642643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951688272642466077095095 2927532408963699115642643)
    ·
      refine ⟨4391298613445548673463965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2927532408963699115642643 4391298613445548673463965)
      ·
        refine ⟨1646736980042080752548987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4391298613445548673463965 1646736980042080752548987)
        ·
          refine ⟨2470105470063121128823481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646736980042080752548987 2470105470063121128823481)
          ·
            refine ⟨1852579102547340846617611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470105470063121128823481 1852579102547340846617611)
            ·
              refine ⟨2778868653821011269926417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852579102547340846617611 2778868653821011269926417)
              ·
                refine ⟨2084151490365758452444813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778868653821011269926417 2084151490365758452444813)
                ·
                  refine ⟨781556808887159419666805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2084151490365758452444813 781556808887159419666805)
                  ·
                    refine ⟨73270950833171195593763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 781556808887159419666805 73270950833171195593763)
                    ·
                      rfl

theorem cell22_214042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_214042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214042 prefixEnd_214042 := by exact prefixLift 214042
  have htrace : WordTrace (prefixWord ++ tailWord_214042) baseStart_214042 baseEnd_214042 := by
    simpa [prefixWord, tailWord_214042, baseEnd_214042] using wordTrace_append hprefix tailTrace_214042
  have hstable : (prefixWord ++ tailWord_214042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214042).length < 2 ^ (prefixWord ++ tailWord_214042).sum := by decide
  have hdescent : baseEnd_214042 < baseStart_214042 := by decide
  rcases family_descends (prefixWord ++ tailWord_214042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214059 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 2, 3]
def baseStart_214059 : Nat := 118140960795 + 214059 * 2 ^ 59
def prefixEnd_214059 : Nat := 4983230072969 + 3 ^ 40 * 214059 * 2
def baseEnd_214059 : Nat := 73276770280588817918711

theorem tailTrace_214059 : CollatzResearch.WordTrace tailWord_214059 prefixEnd_214059 73276770280588817918711 := by
  unfold tailWord_214059
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807373131508276211749231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5204915421005517474499487 7807373131508276211749231)
  ·
    refine ⟨11711059697262414317623847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7807373131508276211749231 11711059697262414317623847)
    ·
      refine ⟨17566589545893621476435771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711059697262414317623847 17566589545893621476435771)
      ·
        refine ⟨26349884318840432214653657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17566589545893621476435771 26349884318840432214653657)
        ·
          refine ⟨19762413239130324160990243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26349884318840432214653657 19762413239130324160990243)
          ·
            refine ⟨29643619858695486241485365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19762413239130324160990243 29643619858695486241485365)
            ·
              refine ⟨2779089361752701835139253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29643619858695486241485365 2779089361752701835139253)
              ·
                refine ⟨260539627664315797044305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2779089361752701835139253 260539627664315797044305)
                ·
                  refine ⟨195404720748236847783229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260539627664315797044305 195404720748236847783229)
                  ·
                    refine ⟨73276770280588817918711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195404720748236847783229 73276770280588817918711)
                    ·
                      rfl

theorem cell22_214059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 3].length) (baseStart_214059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214059 prefixEnd_214059 := by exact prefixLift 214059
  have htrace : WordTrace (prefixWord ++ tailWord_214059) baseStart_214059 baseEnd_214059 := by
    simpa [prefixWord, tailWord_214059, baseEnd_214059] using wordTrace_append hprefix tailTrace_214059
  have hstable : (prefixWord ++ tailWord_214059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214059).length < 2 ^ (prefixWord ++ tailWord_214059).sum := by decide
  have hdescent : baseEnd_214059 < baseStart_214059 := by decide
  rcases family_descends (prefixWord ++ tailWord_214059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214074 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_214074 : Nat := 118140960795 + 214074 * 2 ^ 59
def prefixEnd_214074 : Nat := 4983230072969 + 3 ^ 40 * 214074 * 2
def baseEnd_214074 : Nat := 73281905087133778793665

theorem tailTrace_214074 : CollatzResearch.WordTrace tailWord_214074 prefixEnd_214074 73281905087133778793665 := by
  unfold tailWord_214074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951980056613483443386319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5205280150969289182363517 1951980056613483443386319)
  ·
    refine ⟨2927970084920225165079479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951980056613483443386319 2927970084920225165079479)
    ·
      refine ⟨4391955127380337747619219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2927970084920225165079479 4391955127380337747619219)
      ·
        refine ⟨6587932691070506621428829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391955127380337747619219 6587932691070506621428829)
        ·
          refine ⟨2470474759151439983035811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6587932691070506621428829 2470474759151439983035811)
          ·
            refine ⟨3705712138727159974553717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470474759151439983035811 3705712138727159974553717)
            ·
              refine ⟨347410513005671247614411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3705712138727159974553717 347410513005671247614411)
              ·
                refine ⟨521115769508506871421617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347410513005671247614411 521115769508506871421617)
                ·
                  refine ⟨390836827131380153566213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521115769508506871421617 390836827131380153566213)
                  ·
                    refine ⟨73281905087133778793665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390836827131380153566213 73281905087133778793665)
                    ·
                      rfl

theorem cell22_214074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_214074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214074 prefixEnd_214074 := by exact prefixLift 214074
  have htrace : WordTrace (prefixWord ++ tailWord_214074) baseStart_214074 baseEnd_214074 := by
    simpa [prefixWord, tailWord_214074, baseEnd_214074] using wordTrace_append hprefix tailTrace_214074
  have hstable : (prefixWord ++ tailWord_214074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214074).length < 2 ^ (prefixWord ++ tailWord_214074).sum := by decide
  have hdescent : baseEnd_214074 < baseStart_214074 := by decide
  rcases family_descends (prefixWord ++ tailWord_214074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214078 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_214078 : Nat := 118140960795 + 214078 * 2 ^ 59
def prefixEnd_214078 : Nat := 4983230072969 + 3 ^ 40 * 214078 * 2
def baseEnd_214078 : Nat := 24427758122959700564551

theorem tailTrace_214078 : CollatzResearch.WordTrace tailWord_214078 prefixEnd_214078 24427758122959700564551 := by
  unfold tailWord_214078
  simp only [CollatzResearch.WordTrace]
  refine ⟨976008264804930307086361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5205377412292961637793925 976008264804930307086361)
  ·
    refine ⟨732006198603697730314771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 976008264804930307086361 732006198603697730314771)
    ·
      refine ⟨1098009297905546595472157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732006198603697730314771 1098009297905546595472157)
      ·
        refine ⟨411753486714579973302059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1098009297905546595472157 411753486714579973302059)
        ·
          refine ⟨617630230071869959953089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411753486714579973302059 617630230071869959953089)
          ·
            refine ⟨463222672553902469964817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617630230071869959953089 463222672553902469964817)
            ·
              refine ⟨347417004415426852473613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463222672553902469964817 347417004415426852473613)
              ·
                refine ⟨130281376655785069677605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347417004415426852473613 130281376655785069677605)
                ·
                  refine ⟨24427758122959700564551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130281376655785069677605 24427758122959700564551)
                  ·
                    rfl

theorem cell22_214078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_214078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214078 prefixEnd_214078 := by exact prefixLift 214078
  have htrace : WordTrace (prefixWord ++ tailWord_214078) baseStart_214078 baseEnd_214078 := by
    simpa [prefixWord, tailWord_214078, baseEnd_214078] using wordTrace_append hprefix tailTrace_214078
  have hstable : (prefixWord ++ tailWord_214078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214078).length < 2 ^ (prefixWord ++ tailWord_214078).sum := by decide
  have hdescent : baseEnd_214078 < baseStart_214078 := by decide
  rcases family_descends (prefixWord ++ tailWord_214078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214093 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_214093 : Nat := 118140960795 + 214093 * 2 ^ 59
def prefixEnd_214093 : Nat := 4983230072969 + 3 ^ 40 * 214093 * 2
def baseEnd_214093 : Nat := 73288409175424062568607

theorem tailTrace_214093 : CollatzResearch.WordTrace tailWord_214093 prefixEnd_214093 73288409175424062568607 := by
  unfold tailWord_214093
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808613213385100018486933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5205742142256733345657955 7808613213385100018486933)
  ·
    refine ⟨366028744377426563366575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7808613213385100018486933 366028744377426563366575)
    ·
      refine ⟨549043116566139845049863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366028744377426563366575 549043116566139845049863)
      ·
        refine ⟨823564674849209767574795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549043116566139845049863 823564674849209767574795)
        ·
          refine ⟨1235347012273814651362193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823564674849209767574795 1235347012273814651362193)
          ·
            refine ⟨926510259205360988521645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235347012273814651362193 926510259205360988521645)
            ·
              refine ⟨347441347202010370695617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926510259205360988521645 347441347202010370695617)
              ·
                refine ⟨260581010401507778021713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347441347202010370695617 260581010401507778021713)
                ·
                  refine ⟨195435757801130833516285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260581010401507778021713 195435757801130833516285)
                  ·
                    refine ⟨73288409175424062568607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195435757801130833516285 73288409175424062568607)
                    ·
                      rfl

theorem cell22_214093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_214093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214093 prefixEnd_214093 := by exact prefixLift 214093
  have htrace : WordTrace (prefixWord ++ tailWord_214093) baseStart_214093 baseEnd_214093 := by
    simpa [prefixWord, tailWord_214093, baseEnd_214093] using wordTrace_append hprefix tailTrace_214093
  have hstable : (prefixWord ++ tailWord_214093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214093).length < 2 ^ (prefixWord ++ tailWord_214093).sum := by decide
  have hdescent : baseEnd_214093 < baseStart_214093 := by decide
  rcases family_descends (prefixWord ++ tailWord_214093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214110 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_214110 : Nat := 118140960795 + 214110 * 2 ^ 59
def prefixEnd_214110 : Nat := 4983230072969 + 3 ^ 40 * 214110 * 2
def baseEnd_214110 : Nat := 73294228622841684893555

theorem tailTrace_214110 : CollatzResearch.WordTrace tailWord_214110 prefixEnd_214110 73294228622841684893555 := by
  unfold tailWord_214110
  simp only [CollatzResearch.WordTrace]
  refine ⟨976154156790438990231973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5206155502882341281237189 976154156790438990231973)
  ·
    refine ⟨183028904398207310668495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 976154156790438990231973 183028904398207310668495)
    ·
      refine ⟨274543356597310966002743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183028904398207310668495 274543356597310966002743)
      ·
        refine ⟨411815034895966449004115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274543356597310966002743 411815034895966449004115)
        ·
          refine ⟨617722552343949673506173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411815034895966449004115 617722552343949673506173)
          ·
            refine ⟨231645957128981127564815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617722552343949673506173 231645957128981127564815)
            ·
              refine ⟨347468935693471691347223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231645957128981127564815 347468935693471691347223)
              ·
                refine ⟨521203403540207537020835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347468935693471691347223 521203403540207537020835)
                ·
                  refine ⟨781805105310311305531253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521203403540207537020835 781805105310311305531253)
                  ·
                    refine ⟨73294228622841684893555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 781805105310311305531253 73294228622841684893555)
                    ·
                      rfl

theorem cell22_214110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_214110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214110 prefixEnd_214110 := by exact prefixLift 214110
  have htrace : WordTrace (prefixWord ++ tailWord_214110) baseStart_214110 baseEnd_214110 := by
    simpa [prefixWord, tailWord_214110, baseEnd_214110] using wordTrace_append hprefix tailTrace_214110
  have hstable : (prefixWord ++ tailWord_214110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214110).length < 2 ^ (prefixWord ++ tailWord_214110).sum := by decide
  have hdescent : baseEnd_214110 < baseStart_214110 := by decide
  rcases family_descends (prefixWord ++ tailWord_214110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214134 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_214134 : Nat := 118140960795 + 214134 * 2 ^ 59
def prefixEnd_214134 : Nat := 4983230072969 + 3 ^ 40 * 214134 * 2
def baseEnd_214134 : Nat := 24434148104437874097827

theorem tailTrace_214134 : CollatzResearch.WordTrace tailWord_214134 prefixEnd_214134 24434148104437874097827 := by
  unfold tailWord_214134
  simp only [CollatzResearch.WordTrace]
  refine ⟨488131787889785251295591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5206739070824376013819637 488131787889785251295591)
  ·
    refine ⟨732197681834677876943387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488131787889785251295591 732197681834677876943387)
    ·
      refine ⟨1098296522752016815415081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732197681834677876943387 1098296522752016815415081)
      ·
        refine ⟨823722392064012611561311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098296522752016815415081 823722392064012611561311)
        ·
          refine ⟨1235583588096018917341967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823722392064012611561311 1235583588096018917341967)
          ·
            refine ⟨1853375382144028376012951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235583588096018917341967 1853375382144028376012951)
            ·
              refine ⟨2780063073216042564019427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853375382144028376012951 2780063073216042564019427)
              ·
                refine ⟨4170094609824063846029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780063073216042564019427 4170094609824063846029141)
                ·
                  refine ⟨24434148104437874097827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4170094609824063846029141 24434148104437874097827)
                  ·
                    rfl

theorem cell22_214134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_214134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214134 prefixEnd_214134 := by exact prefixLift 214134
  have htrace : WordTrace (prefixWord ++ tailWord_214134) baseStart_214134 baseEnd_214134 := by
    simpa [prefixWord, tailWord_214134, baseEnd_214134] using wordTrace_append hprefix tailTrace_214134
  have hstable : (prefixWord ++ tailWord_214134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214134).length < 2 ^ (prefixWord ++ tailWord_214134).sum := by decide
  have hdescent : baseEnd_214134 < baseStart_214134 := by decide
  rcases family_descends (prefixWord ++ tailWord_214134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214168 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 5]
def baseStart_214168 : Nat := 118140960795 + 214168 * 2 ^ 59
def prefixEnd_214168 : Nat := 4983230072969 + 3 ^ 40 * 214168 * 2
def baseEnd_214168 : Nat := 24438027736049622314459

theorem tailTrace_214168 : CollatzResearch.WordTrace tailWord_214168 prefixEnd_214168 24438027736049622314459 := by
  unfold tailWord_214168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905674344056693913733579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5207565792075591884978105 3905674344056693913733579)
  ·
    refine ⟨5858511516085040870600369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905674344056693913733579 5858511516085040870600369)
    ·
      refine ⟨4393883637063780652950277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5858511516085040870600369 4393883637063780652950277)
      ·
        refine ⟨823853181949458872428177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4393883637063780652950277 823853181949458872428177)
        ·
          refine ⟨617889886462094154321133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823853181949458872428177 617889886462094154321133)
          ·
            refine ⟨231708707423285307870425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617889886462094154321133 231708707423285307870425)
            ·
              refine ⟨173781530567463980902819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231708707423285307870425 173781530567463980902819)
              ·
                refine ⟨260672295851195971354229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173781530567463980902819 260672295851195971354229)
                ·
                  refine ⟨24438027736049622314459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260672295851195971354229 24438027736049622314459)
                  ·
                    rfl

theorem cell22_214168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_214168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214168 prefixEnd_214168 := by exact prefixLift 214168
  have htrace : WordTrace (prefixWord ++ tailWord_214168) baseStart_214168 baseEnd_214168 := by
    simpa [prefixWord, tailWord_214168, baseEnd_214168] using wordTrace_append hprefix tailTrace_214168
  have hstable : (prefixWord ++ tailWord_214168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214168).length < 2 ^ (prefixWord ++ tailWord_214168).sum := by decide
  have hdescent : baseEnd_214168 < baseStart_214168 := by decide
  rcases family_descends (prefixWord ++ tailWord_214168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214181 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_214181 : Nat := 118140960795 + 214181 * 2 ^ 59
def prefixEnd_214181 : Nat := 4983230072969 + 3 ^ 40 * 214181 * 2
def baseEnd_214181 : Nat := 73318533373821166368337

theorem tailTrace_214181 : CollatzResearch.WordTrace tailWord_214181 prefixEnd_214181 73318533373821166368337 := by
  unfold tailWord_214181
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811822837066291047690397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5207881891377527365126931 7811822837066291047690397)
  ·
    refine ⟨2929433563899859142883899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7811822837066291047690397 2929433563899859142883899)
    ·
      refine ⟨4394150345849788714325849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929433563899859142883899 4394150345849788714325849)
      ·
        refine ⟨3295612759387341535744387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4394150345849788714325849 3295612759387341535744387)
        ·
          refine ⟨4943419139081012303616581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295612759387341535744387 4943419139081012303616581)
          ·
            refine ⟨926891088577689806928109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4943419139081012303616581 926891088577689806928109)
            ·
              refine ⟨347584158216633677598041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926891088577689806928109 347584158216633677598041)
              ·
                refine ⟨260688118662475258198531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347584158216633677598041 260688118662475258198531)
                ·
                  refine ⟨391032177993712887297797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260688118662475258198531 391032177993712887297797)
                  ·
                    refine ⟨73318533373821166368337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391032177993712887297797 73318533373821166368337)
                    ·
                      rfl

theorem cell22_214181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_214181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214181 prefixEnd_214181 := by exact prefixLift 214181
  have htrace : WordTrace (prefixWord ++ tailWord_214181) baseStart_214181 baseEnd_214181 := by
    simpa [prefixWord, tailWord_214181, baseEnd_214181] using wordTrace_append hprefix tailTrace_214181
  have hstable : (prefixWord ++ tailWord_214181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214181).length < 2 ^ (prefixWord ++ tailWord_214181).sum := by decide
  have hdescent : baseEnd_214181 < baseStart_214181 := by decide
  rcases family_descends (prefixWord ++ tailWord_214181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214194 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_214194 : Nat := 118140960795 + 214194 * 2 ^ 59
def prefixEnd_214194 : Nat := 4983230072969 + 3 ^ 40 * 214194 * 2
def baseEnd_214194 : Nat := 73322983539493465793297

theorem tailTrace_214194 : CollatzResearch.WordTrace tailWord_214194 prefixEnd_214194 73322983539493465793297 := by
  unfold tailWord_214194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953074246504798566978409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5208197990679462845275757 1953074246504798566978409)
  ·
    refine ⟨1464805684878598925233807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1953074246504798566978409 1464805684878598925233807)
    ·
      refine ⟨2197208527317898387850711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464805684878598925233807 2197208527317898387850711)
      ·
        refine ⟨3295812790976847581776067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197208527317898387850711 3295812790976847581776067)
        ·
          refine ⟨4943719186465271372664101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295812790976847581776067 4943719186465271372664101)
          ·
            refine ⟨926947347462238382374519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4943719186465271372664101 926947347462238382374519)
            ·
              refine ⟨1390421021193357573561779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926947347462238382374519 1390421021193357573561779)
              ·
                refine ⟨2085631531790036360342669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390421021193357573561779 2085631531790036360342669)
                ·
                  refine ⟨782111824421263635128501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2085631531790036360342669 782111824421263635128501)
                  ·
                    refine ⟨73322983539493465793297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 782111824421263635128501 73322983539493465793297)
                    ·
                      rfl

theorem cell22_214194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_214194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214194 prefixEnd_214194 := by exact prefixLift 214194
  have htrace : WordTrace (prefixWord ++ tailWord_214194) baseStart_214194 baseEnd_214194 := by
    simpa [prefixWord, tailWord_214194, baseEnd_214194] using wordTrace_append hprefix tailTrace_214194
  have hstable : (prefixWord ++ tailWord_214194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214194).length < 2 ^ (prefixWord ++ tailWord_214194).sum := by decide
  have hdescent : baseEnd_214194 < baseStart_214194 := by decide
  rcases family_descends (prefixWord ++ tailWord_214194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214241 : List Nat := [1, 2, 3, 1, 3, 3, 3, 6]
def baseStart_214241 : Nat := 118140960795 + 214241 * 2 ^ 59
def prefixEnd_214241 : Nat := 4983230072969 + 3 ^ 40 * 214241 * 2
def baseEnd_214241 : Nat := 8148785844444556652017

theorem tailTrace_214241 : CollatzResearch.WordTrace tailWord_214241 prefixEnd_214241 8148785844444556652017 := by
  unfold tailWord_214241
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814011216848921294874577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5209340811232614196583051 7814011216848921294874577)
  ·
    refine ⟨5860508412636690971155933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7814011216848921294874577 5860508412636690971155933)
    ·
      refine ⟨2197690654738759114183475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5860508412636690971155933 2197690654738759114183475)
      ·
        refine ⟨3296535982108138671275213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197690654738759114183475 3296535982108138671275213)
        ·
          refine ⟨1236200993290552001728205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3296535982108138671275213 1236200993290552001728205)
          ·
            refine ⟨463575372483957000648077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1236200993290552001728205 463575372483957000648077)
            ·
              refine ⟨173840764681483875243029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463575372483957000648077 173840764681483875243029)
              ·
                refine ⟨8148785844444556652017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173840764681483875243029 8148785844444556652017)
                ·
                  rfl

theorem cell22_214241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 6].length) (baseStart_214241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214241 prefixEnd_214241 := by exact prefixLift 214241
  have htrace : WordTrace (prefixWord ++ tailWord_214241) baseStart_214241 baseEnd_214241 := by
    simpa [prefixWord, tailWord_214241, baseEnd_214241] using wordTrace_append hprefix tailTrace_214241
  have hstable : (prefixWord ++ tailWord_214241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214241).length < 2 ^ (prefixWord ++ tailWord_214241).sum := by decide
  have hdescent : baseEnd_214241 < baseStart_214241 := by decide
  rcases family_descends (prefixWord ++ tailWord_214241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214273 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_214273 : Nat := 118140960795 + 214273 * 2 ^ 59
def prefixEnd_214273 : Nat := 4983230072969 + 3 ^ 40 * 214273 * 2
def baseEnd_214273 : Nat := 73350026853963593068055

theorem tailTrace_214273 : CollatzResearch.WordTrace tailWord_214273 prefixEnd_214273 73350026853963593068055 := by
  unfold tailWord_214273
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815178352732990760039473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5210118901821993840026315 7815178352732990760039473)
  ·
    refine ⟨5861383764549743070029605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7815178352732990760039473 5861383764549743070029605)
    ·
      refine ⟨1099009455853076825630551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5861383764549743070029605 1099009455853076825630551)
      ·
        refine ⟨1648514183779615238445827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099009455853076825630551 1648514183779615238445827)
        ·
          refine ⟨2472771275669422857668741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648514183779615238445827 2472771275669422857668741)
          ·
            refine ⟨463644614188016785812889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2472771275669422857668741 463644614188016785812889)
            ·
              refine ⟨347733460641012589359667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463644614188016785812889 347733460641012589359667)
              ·
                refine ⟨521600190961518884039501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347733460641012589359667 521600190961518884039501)
                ·
                  refine ⟨195600071610569581514813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521600190961518884039501 195600071610569581514813)
                  ·
                    refine ⟨73350026853963593068055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195600071610569581514813 73350026853963593068055)
                    ·
                      rfl

theorem cell22_214273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_214273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214273 prefixEnd_214273 := by exact prefixLift 214273
  have htrace : WordTrace (prefixWord ++ tailWord_214273) baseStart_214273 baseEnd_214273 := by
    simpa [prefixWord, tailWord_214273, baseEnd_214273] using wordTrace_append hprefix tailTrace_214273
  have hstable : (prefixWord ++ tailWord_214273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214273).length < 2 ^ (prefixWord ++ tailWord_214273).sum := by decide
  have hdescent : baseEnd_214273 < baseStart_214273 := by decide
  rcases family_descends (prefixWord ++ tailWord_214273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214361 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_214361 : Nat := 118140960795 + 214361 * 2 ^ 59
def prefixEnd_214361 : Nat := 4983230072969 + 3 ^ 40 * 214361 * 2
def baseEnd_214361 : Nat := 73380151052360696867785

theorem tailTrace_214361 : CollatzResearch.WordTrace tailWord_214361 prefixEnd_214361 73380151052360696867785 := by
  unfold tailWord_214361
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818387976414181789242937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5212258650942787859495291 7818387976414181789242937)
  ·
    refine ⟨5863790982310636341932203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7818387976414181789242937 5863790982310636341932203)
    ·
      refine ⟨8795686473465954512898305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5863790982310636341932203 8795686473465954512898305)
      ·
        refine ⟨6596764855099465884673729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8795686473465954512898305 6596764855099465884673729)
        ·
          refine ⟨4947573641324599413505297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596764855099465884673729 4947573641324599413505297)
          ·
            refine ⟨3710680230993449560128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4947573641324599413505297 3710680230993449560128973)
            ·
              refine ⟨1391505086622543585048365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3710680230993449560128973 1391505086622543585048365)
              ·
                refine ⟨521814407483453844393137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391505086622543585048365 521814407483453844393137)
                ·
                  refine ⟨391360805612590383294853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521814407483453844393137 391360805612590383294853)
                  ·
                    refine ⟨73380151052360696867785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391360805612590383294853 73380151052360696867785)
                    ·
                      rfl

theorem cell22_214361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_214361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214361 prefixEnd_214361 := by exact prefixLift 214361
  have htrace : WordTrace (prefixWord ++ tailWord_214361) baseStart_214361 baseEnd_214361 := by
    simpa [prefixWord, tailWord_214361, baseEnd_214361] using wordTrace_append hprefix tailTrace_214361
  have hstable : (prefixWord ++ tailWord_214361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214361).length < 2 ^ (prefixWord ++ tailWord_214361).sum := by decide
  have hdescent : baseEnd_214361 < baseStart_214361 := by decide
  rcases family_descends (prefixWord ++ tailWord_214361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214376 : List Nat := [2, 1, 4, 2, 3, 10]
def baseStart_214376 : Nat := 118140960795 + 214376 * 2 ^ 59
def prefixEnd_214376 : Nat := 4983230072969 + 3 ^ 40 * 214376 * 2
def baseEnd_214376 : Nat := 905991183443279725219

theorem tailTrace_214376 : CollatzResearch.WordTrace tailWord_214376 prefixEnd_214376 905991183443279725219 := by
  unfold tailWord_214376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909467535679919675519491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5212623380906559567359321 3909467535679919675519491)
  ·
    refine ⟨5864201303519879513279237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3909467535679919675519491 5864201303519879513279237)
    ·
      refine ⟨1099537744409977408739857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5864201303519879513279237 1099537744409977408739857)
      ·
        refine ⟨824653308307483056554893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099537744409977408739857 824653308307483056554893)
        ·
          refine ⟨309244990615306146208085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 824653308307483056554893 309244990615306146208085)
          ·
            refine ⟨905991183443279725219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 309244990615306146208085 905991183443279725219)
            ·
              rfl

theorem cell22_214376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 10].length) (baseStart_214376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214376 prefixEnd_214376 := by exact prefixLift 214376
  have htrace : WordTrace (prefixWord ++ tailWord_214376) baseStart_214376 baseEnd_214376 := by
    simpa [prefixWord, tailWord_214376, baseEnd_214376] using wordTrace_append hprefix tailTrace_214376
  have hstable : (prefixWord ++ tailWord_214376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214376).length < 2 ^ (prefixWord ++ tailWord_214376).sum := by decide
  have hdescent : baseEnd_214376 < baseStart_214376 := by decide
  rcases family_descends (prefixWord ++ tailWord_214376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214380 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_214380 : Nat := 118140960795 + 214380 * 2 ^ 59
def prefixEnd_214380 : Nat := 4983230072969 + 3 ^ 40 * 214380 * 2
def baseEnd_214380 : Nat := 73386655140650980642727

theorem tailTrace_214380 : CollatzResearch.WordTrace tailWord_214380 prefixEnd_214380 73386655140650980642727 := by
  unfold tailWord_214380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909540481672674017092297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5212720642230232022789729 3909540481672674017092297)
  ·
    refine ⟨2932155361254505512819223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3909540481672674017092297 2932155361254505512819223)
    ·
      refine ⟨4398233041881758269228835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2932155361254505512819223 4398233041881758269228835)
      ·
        refine ⟨6597349562822637403843253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398233041881758269228835 6597349562822637403843253)
        ·
          refine ⟨618501521514622256610305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6597349562822637403843253 618501521514622256610305)
          ·
            refine ⟨463876141135966692457729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618501521514622256610305 463876141135966692457729)
            ·
              refine ⟨347907105851975019343297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463876141135966692457729 347907105851975019343297)
              ·
                refine ⟨260930329388981264507473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347907105851975019343297 260930329388981264507473)
                ·
                  refine ⟨195697747041735948380605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260930329388981264507473 195697747041735948380605)
                  ·
                    refine ⟨73386655140650980642727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195697747041735948380605 73386655140650980642727)
                    ·
                      rfl

theorem cell22_214380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_214380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214380 prefixEnd_214380 := by exact prefixLift 214380
  have htrace : WordTrace (prefixWord ++ tailWord_214380) baseStart_214380 baseEnd_214380 := by
    simpa [prefixWord, tailWord_214380, baseEnd_214380] using wordTrace_append hprefix tailTrace_214380
  have hstable : (prefixWord ++ tailWord_214380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214380).length < 2 ^ (prefixWord ++ tailWord_214380).sum := by decide
  have hdescent : baseEnd_214380 < baseStart_214380 := by decide
  rcases family_descends (prefixWord ++ tailWord_214380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214382 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_214382 : Nat := 118140960795 + 214382 * 2 ^ 59
def prefixEnd_214382 : Nat := 4983230072969 + 3 ^ 40 * 214382 * 2
def baseEnd_214382 : Nat := 24462446593841214030907

theorem tailTrace_214382 : CollatzResearch.WordTrace tailWord_214382 prefixEnd_214382 24462446593841214030907 := by
  unfold tailWord_214382
  simp only [CollatzResearch.WordTrace]
  refine ⟨977394238667262796969675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5212769272892068250504933 977394238667262796969675)
  ·
    refine ⟨1466091358000894195454513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977394238667262796969675 1466091358000894195454513)
    ·
      refine ⟨1099568518500670646590885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1466091358000894195454513 1099568518500670646590885)
      ·
        refine ⟨206169097218875746235791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1099568518500670646590885 206169097218875746235791)
        ·
          refine ⟨309253645828313619353687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206169097218875746235791 309253645828313619353687)
          ·
            refine ⟨463880468742470429030531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309253645828313619353687 463880468742470429030531)
            ·
              refine ⟨695820703113705643545797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463880468742470429030531 695820703113705643545797)
              ·
                refine ⟨130466381833819808164837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695820703113705643545797 130466381833819808164837)
                ·
                  refine ⟨24462446593841214030907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130466381833819808164837 24462446593841214030907)
                  ·
                    rfl

theorem cell22_214382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_214382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214382 prefixEnd_214382 := by exact prefixLift 214382
  have htrace : WordTrace (prefixWord ++ tailWord_214382) baseStart_214382 baseEnd_214382 := by
    simpa [prefixWord, tailWord_214382, baseEnd_214382] using wordTrace_append hprefix tailTrace_214382
  have hstable : (prefixWord ++ tailWord_214382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214382).length < 2 ^ (prefixWord ++ tailWord_214382).sum := by decide
  have hdescent : baseEnd_214382 < baseStart_214382 := by decide
  rcases family_descends (prefixWord ++ tailWord_214382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214408 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_214408 : Nat := 118140960795 + 214408 * 2 ^ 59
def prefixEnd_214408 : Nat := 4983230072969 + 3 ^ 40 * 214408 * 2
def baseEnd_214408 : Nat := 73396240112868240942641

theorem tailTrace_214408 : CollatzResearch.WordTrace tailWord_214408 prefixEnd_214408 73396240112868240942641 := by
  unfold tailWord_214408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910051103621954408101939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5213401471495939210802585 3910051103621954408101939)
  ·
    refine ⟨5865076655432931612152909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3910051103621954408101939 5865076655432931612152909)
    ·
      refine ⟨2199403745787349354557341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5865076655432931612152909 2199403745787349354557341)
      ·
        refine ⟨824776404670256007959003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2199403745787349354557341 824776404670256007959003)
        ·
          refine ⟨1237164607005384011938505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824776404670256007959003 1237164607005384011938505)
          ·
            refine ⟨927873455254038008953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237164607005384011938505 927873455254038008953879)
            ·
              refine ⟨1391810182881057013430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927873455254038008953879 1391810182881057013430819)
              ·
                refine ⟨2087715274321585520146229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391810182881057013430819 2087715274321585520146229)
                ·
                  refine ⟨195723306967648642513709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087715274321585520146229 195723306967648642513709)
                  ·
                    refine ⟨73396240112868240942641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195723306967648642513709 73396240112868240942641)
                    ·
                      rfl

theorem cell22_214408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_214408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214408 prefixEnd_214408 := by exact prefixLift 214408
  have htrace : WordTrace (prefixWord ++ tailWord_214408) baseStart_214408 baseEnd_214408 := by
    simpa [prefixWord, tailWord_214408, baseEnd_214408] using wordTrace_append hprefix tailTrace_214408
  have hstable : (prefixWord ++ tailWord_214408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214408).length < 2 ^ (prefixWord ++ tailWord_214408).sum := by decide
  have hdescent : baseEnd_214408 < baseStart_214408 := by decide
  rcases family_descends (prefixWord ++ tailWord_214408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214425 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 1, 3]
def baseStart_214425 : Nat := 118140960795 + 214425 * 2 ^ 59
def prefixEnd_214425 : Nat := 4983230072969 + 3 ^ 40 * 214425 * 2
def baseEnd_214425 : Nat := 73402059560285863267589

theorem tailTrace_214425 : CollatzResearch.WordTrace tailWord_214425 prefixEnd_214425 73402059560285863267589 := by
  unfold tailWord_214425
  simp only [CollatzResearch.WordTrace]
  refine ⟨7820722248182320719572729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5213814832121547146381819 7820722248182320719572729)
  ·
    refine ⟨5865541686136740539679547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7820722248182320719572729 5865541686136740539679547)
    ·
      refine ⟨8798312529205110809519321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865541686136740539679547 8798312529205110809519321)
      ·
        refine ⟨6598734396903833107139491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8798312529205110809519321 6598734396903833107139491)
        ·
          refine ⟨9898101595355749660709237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598734396903833107139491 9898101595355749660709237)
          ·
            refine ⟨927947024564601530691491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9898101595355749660709237 927947024564601530691491)
            ·
              refine ⟨1391920536846902296037237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927947024564601530691491 1391920536846902296037237)
              ·
                refine ⟨130492550329397090253491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1391920536846902296037237 130492550329397090253491)
                ·
                  refine ⟨195738825494095635380237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130492550329397090253491 195738825494095635380237)
                  ·
                    refine ⟨73402059560285863267589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195738825494095635380237 73402059560285863267589)
                    ·
                      rfl

theorem cell22_214425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_214425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214425 prefixEnd_214425 := by exact prefixLift 214425
  have htrace : WordTrace (prefixWord ++ tailWord_214425) baseStart_214425 baseEnd_214425 := by
    simpa [prefixWord, tailWord_214425, baseEnd_214425] using wordTrace_append hprefix tailTrace_214425
  have hstable : (prefixWord ++ tailWord_214425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214425).length < 2 ^ (prefixWord ++ tailWord_214425).sum := by decide
  have hdescent : baseEnd_214425 < baseStart_214425 := by decide
  rcases family_descends (prefixWord ++ tailWord_214425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214451 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 5, 4]
def baseStart_214451 : Nat := 118140960795 + 214451 * 2 ^ 59
def prefixEnd_214451 : Nat := 4983230072969 + 3 ^ 40 * 214451 * 2
def baseEnd_214451 : Nat := 73410959891630462117509

theorem tailTrace_214451 : CollatzResearch.WordTrace tailWord_214451 prefixEnd_214451 73410959891630462117509 := by
  unfold tailWord_214451
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821670546088127160019207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5214447030725418106679471 7821670546088127160019207)
  ·
    refine ⟨11732505819132190740028811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7821670546088127160019207 11732505819132190740028811)
    ·
      refine ⟨17598758728698286110043217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11732505819132190740028811 17598758728698286110043217)
      ·
        refine ⟨13199069046523714582532413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17598758728698286110043217 13199069046523714582532413)
        ·
          refine ⟨4949650892446392968449655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13199069046523714582532413 4949650892446392968449655)
          ·
            refine ⟨7424476338669589452674483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949650892446392968449655 7424476338669589452674483)
            ·
              refine ⟨11136714508004384179011725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424476338669589452674483 11136714508004384179011725)
              ·
                refine ⟨4176267940501644067129397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11136714508004384179011725 4176267940501644067129397)
                ·
                  refine ⟨391525119422029131293381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176267940501644067129397 391525119422029131293381)
                  ·
                    refine ⟨73410959891630462117509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391525119422029131293381 73410959891630462117509)
                    ·
                      rfl

theorem cell22_214451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_214451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214451 prefixEnd_214451 := by exact prefixLift 214451
  have htrace : WordTrace (prefixWord ++ tailWord_214451) baseStart_214451 baseEnd_214451 := by
    simpa [prefixWord, tailWord_214451, baseEnd_214451] using wordTrace_append hprefix tailTrace_214451
  have hstable : (prefixWord ++ tailWord_214451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214451).length < 2 ^ (prefixWord ++ tailWord_214451).sum := by decide
  have hdescent : baseEnd_214451 < baseStart_214451 := by decide
  rcases family_descends (prefixWord ++ tailWord_214451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214453 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_214453 : Nat := 118140960795 + 214453 * 2 ^ 59
def prefixEnd_214453 : Nat := 4983230072969 + 3 ^ 40 * 214453 * 2
def baseEnd_214453 : Nat := 73411644532503123567503

theorem tailTrace_214453 : CollatzResearch.WordTrace tailWord_214453 prefixEnd_214453 73411644532503123567503 := by
  unfold tailWord_214453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821743492080881501592013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5214495661387254334394675 7821743492080881501592013)
  ·
    refine ⟨2933153809530330563097005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7821743492080881501592013 2933153809530330563097005)
    ·
      refine ⟨1099932678573873961161377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2933153809530330563097005 1099932678573873961161377)
      ·
        refine ⟨824949508930405470871033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099932678573873961161377 824949508930405470871033)
        ·
          refine ⟨618712131697804103153275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824949508930405470871033 618712131697804103153275)
          ·
            refine ⟨928068197546706154729913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618712131697804103153275 928068197546706154729913)
            ·
              refine ⟨696051148160029616047435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928068197546706154729913 696051148160029616047435)
              ·
                refine ⟨1044076722240044424071153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696051148160029616047435 1044076722240044424071153)
                ·
                  refine ⟨783057541680033318053365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044076722240044424071153 783057541680033318053365)
                  ·
                    refine ⟨73411644532503123567503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 783057541680033318053365 73411644532503123567503)
                    ·
                      rfl

theorem cell22_214453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_214453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214453 prefixEnd_214453 := by exact prefixLift 214453
  have htrace : WordTrace (prefixWord ++ tailWord_214453) baseStart_214453 baseEnd_214453 := by
    simpa [prefixWord, tailWord_214453, baseEnd_214453] using wordTrace_append hprefix tailTrace_214453
  have hstable : (prefixWord ++ tailWord_214453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214453).length < 2 ^ (prefixWord ++ tailWord_214453).sum := by decide
  have hdescent : baseEnd_214453 < baseStart_214453 := by decide
  rcases family_descends (prefixWord ++ tailWord_214453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214496 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_214496 : Nat := 118140960795 + 214496 * 2 ^ 59
def prefixEnd_214496 : Nat := 4983230072969 + 3 ^ 40 * 214496 * 2
def baseEnd_214496 : Nat := 73426364311265344742371

theorem tailTrace_214496 : CollatzResearch.WordTrace tailWord_214496 prefixEnd_214496 73426364311265344742371 := by
  unfold tailWord_214496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911655915462549922703671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5215541220616733230271561 3911655915462549922703671)
  ·
    refine ⟨5867483873193824884055507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3911655915462549922703671 5867483873193824884055507)
    ·
      refine ⟨8801225809790737326083261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867483873193824884055507 8801225809790737326083261)
      ·
        refine ⟨3300459678671526497281223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8801225809790737326083261 3300459678671526497281223)
        ·
          refine ⟨4950689518007289745921835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300459678671526497281223 4950689518007289745921835)
          ·
            refine ⟨7426034277010934618882753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950689518007289745921835 7426034277010934618882753)
            ·
              refine ⟨5569525707758200964162065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7426034277010934618882753 5569525707758200964162065)
              ·
                refine ⟨4177144280818650723121549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569525707758200964162065 4177144280818650723121549)
                ·
                  refine ⟨1566429105306994021170581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4177144280818650723121549 1566429105306994021170581)
                  ·
                    refine ⟨73426364311265344742371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1566429105306994021170581 73426364311265344742371)
                    ·
                      rfl

theorem cell22_214496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_214496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214496 prefixEnd_214496 := by exact prefixLift 214496
  have htrace : WordTrace (prefixWord ++ tailWord_214496) baseStart_214496 baseEnd_214496 := by
    simpa [prefixWord, tailWord_214496, baseEnd_214496] using wordTrace_append hprefix tailTrace_214496
  have hstable : (prefixWord ++ tailWord_214496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214496).length < 2 ^ (prefixWord ++ tailWord_214496).sum := by decide
  have hdescent : baseEnd_214496 < baseStart_214496 := by decide
  rcases family_descends (prefixWord ++ tailWord_214496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214511 : List Nat := [1, 1, 2, 1, 4, 1, 3, 9]
def baseStart_214511 : Nat := 118140960795 + 214511 * 2 ^ 59
def prefixEnd_214511 : Nat := 4983230072969 + 3 ^ 40 * 214511 * 2
def baseEnd_214511 : Nat := 8159055457534478401925

theorem tailTrace_214511 : CollatzResearch.WordTrace tailWord_214511 prefixEnd_214511 8159055457534478401925 := by
  unfold tailWord_214511
  simp only [CollatzResearch.WordTrace]
  refine ⟨7823858925870757407203387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5215905950580504938135591 7823858925870757407203387)
  ·
    refine ⟨11735788388806136110805081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7823858925870757407203387 11735788388806136110805081)
    ·
      refine ⟨8801841291604602083103811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11735788388806136110805081 8801841291604602083103811)
      ·
        refine ⟨13202761937406903124655717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801841291604602083103811 13202761937406903124655717)
        ·
          refine ⟨2475517863263794335872947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13202761937406903124655717 2475517863263794335872947)
          ·
            refine ⟨3713276794895691503809421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475517863263794335872947 3713276794895691503809421)
            ·
              refine ⟨1392478798085884313928533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3713276794895691503809421 1392478798085884313928533)
              ·
                refine ⟨8159055457534478401925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1392478798085884313928533 8159055457534478401925)
                ·
                  rfl

theorem cell22_214511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 9].length) (baseStart_214511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214511 prefixEnd_214511 := by exact prefixLift 214511
  have htrace : WordTrace (prefixWord ++ tailWord_214511) baseStart_214511 baseEnd_214511 := by
    simpa [prefixWord, tailWord_214511, baseEnd_214511] using wordTrace_append hprefix tailTrace_214511
  have hstable : (prefixWord ++ tailWord_214511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214511).length < 2 ^ (prefixWord ++ tailWord_214511).sum := by decide
  have hdescent : baseEnd_214511 < baseStart_214511 := by decide
  rcases family_descends (prefixWord ++ tailWord_214511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214663 : List Nat := [1, 1, 4, 2, 1, 3, 10]
def baseStart_214663 : Nat := 118140960795 + 214663 * 2 ^ 59
def prefixEnd_214663 : Nat := 4983230072969 + 3 ^ 40 * 214663 * 2
def baseEnd_214663 : Nat := 2721612289782687993217

theorem tailTrace_214663 : CollatzResearch.WordTrace tailWord_214663 prefixEnd_214663 2721612289782687993217 := by
  unfold tailWord_214663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7829402821320087366736643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5219601880880058244491095 7829402821320087366736643)
  ·
    refine ⟨11744104231980131050104965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7829402821320087366736643 11744104231980131050104965)
    ·
      refine ⟨2202019543496274571894681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11744104231980131050104965 2202019543496274571894681)
      ·
        refine ⟨1651514657622205928921011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2202019543496274571894681 1651514657622205928921011)
        ·
          refine ⟨2477271986433308893381517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651514657622205928921011 2477271986433308893381517)
          ·
            refine ⟨928976994912490835018069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2477271986433308893381517 928976994912490835018069)
            ·
              refine ⟨2721612289782687993217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 928976994912490835018069 2721612289782687993217)
              ·
                rfl

theorem cell22_214663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 10].length) (baseStart_214663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214663 prefixEnd_214663 := by exact prefixLift 214663
  have htrace : WordTrace (prefixWord ++ tailWord_214663) baseStart_214663 baseEnd_214663 := by
    simpa [prefixWord, tailWord_214663, baseEnd_214663] using wordTrace_append hprefix tailTrace_214663
  have hstable : (prefixWord ++ tailWord_214663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214663).length < 2 ^ (prefixWord ++ tailWord_214663).sum := by decide
  have hdescent : baseEnd_214663 < baseStart_214663 := by decide
  rcases family_descends (prefixWord ++ tailWord_214663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214680 : List Nat := [2, 1, 2, 4, 1, 3, 2, 7]
def baseStart_214680 : Nat := 118140960795 + 214680 * 2 ^ 59
def prefixEnd_214680 : Nat := 4983230072969 + 3 ^ 40 * 214680 * 2
def baseEnd_214680 : Nat := 8165483474616688682423

theorem tailTrace_214680 : CollatzResearch.WordTrace tailWord_214680 prefixEnd_214680 8165483474616688682423 := by
  unfold tailWord_214680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915011431129249635052747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5220015241505666180070329 3915011431129249635052747)
  ·
    refine ⟨5872517146693874452579121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915011431129249635052747 5872517146693874452579121)
    ·
      refine ⟨4404387860020405839434341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5872517146693874452579121 4404387860020405839434341)
      ·
        refine ⟨825822723753826094893939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4404387860020405839434341 825822723753826094893939)
        ·
          refine ⟨1238734085630739142340909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825822723753826094893939 1238734085630739142340909)
          ·
            refine ⟨464525282111527178377841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1238734085630739142340909 464525282111527178377841)
            ·
              refine ⟨348393961583645383783381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464525282111527178377841 348393961583645383783381)
              ·
                refine ⟨8165483474616688682423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 348393961583645383783381 8165483474616688682423)
                ·
                  rfl

theorem cell22_214680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_214680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214680 prefixEnd_214680 := by exact prefixLift 214680
  have htrace : WordTrace (prefixWord ++ tailWord_214680) baseStart_214680 baseEnd_214680 := by
    simpa [prefixWord, tailWord_214680, baseEnd_214680] using wordTrace_append hprefix tailTrace_214680
  have hstable : (prefixWord ++ tailWord_214680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214680).length < 2 ^ (prefixWord ++ tailWord_214680).sum := by decide
  have hdescent : baseEnd_214680 < baseStart_214680 := by decide
  rcases family_descends (prefixWord ++ tailWord_214680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214684 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_214684 : Nat := 118140960795 + 214684 * 2 ^ 59
def prefixEnd_214684 : Nat := 4983230072969 + 3 ^ 40 * 214684 * 2
def baseEnd_214684 : Nat := 73490720553295521041795

theorem tailTrace_214684 : CollatzResearch.WordTrace tailWord_214684 prefixEnd_214684 73490720553295521041795 := by
  unfold tailWord_214684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915084377122003976625553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5220112502829338635500737 3915084377122003976625553)
  ·
    refine ⟨2936313282841502982469165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3915084377122003976625553 2936313282841502982469165)
    ·
      refine ⟨1101117481065563618425937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2936313282841502982469165 1101117481065563618425937)
      ·
        refine ⟨825838110799172713819453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1101117481065563618425937 825838110799172713819453)
        ·
          refine ⟨309689291549689767682295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 825838110799172713819453 309689291549689767682295)
          ·
            refine ⟨464533937324534651523443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309689291549689767682295 464533937324534651523443)
            ·
              refine ⟨696800905986801977285165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464533937324534651523443 696800905986801977285165)
              ·
                refine ⟨261300339745050741481937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 696800905986801977285165 261300339745050741481937)
                ·
                  refine ⟨195975254808788056111453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261300339745050741481937 195975254808788056111453)
                  ·
                    refine ⟨73490720553295521041795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195975254808788056111453 73490720553295521041795)
                    ·
                      rfl

theorem cell22_214684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_214684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214684 prefixEnd_214684 := by exact prefixLift 214684
  have htrace : WordTrace (prefixWord ++ tailWord_214684) baseStart_214684 baseEnd_214684 := by
    simpa [prefixWord, tailWord_214684, baseEnd_214684] using wordTrace_append hprefix tailTrace_214684
  have hstable : (prefixWord ++ tailWord_214684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214684).length < 2 ^ (prefixWord ++ tailWord_214684).sum := by decide
  have hdescent : baseEnd_214684 < baseStart_214684 := by decide
  rcases family_descends (prefixWord ++ tailWord_214684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214723 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_214723 : Nat := 118140960795 + 214723 * 2 ^ 59
def prefixEnd_214723 : Nat := 4983230072969 + 3 ^ 40 * 214723 * 2
def baseEnd_214723 : Nat := 73504071050312419316675

theorem tailTrace_214723 : CollatzResearch.WordTrace tailWord_214723 prefixEnd_214723 73504071050312419316675 := by
  unfold tailWord_214723
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831591201102717613920823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5221060800735145075947215 7831591201102717613920823)
  ·
    refine ⟨11747386801654076420881235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7831591201102717613920823 11747386801654076420881235)
    ·
      refine ⟨17621080202481114631321853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11747386801654076420881235 17621080202481114631321853)
      ·
        refine ⟨6607905075930417986745695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17621080202481114631321853 6607905075930417986745695)
        ·
          refine ⟨9911857613895626980118543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607905075930417986745695 9911857613895626980118543)
          ·
            refine ⟨14867786420843440470177815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911857613895626980118543 14867786420843440470177815)
            ·
              refine ⟨22301679631265160705266723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14867786420843440470177815 22301679631265160705266723)
              ·
                refine ⟨33452519446897741057900085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22301679631265160705266723 33452519446897741057900085)
                ·
                  refine ⟨3136173698146663224178133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33452519446897741057900085 3136173698146663224178133)
                  ·
                    refine ⟨73504071050312419316675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3136173698146663224178133 73504071050312419316675)
                    ·
                      rfl

theorem cell22_214723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_214723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214723 prefixEnd_214723 := by exact prefixLift 214723
  have htrace : WordTrace (prefixWord ++ tailWord_214723) baseStart_214723 baseEnd_214723 := by
    simpa [prefixWord, tailWord_214723, baseEnd_214723] using wordTrace_append hprefix tailTrace_214723
  have hstable : (prefixWord ++ tailWord_214723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214723).length < 2 ^ (prefixWord ++ tailWord_214723).sum := by decide
  have hdescent : baseEnd_214723 < baseStart_214723 := by decide
  rcases family_descends (prefixWord ++ tailWord_214723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214770 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_214770 : Nat := 118140960795 + 214770 * 2 ^ 59
def prefixEnd_214770 : Nat := 4983230072969 + 3 ^ 40 * 214770 * 2
def baseEnd_214770 : Nat := 24506720036939987797177

theorem tailTrace_214770 : CollatzResearch.WordTrace tailWord_214770 prefixEnd_214770 24506720036939987797177 := by
  unfold tailWord_214770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958326357983111160220441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5222203621288296427254509 1958326357983111160220441)
  ·
    refine ⟨1468744768487333370165331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1958326357983111160220441 1468744768487333370165331)
    ·
      refine ⟨2203117152731000055247997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468744768487333370165331 2203117152731000055247997)
      ·
        refine ⟨826168932274125020717999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2203117152731000055247997 826168932274125020717999)
        ·
          refine ⟨1239253398411187531076999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826168932274125020717999 1239253398411187531076999)
          ·
            refine ⟨1858880097616781296615499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239253398411187531076999 1858880097616781296615499)
            ·
              refine ⟨2788320146425171944923249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858880097616781296615499 2788320146425171944923249)
              ·
                refine ⟨2091240109818878958692437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788320146425171944923249 2091240109818878958692437)
                ·
                  refine ⟨24506720036939987797177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2091240109818878958692437 24506720036939987797177)
                  ·
                    rfl

theorem cell22_214770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_214770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214770 prefixEnd_214770 := by exact prefixLift 214770
  have htrace : WordTrace (prefixWord ++ tailWord_214770) baseStart_214770 baseEnd_214770 := by
    simpa [prefixWord, tailWord_214770, baseEnd_214770] using wordTrace_append hprefix tailTrace_214770
  have hstable : (prefixWord ++ tailWord_214770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214770).length < 2 ^ (prefixWord ++ tailWord_214770).sum := by decide
  have hdescent : baseEnd_214770 < baseStart_214770 := by decide
  rcases family_descends (prefixWord ++ tailWord_214770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214785 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_214785 : Nat := 118140960795 + 214785 * 2 ^ 59
def prefixEnd_214785 : Nat := 4983230072969 + 3 ^ 40 * 214785 * 2
def baseEnd_214785 : Nat := 73525294917364924266485

theorem tailTrace_214785 : CollatzResearch.WordTrace tailWord_214785 prefixEnd_214785 73525294917364924266485 := by
  unfold tailWord_214785
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833852526878102202677809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5222568351252068135118539 7833852526878102202677809)
  ·
    refine ⟨5875389395158576652008357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7833852526878102202677809 5875389395158576652008357)
    ·
      refine ⟨1101635511592233122251567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5875389395158576652008357 1101635511592233122251567)
      ·
        refine ⟨1652453267388349683377351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101635511592233122251567 1652453267388349683377351)
        ·
          refine ⟨2478679901082524525066027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652453267388349683377351 2478679901082524525066027)
          ·
            refine ⟨3718019851623786787599041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478679901082524525066027 3718019851623786787599041)
            ·
              refine ⟨2788514888717840090699281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718019851623786787599041 2788514888717840090699281)
              ·
                refine ⟨2091386166538380068024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788514888717840090699281 2091386166538380068024461)
                ·
                  refine ⟨784269812451892525509173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2091386166538380068024461 784269812451892525509173)
                  ·
                    refine ⟨73525294917364924266485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 784269812451892525509173 73525294917364924266485)
                    ·
                      rfl

theorem cell22_214785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_214785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214785 prefixEnd_214785 := by exact prefixLift 214785
  have htrace : WordTrace (prefixWord ++ tailWord_214785) baseStart_214785 baseEnd_214785 := by
    simpa [prefixWord, tailWord_214785, baseEnd_214785] using wordTrace_append hprefix tailTrace_214785
  have hstable : (prefixWord ++ tailWord_214785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214785).length < 2 ^ (prefixWord ++ tailWord_214785).sum := by decide
  have hdescent : baseEnd_214785 < baseStart_214785 := by decide
  rcases family_descends (prefixWord ++ tailWord_214785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214787 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 4]
def baseStart_214787 : Nat := 118140960795 + 214787 * 2 ^ 59
def prefixEnd_214787 : Nat := 4983230072969 + 3 ^ 40 * 214787 * 2
def baseEnd_214787 : Nat := 24508659852745861905493

theorem tailTrace_214787 : CollatzResearch.WordTrace tailWord_214787 prefixEnd_214787 24508659852745861905493 := by
  unfold tailWord_214787
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833925472870856544250615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5222616981913904362833743 7833925472870856544250615)
  ·
    refine ⟨11750888209306284816375923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833925472870856544250615 11750888209306284816375923)
    ·
      refine ⟨17626332313959427224563885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11750888209306284816375923 17626332313959427224563885)
      ·
        refine ⟨6609874617734785209211457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17626332313959427224563885 6609874617734785209211457)
        ·
          refine ⟨4957405963301088906908593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6609874617734785209211457 4957405963301088906908593)
          ·
            refine ⟨3718054472475816680181445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4957405963301088906908593 3718054472475816680181445)
            ·
              refine ⟨697135213589215627534021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3718054472475816680181445 697135213589215627534021)
              ·
                refine ⟨130712852547977930162629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697135213589215627534021 130712852547977930162629)
                ·
                  refine ⟨24508659852745861905493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130712852547977930162629 24508659852745861905493)
                  ·
                    rfl

theorem cell22_214787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 4].length) (baseStart_214787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214787 prefixEnd_214787 := by exact prefixLift 214787
  have htrace : WordTrace (prefixWord ++ tailWord_214787) baseStart_214787 baseEnd_214787 := by
    simpa [prefixWord, tailWord_214787, baseEnd_214787] using wordTrace_append hprefix tailTrace_214787
  have hstable : (prefixWord ++ tailWord_214787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214787).length < 2 ^ (prefixWord ++ tailWord_214787).sum := by decide
  have hdescent : baseEnd_214787 < baseStart_214787 := by decide
  rcases family_descends (prefixWord ++ tailWord_214787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214815 : List Nat := [1, 1, 2, 4, 2, 1, 3, 8]
def baseStart_214815 : Nat := 118140960795 + 214815 * 2 ^ 59
def prefixEnd_214815 : Nat := 4983230072969 + 3 ^ 40 * 214815 * 2
def baseEnd_214815 : Nat := 8170618281161649557377

theorem tailTrace_214815 : CollatzResearch.WordTrace tailWord_214815 prefixEnd_214815 8170618281161649557377 := by
  unfold tailWord_214815
  simp only [CollatzResearch.WordTrace]
  refine ⟨7834946716769417326269899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5223297811179611550846599 7834946716769417326269899)
  ·
    refine ⟨11752420075154125989404849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7834946716769417326269899 11752420075154125989404849)
    ·
      refine ⟨8814315056365594492053637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11752420075154125989404849 8814315056365594492053637)
      ·
        refine ⟨1652684073068548967260057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8814315056365594492053637 1652684073068548967260057)
        ·
          refine ⟨1239513054801411725445043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652684073068548967260057 1239513054801411725445043)
          ·
            refine ⟨1859269582202117588167565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239513054801411725445043 1859269582202117588167565)
            ·
              refine ⟨697226093325794095562837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859269582202117588167565 697226093325794095562837)
              ·
                refine ⟨8170618281161649557377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 697226093325794095562837 8170618281161649557377)
                ·
                  rfl

theorem cell22_214815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 8].length) (baseStart_214815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214815 prefixEnd_214815 := by exact prefixLift 214815
  have htrace : WordTrace (prefixWord ++ tailWord_214815) baseStart_214815 baseEnd_214815 := by
    simpa [prefixWord, tailWord_214815, baseEnd_214815] using wordTrace_append hprefix tailTrace_214815
  have hstable : (prefixWord ++ tailWord_214815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214815).length < 2 ^ (prefixWord ++ tailWord_214815).sum := by decide
  have hdescent : baseEnd_214815 < baseStart_214815 := by decide
  rcases family_descends (prefixWord ++ tailWord_214815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214838 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_214838 : Nat := 118140960795 + 214838 * 2 ^ 59
def prefixEnd_214838 : Nat := 4983230072969 + 3 ^ 40 * 214838 * 2
def baseEnd_214838 : Nat := 24514479300163484230441

theorem tailTrace_214838 : CollatzResearch.WordTrace tailWord_214838 prefixEnd_214838 24514479300163484230441 := by
  unfold tailWord_214838
  simp only [CollatzResearch.WordTrace]
  refine ⟨489736599730380765897323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5223857063790728169571445 489736599730380765897323)
  ·
    refine ⟨734604899595571148845985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 489736599730380765897323 734604899595571148845985)
    ·
      refine ⟨550953674696678361634489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 734604899595571148845985 550953674696678361634489)
      ·
        refine ⟨413215256022508771225867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550953674696678361634489 413215256022508771225867)
        ·
          refine ⟨619822884033763156838801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413215256022508771225867 619822884033763156838801)
          ·
            refine ⟨464867163025322367629101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619822884033763156838801 464867163025322367629101)
            ·
              refine ⟨174325186134495887860913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464867163025322367629101 174325186134495887860913)
              ·
                refine ⟨130743889600871915895685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174325186134495887860913 130743889600871915895685)
                ·
                  refine ⟨24514479300163484230441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130743889600871915895685 24514479300163484230441)
                  ·
                    rfl

theorem cell22_214838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_214838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214838 prefixEnd_214838 := by exact prefixLift 214838
  have htrace : WordTrace (prefixWord ++ tailWord_214838) baseStart_214838 baseEnd_214838 := by
    simpa [prefixWord, tailWord_214838, baseEnd_214838] using wordTrace_append hprefix tailTrace_214838
  have hstable : (prefixWord ++ tailWord_214838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214838).length < 2 ^ (prefixWord ++ tailWord_214838).sum := by decide
  have hdescent : baseEnd_214838 < baseStart_214838 := by decide
  rcases family_descends (prefixWord ++ tailWord_214838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214894 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_214894 : Nat := 118140960795 + 214894 * 2 ^ 59
def prefixEnd_214894 : Nat := 4983230072969 + 3 ^ 40 * 214894 * 2
def baseEnd_214894 : Nat := 24520869281641657763717

theorem tailTrace_214894 : CollatzResearch.WordTrace tailWord_214894 prefixEnd_214894 24520869281641657763717 := by
  unfold tailWord_214894
  simp only [CollatzResearch.WordTrace]
  refine ⟨979728510435401727299467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5225218722322142545597157 979728510435401727299467)
  ·
    refine ⟨1469592765653102590949201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 979728510435401727299467 1469592765653102590949201)
    ·
      refine ⟨1102194574239826943211901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1469592765653102590949201 1102194574239826943211901)
      ·
        refine ⟨413322965339935103704463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1102194574239826943211901 413322965339935103704463)
        ·
          refine ⟨619984448009902655556695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413322965339935103704463 619984448009902655556695)
          ·
            refine ⟨929976672014853983335043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619984448009902655556695 929976672014853983335043)
            ·
              refine ⟨1394965008022280975002565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929976672014853983335043 1394965008022280975002565)
              ·
                refine ⟨261555939004177682812981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1394965008022280975002565 261555939004177682812981)
                ·
                  refine ⟨24520869281641657763717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261555939004177682812981 24520869281641657763717)
                  ·
                    rfl

theorem cell22_214894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_214894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214894 prefixEnd_214894 := by exact prefixLift 214894
  have htrace : WordTrace (prefixWord ++ tailWord_214894) baseStart_214894 baseEnd_214894 := by
    simpa [prefixWord, tailWord_214894, baseEnd_214894] using wordTrace_append hprefix tailTrace_214894
  have hstable : (prefixWord ++ tailWord_214894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214894).length < 2 ^ (prefixWord ++ tailWord_214894).sum := by decide
  have hdescent : baseEnd_214894 < baseStart_214894 := by decide
  rcases family_descends (prefixWord ++ tailWord_214894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214937 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_214937 : Nat := 118140960795 + 214937 * 2 ^ 59
def prefixEnd_214937 : Nat := 4983230072969 + 3 ^ 40 * 214937 * 2
def baseEnd_214937 : Nat := 73577327623687194466019

theorem tailTrace_214937 : CollatzResearch.WordTrace tailWord_214937 prefixEnd_214937 73577327623687194466019 := by
  unfold tailWord_214937
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839396422327432162211065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5226264281551621441474043 7839396422327432162211065)
  ·
    refine ⟨5879547316745574121658299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7839396422327432162211065 5879547316745574121658299)
    ·
      refine ⟨8819320975118361182487449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5879547316745574121658299 8819320975118361182487449)
      ·
        refine ⟨6614490731338770886865587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8819320975118361182487449 6614490731338770886865587)
        ·
          refine ⟨9921736097008156330298381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614490731338770886865587 9921736097008156330298381)
          ·
            refine ⟨3720651036378058623861893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9921736097008156330298381 3720651036378058623861893)
            ·
              refine ⟨697622069320885991974105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3720651036378058623861893 697622069320885991974105)
              ·
                refine ⟨523216551990664493980579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697622069320885991974105 523216551990664493980579)
                ·
                  refine ⟨784824827985996740970869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523216551990664493980579 784824827985996740970869)
                  ·
                    refine ⟨73577327623687194466019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 784824827985996740970869 73577327623687194466019)
                    ·
                      rfl

theorem cell22_214937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_214937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214937 prefixEnd_214937 := by exact prefixLift 214937
  have htrace : WordTrace (prefixWord ++ tailWord_214937) baseStart_214937 baseEnd_214937 := by
    simpa [prefixWord, tailWord_214937, baseEnd_214937] using wordTrace_append hprefix tailTrace_214937
  have hstable : (prefixWord ++ tailWord_214937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214937).length < 2 ^ (prefixWord ++ tailWord_214937).sum := by decide
  have hdescent : baseEnd_214937 < baseStart_214937 := by decide
  rcases family_descends (prefixWord ++ tailWord_214937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214941 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_214941 : Nat := 118140960795 + 214941 * 2 ^ 59
def prefixEnd_214941 : Nat := 4983230072969 + 3 ^ 40 * 214941 * 2
def baseEnd_214941 : Nat := 73578696905432517366007

theorem tailTrace_214941 : CollatzResearch.WordTrace tailWord_214941 prefixEnd_214941 73578696905432517366007 := by
  unfold tailWord_214941
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839542314312940845356677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5226361542875293896904451 7839542314312940845356677)
  ·
    refine ⟨1469914183933676408504377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7839542314312940845356677 1469914183933676408504377)
    ·
      refine ⟨1102435637950257306378283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1469914183933676408504377 1102435637950257306378283)
      ·
        refine ⟨1653653456925385959567425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102435637950257306378283 1653653456925385959567425)
        ·
          refine ⟨1240240092694039469675569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1653653456925385959567425 1240240092694039469675569)
          ·
            refine ⟨930180069520529602256677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240240092694039469675569 930180069520529602256677)
            ·
              refine ⟨174408763035099300423127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 930180069520529602256677 174408763035099300423127)
              ·
                refine ⟨261613144552648950634691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174408763035099300423127 261613144552648950634691)
                ·
                  refine ⟨392419716828973425952037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261613144552648950634691 392419716828973425952037)
                  ·
                    refine ⟨73578696905432517366007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392419716828973425952037 73578696905432517366007)
                    ·
                      rfl

theorem cell22_214941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_214941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214941 prefixEnd_214941 := by exact prefixLift 214941
  have htrace : WordTrace (prefixWord ++ tailWord_214941) baseStart_214941 baseEnd_214941 := by
    simpa [prefixWord, tailWord_214941, baseEnd_214941] using wordTrace_append hprefix tailTrace_214941
  have hstable : (prefixWord ++ tailWord_214941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214941).length < 2 ^ (prefixWord ++ tailWord_214941).sum := by decide
  have hdescent : baseEnd_214941 < baseStart_214941 := by decide
  rcases family_descends (prefixWord ++ tailWord_214941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214984 : List Nat := [2, 1, 3, 1, 4, 1, 4, 6]
def baseStart_214984 : Nat := 118140960795 + 214984 * 2 ^ 59
def prefixEnd_214984 : Nat := 4983230072969 + 3 ^ 40 * 214984 * 2
def baseEnd_214984 : Nat := 8177046298243859837875

theorem tailTrace_214984 : CollatzResearch.WordTrace tailWord_214984 prefixEnd_214984 8177046298243859837875 := by
  unfold tailWord_214984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920555326578579594586003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5227407102104772792781337 3920555326578579594586003)
  ·
    refine ⟨5880832989867869391879005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3920555326578579594586003 5880832989867869391879005)
    ·
      refine ⟨2205312371200451021954627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5880832989867869391879005 2205312371200451021954627)
      ·
        refine ⟨3307968556800676532931941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205312371200451021954627 3307968556800676532931941)
        ·
          refine ⟨620244104400126849924739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3307968556800676532931941 620244104400126849924739)
          ·
            refine ⟨930366156600190274887109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620244104400126849924739 930366156600190274887109)
            ·
              refine ⟨174443654362535676541333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 930366156600190274887109 174443654362535676541333)
              ·
                refine ⟨8177046298243859837875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174443654362535676541333 8177046298243859837875)
                ·
                  rfl

theorem cell22_214984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_214984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_214984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_214984 prefixEnd_214984 := by exact prefixLift 214984
  have htrace : WordTrace (prefixWord ++ tailWord_214984) baseStart_214984 baseEnd_214984 := by
    simpa [prefixWord, tailWord_214984, baseEnd_214984] using wordTrace_append hprefix tailTrace_214984
  have hstable : (prefixWord ++ tailWord_214984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214984).length < 2 ^ (prefixWord ++ tailWord_214984).sum := by decide
  have hdescent : baseEnd_214984 < baseStart_214984 := by decide
  rcases family_descends (prefixWord ++ tailWord_214984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215012 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_215012 : Nat := 118140960795 + 215012 * 2 ^ 59
def prefixEnd_215012 : Nat := 4983230072969 + 3 ^ 40 * 215012 * 2
def baseEnd_215012 : Nat := 24534333885470666280263

theorem tailTrace_215012 : CollatzResearch.WordTrace tailWord_215012 prefixEnd_215012 24534333885470666280263 := by
  unfold tailWord_215012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921065948527859985595645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5228087931370479980794193 3921065948527859985595645)
  ·
    refine ⟨1470399730697947494598367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3921065948527859985595645 1470399730697947494598367)
    ·
      refine ⟨2205599596046921241897551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470399730697947494598367 2205599596046921241897551)
      ·
        refine ⟨3308399394070381862846327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205599596046921241897551 3308399394070381862846327)
        ·
          refine ⟨4962599091105572794269491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308399394070381862846327 4962599091105572794269491)
          ·
            refine ⟨7443898636658359191404237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962599091105572794269491 7443898636658359191404237)
            ·
              refine ⟨2791461988746884696776589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7443898636658359191404237 2791461988746884696776589)
              ·
                refine ⟨1046798245780081761291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791461988746884696776589 1046798245780081761291221)
                ·
                  refine ⟨24534333885470666280263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1046798245780081761291221 24534333885470666280263)
                  ·
                    rfl

theorem cell22_215012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_215012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215012 prefixEnd_215012 := by exact prefixLift 215012
  have htrace : WordTrace (prefixWord ++ tailWord_215012) baseStart_215012 baseEnd_215012 := by
    simpa [prefixWord, tailWord_215012, baseEnd_215012] using wordTrace_append hprefix tailTrace_215012
  have hstable : (prefixWord ++ tailWord_215012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215012).length < 2 ^ (prefixWord ++ tailWord_215012).sum := by decide
  have hdescent : baseEnd_215012 < baseStart_215012 := by decide
  rcases family_descends (prefixWord ++ tailWord_215012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215027 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_215027 : Nat := 118140960795 + 215027 * 2 ^ 59
def prefixEnd_215027 : Nat := 4983230072969 + 3 ^ 40 * 215027 * 2
def baseEnd_215027 : Nat := 73608136462956959715743

theorem tailTrace_215027 : CollatzResearch.WordTrace tailWord_215027 prefixEnd_215027 73608136462956959715743 := by
  unfold tailWord_215027
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842678992001377532987335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5228452661334251688658223 7842678992001377532987335)
  ·
    refine ⟨11764018488002066299481003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842678992001377532987335 11764018488002066299481003)
    ·
      refine ⟨17646027732003099449221505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11764018488002066299481003 17646027732003099449221505)
      ·
        refine ⟨13234520799002324586916129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17646027732003099449221505 13234520799002324586916129)
        ·
          refine ⟨9925890599251743440187097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13234520799002324586916129 9925890599251743440187097)
          ·
            refine ⟨7444417949438807580140323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9925890599251743440187097 7444417949438807580140323)
            ·
              refine ⟨11166626924158211370210485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444417949438807580140323 11166626924158211370210485)
              ·
                refine ⟨1046871274139832315957233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11166626924158211370210485 1046871274139832315957233)
                ·
                  refine ⟨785153455604874236967925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046871274139832315957233 785153455604874236967925)
                  ·
                    refine ⟨73608136462956959715743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 785153455604874236967925 73608136462956959715743)
                    ·
                      rfl

theorem cell22_215027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_215027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215027 prefixEnd_215027 := by exact prefixLift 215027
  have htrace : WordTrace (prefixWord ++ tailWord_215027) baseStart_215027 baseEnd_215027 := by
    simpa [prefixWord, tailWord_215027, baseEnd_215027] using wordTrace_append hprefix tailTrace_215027
  have hstable : (prefixWord ++ tailWord_215027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215027).length < 2 ^ (prefixWord ++ tailWord_215027).sum := by decide
  have hdescent : baseEnd_215027 < baseStart_215027 := by decide
  rcases family_descends (prefixWord ++ tailWord_215027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215059 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 1, 4]
def baseStart_215059 : Nat := 118140960795 + 215059 * 2 ^ 59
def prefixEnd_215059 : Nat := 4983230072969 + 3 ^ 40 * 215059 * 2
def baseEnd_215059 : Nat := 73619090716919542915645

theorem tailTrace_215059 : CollatzResearch.WordTrace tailWord_215059 prefixEnd_215059 73619090716919542915645 := by
  unfold tailWord_215059
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843846127885446998152231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5229230751923631332101487 7843846127885446998152231)
  ·
    refine ⟨11765769191828170497228347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7843846127885446998152231 11765769191828170497228347)
    ·
      refine ⟨17648653787742255745842521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11765769191828170497228347 17648653787742255745842521)
      ·
        refine ⟨13236490340806691809381891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17648653787742255745842521 13236490340806691809381891)
        ·
          refine ⟨19854735511210037714072837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13236490340806691809381891 19854735511210037714072837)
          ·
            refine ⟨3722762908351882071388657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19854735511210037714072837 3722762908351882071388657)
            ·
              refine ⟨2792072181263911553541493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722762908351882071388657 2792072181263911553541493)
              ·
                refine ⟨261756766993491708144515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2792072181263911553541493 261756766993491708144515)
                ·
                  refine ⟨392635150490237562216773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261756766993491708144515 392635150490237562216773)
                  ·
                    refine ⟨73619090716919542915645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392635150490237562216773 73619090716919542915645)
                    ·
                      rfl

theorem cell22_215059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 4].length) (baseStart_215059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215059 prefixEnd_215059 := by exact prefixLift 215059
  have htrace : WordTrace (prefixWord ++ tailWord_215059) baseStart_215059 baseEnd_215059 := by
    simpa [prefixWord, tailWord_215059, baseEnd_215059] using wordTrace_append hprefix tailTrace_215059
  have hstable : (prefixWord ++ tailWord_215059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215059).length < 2 ^ (prefixWord ++ tailWord_215059).sum := by decide
  have hdescent : baseEnd_215059 < baseStart_215059 := by decide
  rcases family_descends (prefixWord ++ tailWord_215059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215074 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_215074 : Nat := 118140960795 + 215074 * 2 ^ 59
def prefixEnd_215074 : Nat := 4983230072969 + 3 ^ 40 * 215074 * 2
def baseEnd_215074 : Nat := 24541408507821501263533

theorem tailTrace_215074 : CollatzResearch.WordTrace tailWord_215074 prefixEnd_215074 24541408507821501263533 := by
  unfold tailWord_215074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961098305707776139987069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5229595481887403039965517 1961098305707776139987069)
  ·
    refine ⟨735411864640416052495151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1961098305707776139987069 735411864640416052495151)
    ·
      refine ⟨1103117796960624078742727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735411864640416052495151 1103117796960624078742727)
      ·
        refine ⟨1654676695440936118114091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103117796960624078742727 1654676695440936118114091)
        ·
          refine ⟨2482015043161404177171137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654676695440936118114091 2482015043161404177171137)
          ·
            refine ⟨1861511282371053132878353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2482015043161404177171137 1861511282371053132878353)
            ·
              refine ⟨1396133461778289849658765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861511282371053132878353 1396133461778289849658765)
              ·
                refine ⟨523550048166858693622037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1396133461778289849658765 523550048166858693622037)
                ·
                  refine ⟨24541408507821501263533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 523550048166858693622037 24541408507821501263533)
                  ·
                    rfl

theorem cell22_215074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_215074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215074 prefixEnd_215074 := by exact prefixLift 215074
  have htrace : WordTrace (prefixWord ++ tailWord_215074) baseStart_215074 baseEnd_215074 := by
    simpa [prefixWord, tailWord_215074, baseEnd_215074] using wordTrace_append hprefix tailTrace_215074
  have hstable : (prefixWord ++ tailWord_215074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215074).length < 2 ^ (prefixWord ++ tailWord_215074).sum := by decide
  have hdescent : baseEnd_215074 < baseStart_215074 := by decide
  rcases family_descends (prefixWord ++ tailWord_215074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215089 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_215089 : Nat := 118140960795 + 215089 * 2 ^ 59
def prefixEnd_215089 : Nat := 4983230072969 + 3 ^ 40 * 215089 * 2
def baseEnd_215089 : Nat := 73629360330009464665553

theorem tailTrace_215089 : CollatzResearch.WordTrace tailWord_215089 prefixEnd_215089 73629360330009464665553 := by
  unfold tailWord_215089
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844940317776762121744321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5229960211851174747829547 7844940317776762121744321)
  ·
    refine ⟨5883705238332571591308241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7844940317776762121744321 5883705238332571591308241)
    ·
      refine ⟨4412778928749428693481181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5883705238332571591308241 4412778928749428693481181)
      ·
        refine ⟨1654792098281035760055443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4412778928749428693481181 1654792098281035760055443)
        ·
          refine ⟨2482188147421553640083165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654792098281035760055443 2482188147421553640083165)
          ·
            refine ⟨930820555283082615031187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2482188147421553640083165 930820555283082615031187)
            ·
              refine ⟨1396230832924623922546781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930820555283082615031187 1396230832924623922546781)
              ·
                refine ⟨523586562346733970955043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1396230832924623922546781 523586562346733970955043)
                ·
                  refine ⟨785379843520100956432565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523586562346733970955043 785379843520100956432565)
                  ·
                    refine ⟨73629360330009464665553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 785379843520100956432565 73629360330009464665553)
                    ·
                      rfl

theorem cell22_215089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_215089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215089 prefixEnd_215089 := by exact prefixLift 215089
  have htrace : WordTrace (prefixWord ++ tailWord_215089) baseStart_215089 baseEnd_215089 := by
    simpa [prefixWord, tailWord_215089, baseEnd_215089] using wordTrace_append hprefix tailTrace_215089
  have hstable : (prefixWord ++ tailWord_215089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215089).length < 2 ^ (prefixWord ++ tailWord_215089).sum := by decide
  have hdescent : baseEnd_215089 < baseStart_215089 := by decide
  rcases family_descends (prefixWord ++ tailWord_215089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215104 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_215104 : Nat := 118140960795 + 215104 * 2 ^ 59
def prefixEnd_215104 : Nat := 4983230072969 + 3 ^ 40 * 215104 * 2
def baseEnd_215104 : Nat := 73634495136554425540507

theorem tailTrace_215104 : CollatzResearch.WordTrace tailWord_215104 prefixEnd_215104 73634495136554425540507 := by
  unfold tailWord_215104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922743706361209841770183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5230324941814946455693577 3922743706361209841770183)
  ·
    refine ⟨5884115559541814762655275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3922743706361209841770183 5884115559541814762655275)
    ·
      refine ⟨8826173339312722143982913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884115559541814762655275 8826173339312722143982913)
      ·
        refine ⟨6619630004484541607987185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8826173339312722143982913 6619630004484541607987185)
        ·
          refine ⟨4964722503363406205990389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6619630004484541607987185 4964722503363406205990389)
          ·
            refine ⟨465442734690319331811599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4964722503363406205990389 465442734690319331811599)
            ·
              refine ⟨698164102035478997717399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465442734690319331811599 698164102035478997717399)
              ·
                refine ⟨1047246153053218496576099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698164102035478997717399 1047246153053218496576099)
                ·
                  refine ⟨1570869229579827744864149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047246153053218496576099 1570869229579827744864149)
                  ·
                    refine ⟨73634495136554425540507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1570869229579827744864149 73634495136554425540507)
                    ·
                      rfl

theorem cell22_215104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_215104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215104 prefixEnd_215104 := by exact prefixLift 215104
  have htrace : WordTrace (prefixWord ++ tailWord_215104) baseStart_215104 baseEnd_215104 := by
    simpa [prefixWord, tailWord_215104, baseEnd_215104] using wordTrace_append hprefix tailTrace_215104
  have hstable : (prefixWord ++ tailWord_215104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215104).length < 2 ^ (prefixWord ++ tailWord_215104).sum := by decide
  have hdescent : baseEnd_215104 < baseStart_215104 := by decide
  rcases family_descends (prefixWord ++ tailWord_215104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215151 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 3, 3]
def baseStart_215151 : Nat := 118140960795 + 215151 * 2 ^ 59
def prefixEnd_215151 : Nat := 4983230072969 + 3 ^ 40 * 215151 * 2
def baseEnd_215151 : Nat := 73650584197061969615363

theorem tailTrace_215151 : CollatzResearch.WordTrace tailWord_215151 prefixEnd_215151 73650584197061969615363 := by
  unfold tailWord_215151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847201643552146710501307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5231467762368097807000871 7847201643552146710501307)
  ·
    refine ⟨11770802465328220065751961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7847201643552146710501307 11770802465328220065751961)
    ·
      refine ⟨8828101848996165049313971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11770802465328220065751961 8828101848996165049313971)
      ·
        refine ⟨13242152773494247573970957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8828101848996165049313971 13242152773494247573970957)
        ·
          refine ⟨4965807290060342840239109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13242152773494247573970957 4965807290060342840239109)
          ·
            refine ⟨931088866886314282544833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4965807290060342840239109 931088866886314282544833)
            ·
              refine ⟨698316650164735711908625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931088866886314282544833 698316650164735711908625)
              ·
                refine ⟨523737487623551783931469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698316650164735711908625 523737487623551783931469)
                ·
                  refine ⟨196401557858831918974301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523737487623551783931469 196401557858831918974301)
                  ·
                    refine ⟨73650584197061969615363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196401557858831918974301 73650584197061969615363)
                    ·
                      rfl

theorem cell22_215151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_215151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215151 prefixEnd_215151 := by exact prefixLift 215151
  have htrace : WordTrace (prefixWord ++ tailWord_215151) baseStart_215151 baseEnd_215151 := by
    simpa [prefixWord, tailWord_215151, baseEnd_215151] using wordTrace_append hprefix tailTrace_215151
  have hstable : (prefixWord ++ tailWord_215151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215151).length < 2 ^ (prefixWord ++ tailWord_215151).sum := by decide
  have hdescent : baseEnd_215151 < baseStart_215151 := by decide
  rcases family_descends (prefixWord ++ tailWord_215151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215164 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_215164 : Nat := 118140960795 + 215164 * 2 ^ 59
def prefixEnd_215164 : Nat := 4983230072969 + 3 ^ 40 * 215164 * 2
def baseEnd_215164 : Nat := 24551678120911423013441

theorem tailTrace_215164 : CollatzResearch.WordTrace tailWord_215164 prefixEnd_215164 24551678120911423013441 := by
  unfold tailWord_215164
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923837896252524965362273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5231783861670033287149697 3923837896252524965362273)
  ·
    refine ⟨2942878422189393724021705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3923837896252524965362273 2942878422189393724021705)
    ·
      refine ⟨2207158816642045293016279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942878422189393724021705 2207158816642045293016279)
      ·
        refine ⟨3310738224963067939524419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207158816642045293016279 3310738224963067939524419)
        ·
          refine ⟨4966107337444601909286629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310738224963067939524419 4966107337444601909286629)
          ·
            refine ⟨931145125770862857991243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4966107337444601909286629 931145125770862857991243)
            ·
              refine ⟨1396717688656294286986865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931145125770862857991243 1396717688656294286986865)
              ·
                refine ⟨1047538266492220715240149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396717688656294286986865 1047538266492220715240149)
                ·
                  refine ⟨24551678120911423013441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1047538266492220715240149 24551678120911423013441)
                  ·
                    rfl

theorem cell22_215164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_215164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215164 prefixEnd_215164 := by exact prefixLift 215164
  have htrace : WordTrace (prefixWord ++ tailWord_215164) baseStart_215164 baseEnd_215164 := by
    simpa [prefixWord, tailWord_215164, baseEnd_215164] using wordTrace_append hprefix tailTrace_215164
  have hstable : (prefixWord ++ tailWord_215164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215164).length < 2 ^ (prefixWord ++ tailWord_215164).sum := by decide
  have hdescent : baseEnd_215164 < baseStart_215164 := by decide
  rcases family_descends (prefixWord ++ tailWord_215164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215239 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_215239 : Nat := 118140960795 + 215239 * 2 ^ 59
def prefixEnd_215239 : Nat := 4983230072969 + 3 ^ 40 * 215239 * 2
def baseEnd_215239 : Nat := 73680708395459073415093

theorem tailTrace_215239 : CollatzResearch.WordTrace tailWord_215239 prefixEnd_215239 73680708395459073415093 := by
  unfold tailWord_215239
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850411267233337739704771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5233607511488891826469847 7850411267233337739704771)
  ·
    refine ⟨11775616900850006609557157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850411267233337739704771 11775616900850006609557157)
    ·
      refine ⟨2207928168909376239291967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11775616900850006609557157 2207928168909376239291967)
      ·
        refine ⟨3311892253364064358937951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207928168909376239291967 3311892253364064358937951)
        ·
          refine ⟨4967838380046096538406927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311892253364064358937951 4967838380046096538406927)
          ·
            refine ⟨7451757570069144807610391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967838380046096538406927 7451757570069144807610391)
            ·
              refine ⟨11177636355103717211415587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451757570069144807610391 11177636355103717211415587)
              ·
                refine ⟨16766454532655575817123381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11177636355103717211415587 16766454532655575817123381)
                ·
                  refine ⟨1571855112436460232855317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16766454532655575817123381 1571855112436460232855317)
                  ·
                    refine ⟨73680708395459073415093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1571855112436460232855317 73680708395459073415093)
                    ·
                      rfl

theorem cell22_215239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_215239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215239 prefixEnd_215239 := by exact prefixLift 215239
  have htrace : WordTrace (prefixWord ++ tailWord_215239) baseStart_215239 baseEnd_215239 := by
    simpa [prefixWord, tailWord_215239, baseEnd_215239] using wordTrace_append hprefix tailTrace_215239
  have hstable : (prefixWord ++ tailWord_215239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215239).length < 2 ^ (prefixWord ++ tailWord_215239).sum := by decide
  have hdescent : baseEnd_215239 < baseStart_215239 := by decide
  rcases family_descends (prefixWord ++ tailWord_215239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215258 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_215258 : Nat := 118140960795 + 215258 * 2 ^ 59
def prefixEnd_215258 : Nat := 4983230072969 + 3 ^ 40 * 215258 * 2
def baseEnd_215258 : Nat := 73687212483749357190035

theorem tailTrace_215258 : CollatzResearch.WordTrace tailWord_215258 prefixEnd_215258 73687212483749357190035 := by
  unfold tailWord_215258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962776063541125996161607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5234069502776335989764285 1962776063541125996161607)
  ·
    refine ⟨2944164095311688994242411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962776063541125996161607 2944164095311688994242411)
    ·
      refine ⟨4416246142967533491363617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944164095311688994242411 4416246142967533491363617)
      ·
        refine ⟨3312184607225650118522713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4416246142967533491363617 3312184607225650118522713)
        ·
          refine ⟨2484138455419237588892035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3312184607225650118522713 2484138455419237588892035)
          ·
            refine ⟨3726207683128856383338053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484138455419237588892035 3726207683128856383338053)
            ·
              refine ⟨698663940586660571875885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3726207683128856383338053 698663940586660571875885)
              ·
                refine ⟨261998977719997714453457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698663940586660571875885 261998977719997714453457)
                ·
                  refine ⟨196499233289998285840093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261998977719997714453457 196499233289998285840093)
                  ·
                    refine ⟨73687212483749357190035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196499233289998285840093 73687212483749357190035)
                    ·
                      rfl

theorem cell22_215258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_215258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215258 prefixEnd_215258 := by exact prefixLift 215258
  have htrace : WordTrace (prefixWord ++ tailWord_215258) baseStart_215258 baseEnd_215258 := by
    simpa [prefixWord, tailWord_215258, baseEnd_215258] using wordTrace_append hprefix tailTrace_215258
  have hstable : (prefixWord ++ tailWord_215258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215258).length < 2 ^ (prefixWord ++ tailWord_215258).sum := by decide
  have hdescent : baseEnd_215258 < baseStart_215258 := by decide
  rcases family_descends (prefixWord ++ tailWord_215258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215260 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 6]
def baseStart_215260 : Nat := 118140960795 + 215260 * 2 ^ 59
def prefixEnd_215260 : Nat := 4983230072969 + 3 ^ 40 * 215260 * 2
def baseEnd_215260 : Nat := 24562632374874006213343

theorem tailTrace_215260 : CollatzResearch.WordTrace tailWord_215260 prefixEnd_215260 24562632374874006213343 := by
  unfold tailWord_215260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925588600078629163109617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5234118133438172217479489 3925588600078629163109617)
  ·
    refine ⟨2944191450058971872332213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3925588600078629163109617 2944191450058971872332213)
    ·
      refine ⟨276017948443028613031145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2944191450058971872332213 276017948443028613031145)
      ·
        refine ⟨207013461332271459773359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276017948443028613031145 207013461332271459773359)
        ·
          refine ⟨310520191998407189660039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207013461332271459773359 310520191998407189660039)
          ·
            refine ⟨465780287997610784490059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310520191998407189660039 465780287997610784490059)
            ·
              refine ⟨698670431996416176735089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465780287997610784490059 698670431996416176735089)
              ·
                refine ⟨524002823997312132551317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698670431996416176735089 524002823997312132551317)
                ·
                  refine ⟨24562632374874006213343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 524002823997312132551317 24562632374874006213343)
                  ·
                    rfl

theorem cell22_215260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_215260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215260 prefixEnd_215260 := by exact prefixLift 215260
  have htrace : WordTrace (prefixWord ++ tailWord_215260) baseStart_215260 baseEnd_215260 := by
    simpa [prefixWord, tailWord_215260, baseEnd_215260] using wordTrace_append hprefix tailTrace_215260
  have hstable : (prefixWord ++ tailWord_215260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215260).length < 2 ^ (prefixWord ++ tailWord_215260).sum := by decide
  have hdescent : baseEnd_215260 < baseStart_215260 := by decide
  rcases family_descends (prefixWord ++ tailWord_215260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215380 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_215380 : Nat := 118140960795 + 215380 * 2 ^ 59
def prefixEnd_215380 : Nat := 4983230072969 + 3 ^ 40 * 215380 * 2
def baseEnd_215380 : Nat := 73728975576981705639661

theorem tailTrace_215380 : CollatzResearch.WordTrace tailWord_215380 prefixEnd_215380 73728975576981705639661 := by
  unfold tailWord_215380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927776979861259410293797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5237035973148345880391729 3927776979861259410293797)
  ·
    refine ⟨736458183723986139430087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3927776979861259410293797 736458183723986139430087)
    ·
      refine ⟨1104687275585979209145131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736458183723986139430087 1104687275585979209145131)
      ·
        refine ⟨1657030913378968813717697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104687275585979209145131 1657030913378968813717697)
        ·
          refine ⟨1242773185034226610288273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657030913378968813717697 1242773185034226610288273)
          ·
            refine ⟨932079888775669957716205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242773185034226610288273 932079888775669957716205)
            ·
              refine ⟨349529958290876234143577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932079888775669957716205 349529958290876234143577)
              ·
                refine ⟨262147468718157175607683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349529958290876234143577 262147468718157175607683)
                ·
                  refine ⟨393221203077235763411525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262147468718157175607683 393221203077235763411525)
                  ·
                    refine ⟨73728975576981705639661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393221203077235763411525 73728975576981705639661)
                    ·
                      rfl

theorem cell22_215380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_215380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215380 prefixEnd_215380 := by exact prefixLift 215380
  have htrace : WordTrace (prefixWord ++ tailWord_215380) baseStart_215380 baseEnd_215380 := by
    simpa [prefixWord, tailWord_215380, baseEnd_215380] using wordTrace_append hprefix tailTrace_215380
  have hstable : (prefixWord ++ tailWord_215380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215380).length < 2 ^ (prefixWord ++ tailWord_215380).sum := by decide
  have hdescent : baseEnd_215380 < baseStart_215380 := by decide
  rcases family_descends (prefixWord ++ tailWord_215380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215391 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_215391 : Nat := 118140960795 + 215391 * 2 ^ 59
def prefixEnd_215391 : Nat := 4983230072969 + 3 ^ 40 * 215391 * 2
def baseEnd_215391 : Nat := 73732741101781343614627

theorem tailTrace_215391 : CollatzResearch.WordTrace tailWord_215391 prefixEnd_215391 73732741101781343614627 := by
  unfold tailWord_215391
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855955162682667699238027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5237303441788445132825351 7855955162682667699238027)
  ·
    refine ⟨11783932744024001548857041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855955162682667699238027 11783932744024001548857041)
    ·
      refine ⟨8837949558018001161642781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11783932744024001548857041 8837949558018001161642781)
      ·
        refine ⟨3314231084256750435616043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8837949558018001161642781 3314231084256750435616043)
        ·
          refine ⟨4971346626385125653424065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314231084256750435616043 4971346626385125653424065)
          ·
            refine ⟨3728509969788844240068049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4971346626385125653424065 3728509969788844240068049)
            ·
              refine ⟨2796382477341633180051037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728509969788844240068049 2796382477341633180051037)
              ·
                refine ⟨1048643429003112442519139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2796382477341633180051037 1048643429003112442519139)
                ·
                  refine ⟨1572965143504668663778709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048643429003112442519139 1572965143504668663778709)
                  ·
                    refine ⟨73732741101781343614627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1572965143504668663778709 73732741101781343614627)
                    ·
                      rfl

theorem cell22_215391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_215391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215391 prefixEnd_215391 := by exact prefixLift 215391
  have htrace : WordTrace (prefixWord ++ tailWord_215391) baseStart_215391 baseEnd_215391 := by
    simpa [prefixWord, tailWord_215391, baseEnd_215391] using wordTrace_append hprefix tailTrace_215391
  have hstable : (prefixWord ++ tailWord_215391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215391).length < 2 ^ (prefixWord ++ tailWord_215391).sum := by decide
  have hdescent : baseEnd_215391 < baseStart_215391 := by decide
  rcases family_descends (prefixWord ++ tailWord_215391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215406 : List Nat := [4, 1, 2, 15]
def baseStart_215406 : Nat := 118140960795 + 215406 * 2 ^ 59
def prefixEnd_215406 : Nat := 4983230072969 + 3 ^ 40 * 215406 * 2
def baseEnd_215406 : Nat := 101149349668486014389

theorem tailTrace_215406 : CollatzResearch.WordTrace tailWord_215406 prefixEnd_215406 101149349668486014389 := by
  unfold tailWord_215406
  simp only [CollatzResearch.WordTrace]
  refine ⟨982062782203540657629259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5237668171752216840689381 982062782203540657629259)
  ·
    refine ⟨1473094173305310986443889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982062782203540657629259 1473094173305310986443889)
    ·
      refine ⟨1104820629978983239832917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1473094173305310986443889 1104820629978983239832917)
      ·
        refine ⟨101149349668486014389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 1104820629978983239832917 101149349668486014389)
        ·
          rfl

theorem cell22_215406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 15].length) (baseStart_215406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215406 prefixEnd_215406 := by exact prefixLift 215406
  have htrace : WordTrace (prefixWord ++ tailWord_215406) baseStart_215406 baseEnd_215406 := by
    simpa [prefixWord, tailWord_215406, baseEnd_215406] using wordTrace_append hprefix tailTrace_215406
  have hstable : (prefixWord ++ tailWord_215406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215406).length < 2 ^ (prefixWord ++ tailWord_215406).sum := by decide
  have hdescent : baseEnd_215406 < baseStart_215406 := by decide
  rcases family_descends (prefixWord ++ tailWord_215406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215408 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_215408 : Nat := 118140960795 + 215408 * 2 ^ 59
def prefixEnd_215408 : Nat := 4983230072969 + 3 ^ 40 * 215408 * 2
def baseEnd_215408 : Nat := 73738560549198965939575

theorem tailTrace_215408 : CollatzResearch.WordTrace tailWord_215408 prefixEnd_215408 73738560549198965939575 := by
  unfold tailWord_215408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928287601810539801303439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5237716802414053068404585 3928287601810539801303439)
  ·
    refine ⟨5892431402715809701955159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3928287601810539801303439 5892431402715809701955159)
    ·
      refine ⟨8838647104073714552932739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892431402715809701955159 8838647104073714552932739)
      ·
        refine ⟨13257970656110571829399109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8838647104073714552932739 13257970656110571829399109)
        ·
          refine ⟨2485869498020732218012333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13257970656110571829399109 2485869498020732218012333)
          ·
            refine ⟨932201061757774581754625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2485869498020732218012333 932201061757774581754625)
            ·
              refine ⟨699150796318330936315969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932201061757774581754625 699150796318330936315969)
              ·
                refine ⟨524363097238748202236977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699150796318330936315969 524363097238748202236977)
                ·
                  refine ⟨393272322929061151677733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524363097238748202236977 393272322929061151677733)
                  ·
                    refine ⟨73738560549198965939575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393272322929061151677733 73738560549198965939575)
                    ·
                      rfl

theorem cell22_215408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_215408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215408 prefixEnd_215408 := by exact prefixLift 215408
  have htrace : WordTrace (prefixWord ++ tailWord_215408) baseStart_215408 baseEnd_215408 := by
    simpa [prefixWord, tailWord_215408, baseEnd_215408] using wordTrace_append hprefix tailTrace_215408
  have hstable : (prefixWord ++ tailWord_215408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215408).length < 2 ^ (prefixWord ++ tailWord_215408).sum := by decide
  have hdescent : baseEnd_215408 < baseStart_215408 := by decide
  rcases family_descends (prefixWord ++ tailWord_215408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215410 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_215410 : Nat := 118140960795 + 215410 * 2 ^ 59
def prefixEnd_215410 : Nat := 4983230072969 + 3 ^ 40 * 215410 * 2
def baseEnd_215410 : Nat := 73739245190071627389569

theorem tailTrace_215410 : CollatzResearch.WordTrace tailWord_215410 prefixEnd_215410 73739245190071627389569 := by
  unfold tailWord_215410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964162037403458486044921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5237765433075889296119789 1964162037403458486044921)
  ·
    refine ⟨1473121528052593864533691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1964162037403458486044921 1473121528052593864533691)
    ·
      refine ⟨2209682292078890796800537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473121528052593864533691 2209682292078890796800537)
      ·
        refine ⟨1657261719059168097600403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2209682292078890796800537 1657261719059168097600403)
        ·
          refine ⟨2485892578588752146400605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657261719059168097600403 2485892578588752146400605)
          ·
            refine ⟨932209716970782054900227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2485892578588752146400605 932209716970782054900227)
            ·
              refine ⟨1398314575456173082350341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932209716970782054900227 1398314575456173082350341)
              ·
                refine ⟨262183982898032452940689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1398314575456173082350341 262183982898032452940689)
                ·
                  refine ⟨196637987173524339705517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262183982898032452940689 196637987173524339705517)
                  ·
                    refine ⟨73739245190071627389569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196637987173524339705517 73739245190071627389569)
                    ·
                      rfl

theorem cell22_215410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_215410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215410 prefixEnd_215410 := by exact prefixLift 215410
  have htrace : WordTrace (prefixWord ++ tailWord_215410) baseStart_215410 baseEnd_215410 := by
    simpa [prefixWord, tailWord_215410, baseEnd_215410] using wordTrace_append hprefix tailTrace_215410
  have hstable : (prefixWord ++ tailWord_215410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215410).length < 2 ^ (prefixWord ++ tailWord_215410).sum := by decide
  have hdescent : baseEnd_215410 < baseStart_215410 := by decide
  rcases family_descends (prefixWord ++ tailWord_215410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215530 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_215530 : Nat := 118140960795 + 215530 * 2 ^ 59
def prefixEnd_215530 : Nat := 4983230072969 + 3 ^ 40 * 215530 * 2
def baseEnd_215530 : Nat := 24593441214143771463067

theorem tailTrace_215530 : CollatzResearch.WordTrace tailWord_215530 prefixEnd_215530 24593441214143771463067 := by
  unfold tailWord_215530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965256227294773609637011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5240683272786062959032029 1965256227294773609637011)
  ·
    refine ⟨2947884340942160414455517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965256227294773609637011 2947884340942160414455517)
    ·
      refine ⟨1105456627853310155420819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2947884340942160414455517 1105456627853310155420819)
      ·
        refine ⟨1658184941779965233131229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105456627853310155420819 1658184941779965233131229)
        ·
          refine ⟨621819353167486962424211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1658184941779965233131229 621819353167486962424211)
          ·
            refine ⟨932729029751230443636317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621819353167486962424211 932729029751230443636317)
            ·
              refine ⟨349773386156711416363619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932729029751230443636317 349773386156711416363619)
              ·
                refine ⟨524660079235067124545429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349773386156711416363619 524660079235067124545429)
                ·
                  refine ⟨24593441214143771463067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 524660079235067124545429 24593441214143771463067)
                  ·
                    rfl

theorem cell22_215530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_215530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215530 prefixEnd_215530 := by exact prefixLift 215530
  have htrace : WordTrace (prefixWord ++ tailWord_215530) baseStart_215530 baseEnd_215530 := by
    simpa [prefixWord, tailWord_215530, baseEnd_215530] using wordTrace_append hprefix tailTrace_215530
  have hstable : (prefixWord ++ tailWord_215530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215530).length < 2 ^ (prefixWord ++ tailWord_215530).sum := by decide
  have hdescent : baseEnd_215530 < baseStart_215530 := by decide
  rcases family_descends (prefixWord ++ tailWord_215530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215575 : List Nat := [1, 1, 3, 6, 1, 10]
def baseStart_215575 : Nat := 118140960795 + 215575 * 2 ^ 59
def prefixEnd_215575 : Nat := 4983230072969 + 3 ^ 40 * 215575 * 2
def baseEnd_215575 : Nat := 911058371136619716223

theorem tailTrace_215575 : CollatzResearch.WordTrace tailWord_215575 prefixEnd_215575 911058371136619716223 := by
  unfold tailWord_215575
  simp only [CollatzResearch.WordTrace]
  refine ⟨7862666194016067123936179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5241777462677378082624119 7862666194016067123936179)
  ·
    refine ⟨11793999291024100685904269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7862666194016067123936179 11793999291024100685904269)
    ·
      refine ⟨4422749734134037757214101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11793999291024100685904269 4422749734134037757214101)
      ·
        refine ⟨207316393787533019869411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4422749734134037757214101 207316393787533019869411)
        ·
          refine ⟨310974590681299529804117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207316393787533019869411 310974590681299529804117)
          ·
            refine ⟨911058371136619716223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 310974590681299529804117 911058371136619716223)
            ·
              rfl

theorem cell22_215575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 10].length) (baseStart_215575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215575 prefixEnd_215575 := by exact prefixLift 215575
  have htrace : WordTrace (prefixWord ++ tailWord_215575) baseStart_215575 baseEnd_215575 := by
    simpa [prefixWord, tailWord_215575, baseEnd_215575] using wordTrace_append hprefix tailTrace_215575
  have hstable : (prefixWord ++ tailWord_215575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215575).length < 2 ^ (prefixWord ++ tailWord_215575).sum := by decide
  have hdescent : baseEnd_215575 < baseStart_215575 := by decide
  rcases family_descends (prefixWord ++ tailWord_215575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215592 : List Nat := [2, 1, 5, 2, 1, 3, 1, 7]
def baseStart_215592 : Nat := 118140960795 + 215592 * 2 ^ 59
def prefixEnd_215592 : Nat := 4983230072969 + 3 ^ 40 * 215592 * 2
def baseEnd_215592 : Nat := 8200171945498202148779

theorem tailTrace_215592 : CollatzResearch.WordTrace tailWord_215592 prefixEnd_215592 8200171945498202148779 := by
  unfold tailWord_215592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931643117477239513652515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5242190823302986018203353 3931643117477239513652515)
  ·
    refine ⟨5897464676215859270478773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3931643117477239513652515 5897464676215859270478773)
    ·
      refine ⟨552887313395236806607385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5897464676215859270478773 552887313395236806607385)
      ·
        refine ⟨414665485046427604955539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552887313395236806607385 414665485046427604955539)
        ·
          refine ⟨621998227569641407433309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414665485046427604955539 621998227569641407433309)
          ·
            refine ⟨233249335338615527787491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621998227569641407433309 233249335338615527787491)
            ·
              refine ⟨349874003007923291681237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233249335338615527787491 349874003007923291681237)
              ·
                refine ⟨8200171945498202148779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 349874003007923291681237 8200171945498202148779)
                ·
                  rfl

theorem cell22_215592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_215592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215592 prefixEnd_215592 := by exact prefixLift 215592
  have htrace : WordTrace (prefixWord ++ tailWord_215592) baseStart_215592 baseEnd_215592 := by
    simpa [prefixWord, tailWord_215592, baseEnd_215592] using wordTrace_append hprefix tailTrace_215592
  have hstable : (prefixWord ++ tailWord_215592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215592).length < 2 ^ (prefixWord ++ tailWord_215592).sum := by decide
  have hdescent : baseEnd_215592 < baseStart_215592 := by decide
  rcases family_descends (prefixWord ++ tailWord_215592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215695 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 2, 4]
def baseStart_215695 : Nat := 118140960795 + 215695 * 2 ^ 59
def prefixEnd_215695 : Nat := 4983230072969 + 3 ^ 40 * 215695 * 2
def baseEnd_215695 : Nat := 73836806514425884013695

theorem tailTrace_215695 : CollatzResearch.WordTrace tailWord_215695 prefixEnd_215695 73836806514425884013695 := by
  unfold tailWord_215695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867042953581327618304539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5244695302387551745536359 7867042953581327618304539)
  ·
    refine ⟨11800564430371991427456809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7867042953581327618304539 11800564430371991427456809)
    ·
      refine ⟨8850423322778993570592607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11800564430371991427456809 8850423322778993570592607)
      ·
        refine ⟨13275634984168490355888911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8850423322778993570592607 13275634984168490355888911)
        ·
          refine ⟨19913452476252735533833367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13275634984168490355888911 19913452476252735533833367)
          ·
            refine ⟨29870178714379103300750051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19913452476252735533833367 29870178714379103300750051)
            ·
              refine ⟨44805268071568654951125077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29870178714379103300750051 44805268071568654951125077)
              ·
                refine ⟨525061735213695175208497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 44805268071568654951125077 525061735213695175208497)
                ·
                  refine ⟨393796301410271381406373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525061735213695175208497 393796301410271381406373)
                  ·
                    refine ⟨73836806514425884013695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393796301410271381406373 73836806514425884013695)
                    ·
                      rfl

theorem cell22_215695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_215695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215695 prefixEnd_215695 := by exact prefixLift 215695
  have htrace : WordTrace (prefixWord ++ tailWord_215695) baseStart_215695 baseEnd_215695 := by
    simpa [prefixWord, tailWord_215695, baseEnd_215695] using wordTrace_append hprefix tailTrace_215695
  have hstable : (prefixWord ++ tailWord_215695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215695).length < 2 ^ (prefixWord ++ tailWord_215695).sum := by decide
  have hdescent : baseEnd_215695 < baseStart_215695 := by decide
  rcases family_descends (prefixWord ++ tailWord_215695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215800 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_215800 : Nat := 118140960795 + 215800 * 2 ^ 59
def prefixEnd_215800 : Nat := 4983230072969 + 3 ^ 40 * 215800 * 2
def baseEnd_215800 : Nat := 24624250053413536712791

theorem tailTrace_215800 : CollatzResearch.WordTrace tailWord_215800 prefixEnd_215800 24624250053413536712791 := by
  unfold tailWord_215800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935436309100465275438427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5247248412133953700584569 3935436309100465275438427)
  ·
    refine ⟨5903154463650697913157641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935436309100465275438427 5903154463650697913157641)
    ·
      refine ⟨4427365847738023434868231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5903154463650697913157641 4427365847738023434868231)
      ·
        refine ⟨6641048771607035152302347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427365847738023434868231 6641048771607035152302347)
        ·
          refine ⟨9961573157410552728453521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641048771607035152302347 9961573157410552728453521)
          ·
            refine ⟨7471179868057914546340141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9961573157410552728453521 7471179868057914546340141)
            ·
              refine ⟨2801692450521717954877553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7471179868057914546340141 2801692450521717954877553)
              ·
                refine ⟨2101269337891288466158165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801692450521717954877553 2101269337891288466158165)
                ·
                  refine ⟨24624250053413536712791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2101269337891288466158165 24624250053413536712791)
                  ·
                    rfl

theorem cell22_215800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_215800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215800 prefixEnd_215800 := by exact prefixLift 215800
  have htrace : WordTrace (prefixWord ++ tailWord_215800) baseStart_215800 baseEnd_215800 := by
    simpa [prefixWord, tailWord_215800, baseEnd_215800] using wordTrace_append hprefix tailTrace_215800
  have hstable : (prefixWord ++ tailWord_215800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215800).length < 2 ^ (prefixWord ++ tailWord_215800).sum := by decide
  have hdescent : baseEnd_215800 < baseStart_215800 := by decide
  rcases family_descends (prefixWord ++ tailWord_215800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215806 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_215806 : Nat := 118140960795 + 215806 * 2 ^ 59
def prefixEnd_215806 : Nat := 4983230072969 + 3 ^ 40 * 215806 * 2
def baseEnd_215806 : Nat := 24624934694286198162785

theorem tailTrace_215806 : CollatzResearch.WordTrace tailWord_215806 prefixEnd_215806 24624934694286198162785 := by
  unfold tailWord_215806
  simp only [CollatzResearch.WordTrace]
  refine ⟨983886432022399196949409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5247394304119462383730181 983886432022399196949409)
  ·
    refine ⟨737914824016799397712057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 983886432022399196949409 737914824016799397712057)
    ·
      refine ⟨553436118012599548284043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 737914824016799397712057 553436118012599548284043)
      ·
        refine ⟨830154177018899322426065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553436118012599548284043 830154177018899322426065)
        ·
          refine ⟨622615632764174491819549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830154177018899322426065 622615632764174491819549)
          ·
            refine ⟨233480862286565434432331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622615632764174491819549 233480862286565434432331)
            ·
              refine ⟨350221293429848151648497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233480862286565434432331 350221293429848151648497)
              ·
                refine ⟨262665970072386113736373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350221293429848151648497 262665970072386113736373)
                ·
                  refine ⟨24624934694286198162785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262665970072386113736373 24624934694286198162785)
                  ·
                    rfl

theorem cell22_215806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_215806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215806 prefixEnd_215806 := by exact prefixLift 215806
  have htrace : WordTrace (prefixWord ++ tailWord_215806) baseStart_215806 baseEnd_215806 := by
    simpa [prefixWord, tailWord_215806, baseEnd_215806] using wordTrace_append hprefix tailTrace_215806
  have hstable : (prefixWord ++ tailWord_215806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215806).length < 2 ^ (prefixWord ++ tailWord_215806).sum := by decide
  have hdescent : baseEnd_215806 < baseStart_215806 := by decide
  rcases family_descends (prefixWord ++ tailWord_215806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215971 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 1, 4]
def baseStart_215971 : Nat := 118140960795 + 215971 * 2 ^ 59
def prefixEnd_215971 : Nat := 4983230072969 + 3 ^ 40 * 215971 * 2
def baseEnd_215971 : Nat := 73931286954853164112849

theorem tailTrace_215971 : CollatzResearch.WordTrace tailWord_215971 prefixEnd_215971 73931286954853164112849 := by
  unfold tailWord_215971
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877109500581426755351767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5251406333720951170234511 7877109500581426755351767)
  ·
    refine ⟨11815664250872140133027651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7877109500581426755351767 11815664250872140133027651)
    ·
      refine ⟨17723496376308210199541477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11815664250872140133027651 17723496376308210199541477)
      ·
        refine ⟨3323155570557789412414027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17723496376308210199541477 3323155570557789412414027)
        ·
          refine ⟨4984733355836684118621041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323155570557789412414027 4984733355836684118621041)
          ·
            refine ⟨3738550016877513088965781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984733355836684118621041 3738550016877513088965781)
            ·
              refine ⟨175244532041133426045271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3738550016877513088965781 175244532041133426045271)
              ·
                refine ⟨262866798061700139067907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175244532041133426045271 262866798061700139067907)
                ·
                  refine ⟨394300197092550208601861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262866798061700139067907 394300197092550208601861)
                  ·
                    refine ⟨73931286954853164112849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 394300197092550208601861 73931286954853164112849)
                    ·
                      rfl

theorem cell22_215971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 4].length) (baseStart_215971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_215971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_215971 prefixEnd_215971 := by exact prefixLift 215971
  have htrace : WordTrace (prefixWord ++ tailWord_215971) baseStart_215971 baseEnd_215971 := by
    simpa [prefixWord, tailWord_215971, baseEnd_215971] using wordTrace_append hprefix tailTrace_215971
  have hstable : (prefixWord ++ tailWord_215971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215971).length < 2 ^ (prefixWord ++ tailWord_215971).sum := by decide
  have hdescent : baseEnd_215971 < baseStart_215971 := by decide
  rcases family_descends (prefixWord ++ tailWord_215971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216014 : List Nat := [4, 1, 1, 1, 2, 4, 1, 8]
def baseStart_216014 : Nat := 118140960795 + 216014 * 2 ^ 59
def prefixEnd_216014 : Nat := 4983230072969 + 3 ^ 40 * 216014 * 2
def baseEnd_216014 : Nat := 8216222970401709476413

theorem tailTrace_216014 : CollatzResearch.WordTrace tailWord_216014 prefixEnd_216014 8216222970401709476413 := by
  unfold tailWord_216014
  simp only [CollatzResearch.WordTrace]
  refine ⟨984834729928205637395887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5252451892950430066111397 984834729928205637395887)
  ·
    refine ⟨1477252094892308456093831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984834729928205637395887 1477252094892308456093831)
    ·
      refine ⟨2215878142338462684140747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477252094892308456093831 2215878142338462684140747)
      ·
        refine ⟨3323817213507694026211121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215878142338462684140747 3323817213507694026211121)
        ·
          refine ⟨2492862910130770519658341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323817213507694026211121 2492862910130770519658341)
          ·
            refine ⟨467411795649519472435939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2492862910130770519658341 467411795649519472435939)
            ·
              refine ⟨701117693474279208653909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467411795649519472435939 701117693474279208653909)
              ·
                refine ⟨8216222970401709476413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 701117693474279208653909 8216222970401709476413)
                ·
                  rfl

theorem cell22_216014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_216014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216014 prefixEnd_216014 := by exact prefixLift 216014
  have htrace : WordTrace (prefixWord ++ tailWord_216014) baseStart_216014 baseEnd_216014 := by
    simpa [prefixWord, tailWord_216014, baseEnd_216014] using wordTrace_append hprefix tailTrace_216014
  have hstable : (prefixWord ++ tailWord_216014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216014).length < 2 ^ (prefixWord ++ tailWord_216014).sum := by decide
  have hdescent : baseEnd_216014 < baseStart_216014 := by decide
  rcases family_descends (prefixWord ++ tailWord_216014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216031 : List Nat := [1, 1, 2, 3, 6, 1, 8]
def baseStart_216031 : Nat := 118140960795 + 216031 * 2 ^ 59
def prefixEnd_216031 : Nat := 4983230072969 + 3 ^ 40 * 216031 * 2
def baseEnd_216031 : Nat := 2738956525223444726395

theorem tailTrace_216031 : CollatzResearch.WordTrace tailWord_216031 prefixEnd_216031 2738956525223444726395 := by
  unfold tailWord_216031
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879297880364057002535947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5252865253576038001690631 7879297880364057002535947)
  ·
    refine ⟨11818946820546085503803921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7879297880364057002535947 11818946820546085503803921)
    ·
      refine ⟨8864210115409564127852941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11818946820546085503803921 8864210115409564127852941)
      ·
        refine ⟨3324078793278586547944853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8864210115409564127852941 3324078793278586547944853)
        ·
          refine ⟨155816193434933744434915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3324078793278586547944853 155816193434933744434915)
          ·
            refine ⟨233724290152400616652373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155816193434933744434915 233724290152400616652373)
            ·
              refine ⟨2738956525223444726395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 233724290152400616652373 2738956525223444726395)
              ·
                rfl

theorem cell22_216031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 8].length) (baseStart_216031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216031 prefixEnd_216031 := by exact prefixLift 216031
  have htrace : WordTrace (prefixWord ++ tailWord_216031) baseStart_216031 baseEnd_216031 := by
    simpa [prefixWord, tailWord_216031, baseEnd_216031] using wordTrace_append hprefix tailTrace_216031
  have hstable : (prefixWord ++ tailWord_216031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216031).length < 2 ^ (prefixWord ++ tailWord_216031).sum := by decide
  have hdescent : baseEnd_216031 < baseStart_216031 := by decide
  rcases family_descends (prefixWord ++ tailWord_216031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216093 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 5]
def baseStart_216093 : Nat := 118140960795 + 216093 * 2 ^ 59
def prefixEnd_216093 : Nat := 4983230072969 + 3 ^ 40 * 216093 * 2
def baseEnd_216093 : Nat := 24657683349361837520825

theorem tailTrace_216093 : CollatzResearch.WordTrace tailWord_216093 prefixEnd_216093 24657683349361837520825 := by
  unfold tailWord_216093
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881559206139441591292933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5254372804092961060861955 7881559206139441591292933)
  ·
    refine ⟨1477792351151145298367425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7881559206139441591292933 1477792351151145298367425)
    ·
      refine ⟨1108344263363358973775569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1477792351151145298367425 1108344263363358973775569)
      ·
        refine ⟨831258197522519230331677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1108344263363358973775569 831258197522519230331677)
        ·
          refine ⟨311721824070944711374379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 831258197522519230331677 311721824070944711374379)
          ·
            refine ⟨467582736106417067061569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311721824070944711374379 467582736106417067061569)
            ·
              refine ⟨350687052079812800296177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467582736106417067061569 350687052079812800296177)
              ·
                refine ⟨263015289059859600222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350687052079812800296177 263015289059859600222133)
                ·
                  refine ⟨24657683349361837520825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263015289059859600222133 24657683349361837520825)
                  ·
                    rfl

theorem cell22_216093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_216093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216093 prefixEnd_216093 := by exact prefixLift 216093
  have htrace : WordTrace (prefixWord ++ tailWord_216093) baseStart_216093 baseEnd_216093 := by
    simpa [prefixWord, tailWord_216093, baseEnd_216093] using wordTrace_append hprefix tailTrace_216093
  have hstable : (prefixWord ++ tailWord_216093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216093).length < 2 ^ (prefixWord ++ tailWord_216093).sum := by decide
  have hdescent : baseEnd_216093 < baseStart_216093 := by decide
  rcases family_descends (prefixWord ++ tailWord_216093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216097 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 1, 3]
def baseStart_216097 : Nat := 118140960795 + 216097 * 2 ^ 59
def prefixEnd_216097 : Nat := 4983230072969 + 3 ^ 40 * 216097 * 2
def baseEnd_216097 : Nat := 73974419329830835462463

theorem tailTrace_216097 : CollatzResearch.WordTrace tailWord_216097 prefixEnd_216097 73974419329830835462463 := by
  unfold tailWord_216097
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881705098124950274438545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5254470065416633516292363 7881705098124950274438545)
  ·
    refine ⟨5911278823593712705828909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7881705098124950274438545 5911278823593712705828909)
    ·
      refine ⟨2216729558847642264685841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5911278823593712705828909 2216729558847642264685841)
      ·
        refine ⟨1662547169135731698514381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2216729558847642264685841 1662547169135731698514381)
        ·
          refine ⟨623455188425899386942893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1662547169135731698514381 623455188425899386942893)
          ·
            refine ⟨233795695659712270103585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623455188425899386942893 233795695659712270103585)
            ·
              refine ⟨175346771744784202577689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233795695659712270103585 175346771744784202577689)
              ·
                refine ⟨131510078808588151933267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175346771744784202577689 131510078808588151933267)
                ·
                  refine ⟨197265118212882227899901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131510078808588151933267 197265118212882227899901)
                  ·
                    refine ⟨73974419329830835462463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197265118212882227899901 73974419329830835462463)
                    ·
                      rfl

theorem cell22_216097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_216097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216097 prefixEnd_216097 := by exact prefixLift 216097
  have htrace : WordTrace (prefixWord ++ tailWord_216097) baseStart_216097 baseEnd_216097 := by
    simpa [prefixWord, tailWord_216097, baseEnd_216097] using wordTrace_append hprefix tailTrace_216097
  have hstable : (prefixWord ++ tailWord_216097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216097).length < 2 ^ (prefixWord ++ tailWord_216097).sum := by decide
  have hdescent : baseEnd_216097 < baseStart_216097 := by decide
  rcases family_descends (prefixWord ++ tailWord_216097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216121 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 6]
def baseStart_216121 : Nat := 118140960795 + 216121 * 2 ^ 59
def prefixEnd_216121 : Nat := 4983230072969 + 3 ^ 40 * 216121 * 2
def baseEnd_216121 : Nat := 24660878340100924287463

theorem tailTrace_216121 : CollatzResearch.WordTrace tailWord_216121 prefixEnd_216121 24660878340100924287463 := by
  unfold tailWord_216121
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882580450038002373312217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5255053633358668248874811 7882580450038002373312217)
  ·
    refine ⟨5911935337528501779984163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7882580450038002373312217 5911935337528501779984163)
    ·
      refine ⟨8867903006292752669976245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911935337528501779984163 8867903006292752669976245)
      ·
        refine ⟨831365906839945562810273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8867903006292752669976245 831365906839945562810273)
        ·
          refine ⟨623524430129959172107705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831365906839945562810273 623524430129959172107705)
          ·
            refine ⟨467643322597469379080779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623524430129959172107705 467643322597469379080779)
            ·
              refine ⟨701464983896204068621169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467643322597469379080779 701464983896204068621169)
              ·
                refine ⟨526098737922153051465877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701464983896204068621169 526098737922153051465877)
                ·
                  refine ⟨24660878340100924287463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 526098737922153051465877 24660878340100924287463)
                  ·
                    rfl

theorem cell22_216121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_216121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216121 prefixEnd_216121 := by exact prefixLift 216121
  have htrace : WordTrace (prefixWord ++ tailWord_216121) baseStart_216121 baseEnd_216121 := by
    simpa [prefixWord, tailWord_216121, baseEnd_216121] using wordTrace_append hprefix tailTrace_216121
  have hstable : (prefixWord ++ tailWord_216121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216121).length < 2 ^ (prefixWord ++ tailWord_216121).sum := by decide
  have hdescent : baseEnd_216121 < baseStart_216121 := by decide
  rcases family_descends (prefixWord ++ tailWord_216121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216136 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_216136 : Nat := 118140960795 + 216136 * 2 ^ 59
def prefixEnd_216136 : Nat := 4983230072969 + 3 ^ 40 * 216136 * 2
def baseEnd_216136 : Nat := 73987769826847733737343

theorem tailTrace_216136 : CollatzResearch.WordTrace tailWord_216136 prefixEnd_216136 73987769826847733737343 := by
  unfold tailWord_216136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941563772491829967554131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5255418363322439956738841 3941563772491829967554131)
  ·
    refine ⟨5912345658737744951331197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3941563772491829967554131 5912345658737744951331197)
    ·
      refine ⟨2217129622026654356749199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5912345658737744951331197 2217129622026654356749199)
      ·
        refine ⟨3325694433039981535123799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217129622026654356749199 3325694433039981535123799)
        ·
          refine ⟨4988541649559972302685699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325694433039981535123799 4988541649559972302685699)
          ·
            refine ⟨7482812474339958454028549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988541649559972302685699 7482812474339958454028549)
            ·
              refine ⟨1403027338938742210130353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7482812474339958454028549 1403027338938742210130353)
              ·
                refine ⟨1052270504204056657597765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403027338938742210130353 1052270504204056657597765)
                ·
                  refine ⟨197300719538260623299581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052270504204056657597765 197300719538260623299581)
                  ·
                    refine ⟨73987769826847733737343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197300719538260623299581 73987769826847733737343)
                    ·
                      rfl

theorem cell22_216136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_216136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216136 prefixEnd_216136 := by exact prefixLift 216136
  have htrace : WordTrace (prefixWord ++ tailWord_216136) baseStart_216136 baseEnd_216136 := by
    simpa [prefixWord, tailWord_216136, baseEnd_216136] using wordTrace_append hprefix tailTrace_216136
  have hstable : (prefixWord ++ tailWord_216136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216136).length < 2 ^ (prefixWord ++ tailWord_216136).sum := by decide
  have hdescent : baseEnd_216136 < baseStart_216136 := by decide
  rcases family_descends (prefixWord ++ tailWord_216136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216149 : List Nat := [1, 3, 2, 2, 1, 2, 11]
def baseStart_216149 : Nat := 118140960795 + 216149 * 2 ^ 59
def prefixEnd_216149 : Nat := 4983230072969 + 3 ^ 40 * 216149 * 2
def baseEnd_216149 : Nat := 2740452592315556783789

theorem tailTrace_216149 : CollatzResearch.WordTrace tailWord_216149 prefixEnd_216149 2740452592315556783789 := by
  unfold tailWord_216149
  simp only [CollatzResearch.WordTrace]
  refine ⟨7883601693936563155331501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5255734462624375436887667 7883601693936563155331501)
  ·
    refine ⟨2956350635226211183249313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7883601693936563155331501 2956350635226211183249313)
    ·
      refine ⟨2217262976419658387436985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2956350635226211183249313 2217262976419658387436985)
      ·
        refine ⟨1662947232314743790577739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2217262976419658387436985 1662947232314743790577739)
        ·
          refine ⟨2494420848472115685866609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662947232314743790577739 2494420848472115685866609)
          ·
            refine ⟨1870815636354086764399957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494420848472115685866609 1870815636354086764399957)
            ·
              refine ⟨2740452592315556783789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1870815636354086764399957 2740452592315556783789)
              ·
                rfl

theorem cell22_216149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 11].length) (baseStart_216149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216149 prefixEnd_216149 := by exact prefixLift 216149
  have htrace : WordTrace (prefixWord ++ tailWord_216149) baseStart_216149 baseEnd_216149 := by
    simpa [prefixWord, tailWord_216149, baseEnd_216149] using wordTrace_append hprefix tailTrace_216149
  have hstable : (prefixWord ++ tailWord_216149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216149).length < 2 ^ (prefixWord ++ tailWord_216149).sum := by decide
  have hdescent : baseEnd_216149 < baseStart_216149 := by decide
  rcases family_descends (prefixWord ++ tailWord_216149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216215 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 3, 3]
def baseStart_216215 : Nat := 118140960795 + 216215 * 2 ^ 59
def prefixEnd_216215 : Nat := 4983230072969 + 3 ^ 40 * 216215 * 2
def baseEnd_216215 : Nat := 74014813141317861012101

theorem tailTrace_216215 : CollatzResearch.WordTrace tailWord_216215 prefixEnd_216215 74014813141317861012101 := by
  unfold tailWord_216215
  simp only [CollatzResearch.WordTrace]
  refine ⟨7886008911697456427234099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5257339274464970951489399 7886008911697456427234099)
  ·
    refine ⟨11829013367546184640851149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7886008911697456427234099 11829013367546184640851149)
    ·
      refine ⟨4435880012829819240319181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11829013367546184640851149 4435880012829819240319181)
      ·
        refine ⟨1663455004811182215119693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4435880012829819240319181 1663455004811182215119693)
        ·
          refine ⟨623795626804193330669885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1663455004811182215119693 623795626804193330669885)
          ·
            refine ⟨233923360051572499001207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623795626804193330669885 233923360051572499001207)
            ·
              refine ⟨350885040077358748501811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233923360051572499001207 350885040077358748501811)
              ·
                refine ⟨526327560116038122752717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350885040077358748501811 526327560116038122752717)
                ·
                  refine ⟨197372835043514296032269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526327560116038122752717 197372835043514296032269)
                  ·
                    refine ⟨74014813141317861012101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197372835043514296032269 74014813141317861012101)
                    ·
                      rfl

theorem cell22_216215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_216215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216215 prefixEnd_216215 := by exact prefixLift 216215
  have htrace : WordTrace (prefixWord ++ tailWord_216215) baseStart_216215 baseEnd_216215 := by
    simpa [prefixWord, tailWord_216215, baseEnd_216215] using wordTrace_append hprefix tailTrace_216215
  have hstable : (prefixWord ++ tailWord_216215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216215).length < 2 ^ (prefixWord ++ tailWord_216215).sum := by decide
  have hdescent : baseEnd_216215 < baseStart_216215 := by decide
  rcases family_descends (prefixWord ++ tailWord_216215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216228 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_216228 : Nat := 118140960795 + 216228 * 2 ^ 59
def prefixEnd_216228 : Nat := 4983230072969 + 3 ^ 40 * 216228 * 2
def baseEnd_216228 : Nat := 24673087768996720145687

theorem tailTrace_216228 : CollatzResearch.WordTrace tailWord_216228 prefixEnd_216228 24673087768996720145687 := by
  unfold tailWord_216228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943241530325179823728669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5257655373766906431638225 3943241530325179823728669)
  ·
    refine ⟨1478715573871942433898251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3943241530325179823728669 1478715573871942433898251)
    ·
      refine ⟨2218073360807913650847377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478715573871942433898251 2218073360807913650847377)
      ·
        refine ⟨1663555020605935238135533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2218073360807913650847377 1663555020605935238135533)
        ·
          refine ⟨623833132727225714300825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1663555020605935238135533 623833132727225714300825)
          ·
            refine ⟨467874849545419285725619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623833132727225714300825 467874849545419285725619)
            ·
              refine ⟨701812274318128928588429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467874849545419285725619 701812274318128928588429)
              ·
                refine ⟨263179602869298348220661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701812274318128928588429 263179602869298348220661)
                ·
                  refine ⟨24673087768996720145687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263179602869298348220661 24673087768996720145687)
                  ·
                    rfl

theorem cell22_216228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_216228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216228 prefixEnd_216228 := by exact prefixLift 216228
  have htrace : WordTrace (prefixWord ++ tailWord_216228) baseStart_216228 baseEnd_216228 := by
    simpa [prefixWord, tailWord_216228, baseEnd_216228] using wordTrace_append hprefix tailTrace_216228
  have hstable : (prefixWord ++ tailWord_216228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216228).length < 2 ^ (prefixWord ++ tailWord_216228).sum := by decide
  have hdescent : baseEnd_216228 < baseStart_216228 := by decide
  rcases family_descends (prefixWord ++ tailWord_216228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216288 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_216288 : Nat := 118140960795 + 216288 * 2 ^ 59
def prefixEnd_216288 : Nat := 4983230072969 + 3 ^ 40 * 216288 * 2
def baseEnd_216288 : Nat := 74039802533170003936877

theorem tailTrace_216288 : CollatzResearch.WordTrace tailWord_216288 prefixEnd_216288 74039802533170003936877 := by
  unfold tailWord_216288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944335720216494947320759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5259114293621993263094345 3944335720216494947320759)
  ·
    refine ⟨5916503580324742420981139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3944335720216494947320759 5916503580324742420981139)
    ·
      refine ⟨8874755370487113631471709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5916503580324742420981139 8874755370487113631471709)
      ·
        refine ⟨3328033263932667611801891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8874755370487113631471709 3328033263932667611801891)
        ·
          refine ⟨4992049895899001417702837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328033263932667611801891 4992049895899001417702837)
          ·
            refine ⟨468004677740531382909641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4992049895899001417702837 468004677740531382909641)
            ·
              refine ⟨351003508305398537182231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468004677740531382909641 351003508305398537182231)
              ·
                refine ⟨526505262458097805773347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351003508305398537182231 526505262458097805773347)
                ·
                  refine ⟨789757893687146708660021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526505262458097805773347 789757893687146708660021)
                  ·
                    refine ⟨74039802533170003936877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 789757893687146708660021 74039802533170003936877)
                    ·
                      rfl

theorem cell22_216288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_216288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216288 prefixEnd_216288 := by exact prefixLift 216288
  have htrace : WordTrace (prefixWord ++ tailWord_216288) baseStart_216288 baseEnd_216288 := by
    simpa [prefixWord, tailWord_216288, baseEnd_216288] using wordTrace_append hprefix tailTrace_216288
  have hstable : (prefixWord ++ tailWord_216288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216288).length < 2 ^ (prefixWord ++ tailWord_216288).sum := by decide
  have hdescent : baseEnd_216288 < baseStart_216288 := by decide
  rcases family_descends (prefixWord ++ tailWord_216288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216303 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 1, 6]
def baseStart_216303 : Nat := 118140960795 + 216303 * 2 ^ 59
def prefixEnd_216303 : Nat := 4983230072969 + 3 ^ 40 * 216303 * 2
def baseEnd_216303 : Nat := 74044937339714964811831

theorem tailTrace_216303 : CollatzResearch.WordTrace tailWord_216303 prefixEnd_216303 74044937339714964811831 := by
  unfold tailWord_216303
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889218535378647456437563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5259479023585764970958375 7889218535378647456437563)
  ·
    refine ⟨11833827803067971184656345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7889218535378647456437563 11833827803067971184656345)
    ·
      refine ⟨8875370852300978388492259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11833827803067971184656345 8875370852300978388492259)
      ·
        refine ⟨13313056278451467582738389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8875370852300978388492259 13313056278451467582738389)
        ·
          refine ⟨312024756526206271470431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13313056278451467582738389 312024756526206271470431)
          ·
            refine ⟨468037134789309407205647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312024756526206271470431 468037134789309407205647)
            ·
              refine ⟨702055702183964110808471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468037134789309407205647 702055702183964110808471)
              ·
                refine ⟨1053083553275946166212707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702055702183964110808471 1053083553275946166212707)
                ·
                  refine ⟨1579625329913919249319061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053083553275946166212707 1579625329913919249319061)
                  ·
                    refine ⟨74044937339714964811831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1579625329913919249319061 74044937339714964811831)
                    ·
                      rfl

theorem cell22_216303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_216303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216303 prefixEnd_216303 := by exact prefixLift 216303
  have htrace : WordTrace (prefixWord ++ tailWord_216303) baseStart_216303 baseEnd_216303 := by
    simpa [prefixWord, tailWord_216303, baseEnd_216303] using wordTrace_append hprefix tailTrace_216303
  have hstable : (prefixWord ++ tailWord_216303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216303).length < 2 ^ (prefixWord ++ tailWord_216303).sum := by decide
  have hdescent : baseEnd_216303 < baseStart_216303 := by decide
  rcases family_descends (prefixWord ++ tailWord_216303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216318 : List Nat := [4, 2, 2, 1, 1, 3, 9]
def baseStart_216318 : Nat := 118140960795 + 216318 * 2 ^ 59
def prefixEnd_216318 : Nat := 4983230072969 + 3 ^ 40 * 216318 * 2
def baseEnd_216318 : Nat := 2742595264676293543955

theorem tailTrace_216318 : CollatzResearch.WordTrace tailWord_216318 prefixEnd_216318 2742595264676293543955 := by
  unfold tailWord_216318
  simp only [CollatzResearch.WordTrace]
  refine ⟨986220703790538127279201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5259843753549536678822405 986220703790538127279201)
  ·
    refine ⟨739665527842903595459401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 986220703790538127279201 739665527842903595459401)
    ·
      refine ⟨554749145882177696594551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 739665527842903595459401 554749145882177696594551)
      ·
        refine ⟨832123718823266544891827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554749145882177696594551 832123718823266544891827)
        ·
          refine ⟨1248185578234899817337741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832123718823266544891827 1248185578234899817337741)
          ·
            refine ⟨468069591838087431501653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1248185578234899817337741 468069591838087431501653)
            ·
              refine ⟨2742595264676293543955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 468069591838087431501653 2742595264676293543955)
              ·
                rfl

theorem cell22_216318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 9].length) (baseStart_216318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216318 prefixEnd_216318 := by exact prefixLift 216318
  have htrace : WordTrace (prefixWord ++ tailWord_216318) baseStart_216318 baseEnd_216318 := by
    simpa [prefixWord, tailWord_216318, baseEnd_216318] using wordTrace_append hprefix tailTrace_216318
  have hstable : (prefixWord ++ tailWord_216318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216318).length < 2 ^ (prefixWord ++ tailWord_216318).sum := by decide
  have hdescent : baseEnd_216318 < baseStart_216318 := by decide
  rcases family_descends (prefixWord ++ tailWord_216318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216322 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_216322 : Nat := 118140960795 + 216322 * 2 ^ 59
def prefixEnd_216322 : Nat := 4983230072969 + 3 ^ 40 * 216322 * 2
def baseEnd_216322 : Nat := 74051441428005248586773

theorem tailTrace_216322 : CollatzResearch.WordTrace tailWord_216322 prefixEnd_216322 74051441428005248586773 := by
  unfold tailWord_216322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972477880577453425344805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5259941014873209134252813 1972477880577453425344805)
  ·
    refine ⟨369839602608272517252151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1972477880577453425344805 369839602608272517252151)
    ·
      refine ⟨554759403912408775878227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369839602608272517252151 554759403912408775878227)
      ·
        refine ⟨832139105868613163817341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554759403912408775878227 832139105868613163817341)
        ·
          refine ⟨312052164700729936431503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 832139105868613163817341 312052164700729936431503)
          ·
            refine ⟨468078247051094904647255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312052164700729936431503 468078247051094904647255)
            ·
              refine ⟨702117370576642356970883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468078247051094904647255 702117370576642356970883)
              ·
                refine ⟨1053176055864963535456325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702117370576642356970883 1053176055864963535456325)
                ·
                  refine ⟨197470510474680662898061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053176055864963535456325 197470510474680662898061)
                  ·
                    refine ⟨74051441428005248586773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197470510474680662898061 74051441428005248586773)
                    ·
                      rfl

theorem cell22_216322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_216322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216322 prefixEnd_216322 := by exact prefixLift 216322
  have htrace : WordTrace (prefixWord ++ tailWord_216322) baseStart_216322 baseEnd_216322 := by
    simpa [prefixWord, tailWord_216322, baseEnd_216322] using wordTrace_append hprefix tailTrace_216322
  have hstable : (prefixWord ++ tailWord_216322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216322).length < 2 ^ (prefixWord ++ tailWord_216322).sum := by decide
  have hdescent : baseEnd_216322 < baseStart_216322 := by decide
  rcases family_descends (prefixWord ++ tailWord_216322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216352 : List Nat := [2, 1, 1, 5, 4, 1, 2, 6]
def baseStart_216352 : Nat := 118140960795 + 216352 * 2 ^ 59
def prefixEnd_216352 : Nat := 4983230072969 + 3 ^ 40 * 216352 * 2
def baseEnd_216352 : Nat := 8229079004566130037409

theorem tailTrace_216352 : CollatzResearch.WordTrace tailWord_216352 prefixEnd_216352 8229079004566130037409 := by
  unfold tailWord_216352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945502856100564412485655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5260670474800752549980873 3945502856100564412485655)
  ·
    refine ⟨5918254284150846618728483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3945502856100564412485655 5918254284150846618728483)
    ·
      refine ⟨8877381426226269928092725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918254284150846618728483 8877381426226269928092725)
      ·
        refine ⟨832254508708712805758693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8877381426226269928092725 832254508708712805758693)
        ·
          refine ⟨156047720382883651079755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 832254508708712805758693 156047720382883651079755)
          ·
            refine ⟨234071580574325476619633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156047720382883651079755 234071580574325476619633)
            ·
              refine ⟨175553685430744107464725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234071580574325476619633 175553685430744107464725)
              ·
                refine ⟨8229079004566130037409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175553685430744107464725 8229079004566130037409)
                ·
                  rfl

theorem cell22_216352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_216352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216352 prefixEnd_216352 := by exact prefixLift 216352
  have htrace : WordTrace (prefixWord ++ tailWord_216352) baseStart_216352 baseEnd_216352 := by
    simpa [prefixWord, tailWord_216352, baseEnd_216352] using wordTrace_append hprefix tailTrace_216352
  have hstable : (prefixWord ++ tailWord_216352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216352).length < 2 ^ (prefixWord ++ tailWord_216352).sum := by decide
  have hdescent : baseEnd_216352 < baseStart_216352 := by decide
  rcases family_descends (prefixWord ++ tailWord_216352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216390 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_216390 : Nat := 118140960795 + 216390 * 2 ^ 59
def prefixEnd_216390 : Nat := 4983230072969 + 3 ^ 40 * 216390 * 2
def baseEnd_216390 : Nat := 74074719217675737886565

theorem tailTrace_216390 : CollatzResearch.WordTrace tailWord_216390 prefixEnd_216390 74074719217675737886565 := by
  unfold tailWord_216390
  simp only [CollatzResearch.WordTrace]
  refine ⟨246637240189483166089207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5261594457375640876569749 246637240189483166089207)
  ·
    refine ⟨369955860284224749133811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246637240189483166089207 369955860284224749133811)
    ·
      refine ⟨554933790426337123700717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369955860284224749133811 554933790426337123700717)
      ·
        refine ⟨208100171409876421387769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554933790426337123700717 208100171409876421387769)
        ·
          refine ⟨156075128557407316040827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208100171409876421387769 156075128557407316040827)
          ·
            refine ⟨234112692836110974061241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156075128557407316040827 234112692836110974061241)
            ·
              refine ⟨175584519627083230545931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234112692836110974061241 175584519627083230545931)
              ·
                refine ⟨263376779440624845818897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175584519627083230545931 263376779440624845818897)
                ·
                  refine ⟨197532584580468634364173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263376779440624845818897 197532584580468634364173)
                  ·
                    refine ⟨74074719217675737886565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197532584580468634364173 74074719217675737886565)
                    ·
                      rfl

theorem cell22_216390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_216390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216390 prefixEnd_216390 := by exact prefixLift 216390
  have htrace : WordTrace (prefixWord ++ tailWord_216390) baseStart_216390 baseEnd_216390 := by
    simpa [prefixWord, tailWord_216390, baseEnd_216390] using wordTrace_append hprefix tailTrace_216390
  have hstable : (prefixWord ++ tailWord_216390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216390).length < 2 ^ (prefixWord ++ tailWord_216390).sum := by decide
  have hdescent : baseEnd_216390 < baseStart_216390 := by decide
  rcases family_descends (prefixWord ++ tailWord_216390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216410 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_216410 : Nat := 118140960795 + 216410 * 2 ^ 59
def prefixEnd_216410 : Nat := 4983230072969 + 3 ^ 40 * 216410 * 2
def baseEnd_216410 : Nat := 74081565626402352386503

theorem tailTrace_216410 : CollatzResearch.WordTrace tailWord_216410 prefixEnd_216410 74081565626402352386503 := by
  unfold tailWord_216410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973280286497751182645671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5262080763994003153721789 1973280286497751182645671)
  ·
    refine ⟨2959920429746626773968507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973280286497751182645671 2959920429746626773968507)
    ·
      refine ⟨4439880644619940160952761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959920429746626773968507 4439880644619940160952761)
      ·
        refine ⟨3329910483464955120714571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4439880644619940160952761 3329910483464955120714571)
        ·
          refine ⟨4994865725197432681071857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329910483464955120714571 4994865725197432681071857)
          ·
            refine ⟨3746149293898074510803893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4994865725197432681071857 3746149293898074510803893)
            ·
              refine ⟨351201496302944485387865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3746149293898074510803893 351201496302944485387865)
              ·
                refine ⟨263401122227208364040899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351201496302944485387865 263401122227208364040899)
                ·
                  refine ⟨395101683340812546061349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263401122227208364040899 395101683340812546061349)
                  ·
                    refine ⟨74081565626402352386503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395101683340812546061349 74081565626402352386503)
                    ·
                      rfl

theorem cell22_216410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_216410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216410 prefixEnd_216410 := by exact prefixLift 216410
  have htrace : WordTrace (prefixWord ++ tailWord_216410) baseStart_216410 baseEnd_216410 := by
    simpa [prefixWord, tailWord_216410, baseEnd_216410] using wordTrace_append hprefix tailTrace_216410
  have hstable : (prefixWord ++ tailWord_216410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216410).length < 2 ^ (prefixWord ++ tailWord_216410).sum := by decide
  have hdescent : baseEnd_216410 < baseStart_216410 := by decide
  rcases family_descends (prefixWord ++ tailWord_216410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216453 : List Nat := [1, 3, 1, 1, 3, 1, 5, 7]
def baseStart_216453 : Nat := 118140960795 + 216453 * 2 ^ 59
def prefixEnd_216453 : Nat := 4983230072969 + 3 ^ 40 * 216453 * 2
def baseEnd_216453 : Nat := 8232920600573841506819

theorem tailTrace_216453 : CollatzResearch.WordTrace tailWord_216453 prefixEnd_216453 8232920600573841506819 := by
  unfold tailWord_216453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894689484835223074398013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5263126323223482049598675 7894689484835223074398013)
  ·
    refine ⟨2960508556813208652899255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7894689484835223074398013 2960508556813208652899255)
    ·
      refine ⟨4440762835219812979348883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960508556813208652899255 4440762835219812979348883)
      ·
        refine ⟨6661144252829719469023325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440762835219812979348883 6661144252829719469023325)
        ·
          refine ⟨2497929094811144800883747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6661144252829719469023325 2497929094811144800883747)
          ·
            refine ⟨3746893642216717201325621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497929094811144800883747 3746893642216717201325621)
            ·
              refine ⟨351271278957817237624277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3746893642216717201325621 351271278957817237624277)
              ·
                refine ⟨8232920600573841506819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 351271278957817237624277 8232920600573841506819)
                ·
                  rfl

theorem cell22_216453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 7].length) (baseStart_216453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216453 prefixEnd_216453 := by exact prefixLift 216453
  have htrace : WordTrace (prefixWord ++ tailWord_216453) baseStart_216453 baseEnd_216453 := by
    simpa [prefixWord, tailWord_216453, baseEnd_216453] using wordTrace_append hprefix tailTrace_216453
  have hstable : (prefixWord ++ tailWord_216453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216453).length < 2 ^ (prefixWord ++ tailWord_216453).sum := by decide
  have hdescent : baseEnd_216453 < baseStart_216453 := by decide
  rcases family_descends (prefixWord ++ tailWord_216453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216478 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_216478 : Nat := 118140960795 + 216478 * 2 ^ 59
def prefixEnd_216478 : Nat := 4983230072969 + 3 ^ 40 * 216478 * 2
def baseEnd_216478 : Nat := 74104843416072841686295

theorem tailTrace_216478 : CollatzResearch.WordTrace tailWord_216478 prefixEnd_216478 74104843416072841686295 := by
  unfold tailWord_216478
  simp only [CollatzResearch.WordTrace]
  refine ⟨986950163718081543007261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5263734206496434896038725 986950163718081543007261)
  ·
    refine ⟨370106311394280578627723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 986950163718081543007261 370106311394280578627723)
    ·
      refine ⟨555159467091420867941585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370106311394280578627723 555159467091420867941585)
      ·
        refine ⟨416369600318565650956189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555159467091420867941585 416369600318565650956189)
        ·
          refine ⟨156138600119462119108571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416369600318565650956189 156138600119462119108571)
          ·
            refine ⟨234207900179193178662857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156138600119462119108571 234207900179193178662857)
            ·
              refine ⟨175655925134394883997143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234207900179193178662857 175655925134394883997143)
              ·
                refine ⟨263483887701592325995715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175655925134394883997143 263483887701592325995715)
                ·
                  refine ⟨395225831552388488993573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263483887701592325995715 395225831552388488993573)
                  ·
                    refine ⟨74104843416072841686295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395225831552388488993573 74104843416072841686295)
                    ·
                      rfl

theorem cell22_216478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_216478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216478 prefixEnd_216478 := by exact prefixLift 216478
  have htrace : WordTrace (prefixWord ++ tailWord_216478) baseStart_216478 baseEnd_216478 := by
    simpa [prefixWord, tailWord_216478, baseEnd_216478] using wordTrace_append hprefix tailTrace_216478
  have hstable : (prefixWord ++ tailWord_216478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216478).length < 2 ^ (prefixWord ++ tailWord_216478).sum := by decide
  have hdescent : baseEnd_216478 < baseStart_216478 := by decide
  rcases family_descends (prefixWord ++ tailWord_216478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216560 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_216560 : Nat := 118140960795 + 216560 * 2 ^ 59
def prefixEnd_216560 : Nat := 4983230072969 + 3 ^ 40 * 216560 * 2
def baseEnd_216560 : Nat := 24710971230617320378681

theorem tailTrace_216560 : CollatzResearch.WordTrace tailWord_216560 prefixEnd_216560 24710971230617320378681 := by
  unfold tailWord_216560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949296047723790174271567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5265728063631720232362089 3949296047723790174271567)
  ·
    refine ⟨5923944071585685261407351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949296047723790174271567 5923944071585685261407351)
    ·
      refine ⟨8885916107378527892111027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5923944071585685261407351 8885916107378527892111027)
      ·
        refine ⟨13328874161067791838166541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8885916107378527892111027 13328874161067791838166541)
        ·
          refine ⟨4998327810400421939312453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13328874161067791838166541 4998327810400421939312453)
          ·
            refine ⟨937186464450079113621085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4998327810400421939312453 937186464450079113621085)
            ·
              refine ⟨351444924168779667607907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937186464450079113621085 351444924168779667607907)
              ·
                refine ⟨527167386253169501411861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351444924168779667607907 527167386253169501411861)
                ·
                  refine ⟨24710971230617320378681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 527167386253169501411861 24710971230617320378681)
                  ·
                    rfl

theorem cell22_216560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_216560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216560 prefixEnd_216560 := by exact prefixLift 216560
  have htrace : WordTrace (prefixWord ++ tailWord_216560) baseStart_216560 baseEnd_216560 := by
    simpa [prefixWord, tailWord_216560, baseEnd_216560] using wordTrace_append hprefix tailTrace_216560
  have hstable : (prefixWord ++ tailWord_216560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216560).length < 2 ^ (prefixWord ++ tailWord_216560).sum := by decide
  have hdescent : baseEnd_216560 < baseStart_216560 := by decide
  rcases family_descends (prefixWord ++ tailWord_216560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216575 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 6, 3]
def baseStart_216575 : Nat := 118140960795 + 216575 * 2 ^ 59
def prefixEnd_216575 : Nat := 4983230072969 + 3 ^ 40 * 216575 * 2
def baseEnd_216575 : Nat := 74138048498396922010997

theorem tailTrace_216575 : CollatzResearch.WordTrace tailWord_216575 prefixEnd_216575 74138048498396922010997 := by
  unfold tailWord_216575
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899139190393237910339179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5266092793595491940226119 7899139190393237910339179)
  ·
    refine ⟨11848708785589856865508769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7899139190393237910339179 11848708785589856865508769)
    ·
      refine ⟨8886531589192392649131577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11848708785589856865508769 8886531589192392649131577)
      ·
        refine ⟨6664898691894294486848683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8886531589192392649131577 6664898691894294486848683)
        ·
          refine ⟨9997348037841441730273025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664898691894294486848683 9997348037841441730273025)
          ·
            refine ⟨7498011028381081297704769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9997348037841441730273025 7498011028381081297704769)
            ·
              refine ⟨5623508271285810973278577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498011028381081297704769 5623508271285810973278577)
              ·
                refine ⟨4217631203464358229958933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623508271285810973278577 4217631203464358229958933)
                ·
                  refine ⟨197701462662391792029325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4217631203464358229958933 197701462662391792029325)
                  ·
                    refine ⟨74138048498396922010997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197701462662391792029325 74138048498396922010997)
                    ·
                      rfl

theorem cell22_216575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_216575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216575 prefixEnd_216575 := by exact prefixLift 216575
  have htrace : WordTrace (prefixWord ++ tailWord_216575) baseStart_216575 baseEnd_216575 := by
    simpa [prefixWord, tailWord_216575, baseEnd_216575] using wordTrace_append hprefix tailTrace_216575
  have hstable : (prefixWord ++ tailWord_216575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216575).length < 2 ^ (prefixWord ++ tailWord_216575).sum := by decide
  have hdescent : baseEnd_216575 < baseStart_216575 := by decide
  rcases family_descends (prefixWord ++ tailWord_216575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216609 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_216609 : Nat := 118140960795 + 216609 * 2 ^ 59
def prefixEnd_216609 : Nat := 4983230072969 + 3 ^ 40 * 216609 * 2
def baseEnd_216609 : Nat := 74149687393232166660893

theorem tailTrace_216609 : CollatzResearch.WordTrace tailWord_216609 prefixEnd_216609 74149687393232166660893 := by
  unfold tailWord_216609
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900379272270061717076881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5266919514846707811384587 7900379272270061717076881)
  ·
    refine ⟨5925284454202546287807661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7900379272270061717076881 5925284454202546287807661)
    ·
      refine ⟨2221981670325954857927873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5925284454202546287807661 2221981670325954857927873)
      ·
        refine ⟨1666486252744466143445905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221981670325954857927873 1666486252744466143445905)
        ·
          refine ⟨1249864689558349607584429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666486252744466143445905 1249864689558349607584429)
          ·
            refine ⟨468699258584381102844161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1249864689558349607584429 468699258584381102844161)
            ·
              refine ⟨351524443938285827133121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468699258584381102844161 351524443938285827133121)
              ·
                refine ⟨263643332953714370349841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351524443938285827133121 263643332953714370349841)
                ·
                  refine ⟨197732499715285777762381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263643332953714370349841 197732499715285777762381)
                  ·
                    refine ⟨74149687393232166660893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197732499715285777762381 74149687393232166660893)
                    ·
                      rfl

theorem cell22_216609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_216609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216609 prefixEnd_216609 := by exact prefixLift 216609
  have htrace : WordTrace (prefixWord ++ tailWord_216609) baseStart_216609 baseEnd_216609 := by
    simpa [prefixWord, tailWord_216609, baseEnd_216609] using wordTrace_append hprefix tailTrace_216609
  have hstable : (prefixWord ++ tailWord_216609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216609).length < 2 ^ (prefixWord ++ tailWord_216609).sum := by decide
  have hdescent : baseEnd_216609 < baseStart_216609 := by decide
  rcases family_descends (prefixWord ++ tailWord_216609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216611 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 4]
def baseStart_216611 : Nat := 118140960795 + 216611 * 2 ^ 59
def prefixEnd_216611 : Nat := 4983230072969 + 3 ^ 40 * 216611 * 2
def baseEnd_216611 : Nat := 24716790678034942703629

theorem tailTrace_216611 : CollatzResearch.WordTrace tailWord_216611 prefixEnd_216611 24716790678034942703629 := by
  unfold tailWord_216611
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900452218262816058649687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5266968145508544039099791 7900452218262816058649687)
  ·
    refine ⟨11850678327394224087974531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7900452218262816058649687 11850678327394224087974531)
    ·
      refine ⟨17776017491091336131961797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11850678327394224087974531 17776017491091336131961797)
      ·
        refine ⟨3333003279579625524742837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17776017491091336131961797 3333003279579625524742837)
        ·
          refine ⟨312469057460589892944641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3333003279579625524742837 312469057460589892944641)
          ·
            refine ⟨234351793095442419708481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312469057460589892944641 234351793095442419708481)
            ·
              refine ⟨175763844821581814781361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234351793095442419708481 175763844821581814781361)
              ·
                refine ⟨131822883616186361086021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175763844821581814781361 131822883616186361086021)
                ·
                  refine ⟨24716790678034942703629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131822883616186361086021 24716790678034942703629)
                  ·
                    rfl

theorem cell22_216611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 4].length) (baseStart_216611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216611 prefixEnd_216611 := by exact prefixLift 216611
  have htrace : WordTrace (prefixWord ++ tailWord_216611) baseStart_216611 baseEnd_216611 := by
    simpa [prefixWord, tailWord_216611, baseEnd_216611] using wordTrace_append hprefix tailTrace_216611
  have hstable : (prefixWord ++ tailWord_216611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216611).length < 2 ^ (prefixWord ++ tailWord_216611).sum := by decide
  have hdescent : baseEnd_216611 < baseStart_216611 := by decide
  rcases family_descends (prefixWord ++ tailWord_216611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216622 : List Nat := [4, 1, 3, 1, 2, 1, 3, 7]
def baseStart_216622 : Nat := 118140960795 + 216622 * 2 ^ 59
def prefixEnd_216622 : Nat := 4983230072969 + 3 ^ 40 * 216622 * 2
def baseEnd_216622 : Nat := 8239348617656051787317

theorem tailTrace_216622 : CollatzResearch.WordTrace tailWord_216622 prefixEnd_216622 8239348617656051787317 := by
  unfold tailWord_216622
  simp only [CollatzResearch.WordTrace]
  refine ⟨987606677652870617162515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5267235614148643291533413 987606677652870617162515)
  ·
    refine ⟨1481410016479305925743773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987606677652870617162515 1481410016479305925743773)
    ·
      refine ⟨555528756179739722153915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1481410016479305925743773 555528756179739722153915)
      ·
        refine ⟨833293134269609583230873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555528756179739722153915 833293134269609583230873)
        ·
          refine ⟨624969850702207187423155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833293134269609583230873 624969850702207187423155)
          ·
            refine ⟨937454776053310781134733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624969850702207187423155 937454776053310781134733)
            ·
              refine ⟨351545541019991542925525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937454776053310781134733 351545541019991542925525)
              ·
                refine ⟨8239348617656051787317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 351545541019991542925525 8239348617656051787317)
                ·
                  rfl

theorem cell22_216622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_216622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216622 prefixEnd_216622 := by exact prefixLift 216622
  have htrace : WordTrace (prefixWord ++ tailWord_216622) baseStart_216622 baseEnd_216622 := by
    simpa [prefixWord, tailWord_216622, baseEnd_216622] using wordTrace_append hprefix tailTrace_216622
  have hstable : (prefixWord ++ tailWord_216622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216622).length < 2 ^ (prefixWord ++ tailWord_216622).sum := by decide
  have hdescent : baseEnd_216622 < baseStart_216622 := by decide
  rcases family_descends (prefixWord ++ tailWord_216622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216650 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_216650 : Nat := 118140960795 + 216650 * 2 ^ 59
def prefixEnd_216650 : Nat := 4983230072969 + 3 ^ 40 * 216650 * 2
def baseEnd_216650 : Nat := 24721240843707242128589

theorem tailTrace_216650 : CollatzResearch.WordTrace tailWord_216650 prefixEnd_216650 24721240843707242128589 := by
  unfold tailWord_216650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975468666280381429829851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5267916443414350479546269 1975468666280381429829851)
  ·
    refine ⟨2963202999420572144744777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975468666280381429829851 2963202999420572144744777)
    ·
      refine ⟨2222402249565429108558583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2963202999420572144744777 2222402249565429108558583)
      ·
        refine ⟨3333603374348143662837875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222402249565429108558583 3333603374348143662837875)
        ·
          refine ⟨5000405061522215494256813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333603374348143662837875 5000405061522215494256813)
          ·
            refine ⟨1875151898070830810346305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5000405061522215494256813 1875151898070830810346305)
            ·
              refine ⟨1406363923553123107759729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875151898070830810346305 1406363923553123107759729)
              ·
                refine ⟨1054772942664842330819797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406363923553123107759729 1054772942664842330819797)
                ·
                  refine ⟨24721240843707242128589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1054772942664842330819797 24721240843707242128589)
                  ·
                    rfl

theorem cell22_216650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_216650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216650 prefixEnd_216650 := by exact prefixLift 216650
  have htrace : WordTrace (prefixWord ++ tailWord_216650) baseStart_216650 baseEnd_216650 := by
    simpa [prefixWord, tailWord_216650, baseEnd_216650] using wordTrace_append hprefix tailTrace_216650
  have hstable : (prefixWord ++ tailWord_216650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216650).length < 2 ^ (prefixWord ++ tailWord_216650).sum := by decide
  have hdescent : baseEnd_216650 < baseStart_216650 := by decide
  rcases family_descends (prefixWord ++ tailWord_216650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216682 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_216682 : Nat := 118140960795 + 216682 * 2 ^ 59
def prefixEnd_216682 : Nat := 4983230072969 + 3 ^ 40 * 216682 * 2
def baseEnd_216682 : Nat := 74174676785084309585669

theorem tailTrace_216682 : CollatzResearch.WordTrace tailWord_216682 prefixEnd_216682 74174676785084309585669 := by
  unfold tailWord_216682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975760450251398796121075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5268694534003730122989533 1975760450251398796121075)
  ·
    refine ⟨2963640675377098194181613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975760450251398796121075 2963640675377098194181613)
    ·
      refine ⟨1111365253266411822818105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2963640675377098194181613 1111365253266411822818105)
      ·
        refine ⟨833523939949808867113579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1111365253266411822818105 833523939949808867113579)
        ·
          refine ⟨1250285909924713300670369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833523939949808867113579 1250285909924713300670369)
          ·
            refine ⟨937714432443534975502777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1250285909924713300670369 937714432443534975502777)
            ·
              refine ⟨703285824332651231627083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937714432443534975502777 703285824332651231627083)
              ·
                refine ⟨1054928736498976847440625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703285824332651231627083 1054928736498976847440625)
                ·
                  refine ⟨791196552374232635580469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054928736498976847440625 791196552374232635580469)
                  ·
                    refine ⟨74174676785084309585669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 791196552374232635580469 74174676785084309585669)
                    ·
                      rfl

theorem cell22_216682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_216682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216682 prefixEnd_216682 := by exact prefixLift 216682
  have htrace : WordTrace (prefixWord ++ tailWord_216682) baseStart_216682 baseEnd_216682 := by
    simpa [prefixWord, tailWord_216682, baseEnd_216682] using wordTrace_append hprefix tailTrace_216682
  have hstable : (prefixWord ++ tailWord_216682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216682).length < 2 ^ (prefixWord ++ tailWord_216682).sum := by decide
  have hdescent : baseEnd_216682 < baseStart_216682 := by decide
  rcases family_descends (prefixWord ++ tailWord_216682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216714 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_216714 : Nat := 118140960795 + 216714 * 2 ^ 59
def prefixEnd_216714 : Nat := 4983230072969 + 3 ^ 40 * 216714 * 2
def baseEnd_216714 : Nat := 74185631039046892785571

theorem tailTrace_216714 : CollatzResearch.WordTrace tailWord_216714 prefixEnd_216714 74185631039046892785571 := by
  unfold tailWord_216714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976052234222416162412299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5269472624593109766432797 1976052234222416162412299)
  ·
    refine ⟨2964078351333624243618449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1976052234222416162412299 2964078351333624243618449)
    ·
      refine ⟨2223058763500218182713837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2964078351333624243618449 2223058763500218182713837)
      ·
        refine ⟨833647036312581818517689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2223058763500218182713837 833647036312581818517689)
        ·
          refine ⟨625235277234436363888267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833647036312581818517689 625235277234436363888267)
          ·
            refine ⟨937852915851654545832401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625235277234436363888267 937852915851654545832401)
            ·
              refine ⟨703389686888740909374301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937852915851654545832401 703389686888740909374301)
              ·
                refine ⟨263771132583277841015363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703389686888740909374301 263771132583277841015363)
                ·
                  refine ⟨395656698874916761523045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263771132583277841015363 395656698874916761523045)
                  ·
                    refine ⟨74185631039046892785571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395656698874916761523045 74185631039046892785571)
                    ·
                      rfl

theorem cell22_216714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_216714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216714 prefixEnd_216714 := by exact prefixLift 216714
  have htrace : WordTrace (prefixWord ++ tailWord_216714) baseStart_216714 baseEnd_216714 := by
    simpa [prefixWord, tailWord_216714, baseEnd_216714] using wordTrace_append hprefix tailTrace_216714
  have hstable : (prefixWord ++ tailWord_216714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216714).length < 2 ^ (prefixWord ++ tailWord_216714).sum := by decide
  have hdescent : baseEnd_216714 < baseStart_216714 := by decide
  rcases family_descends (prefixWord ++ tailWord_216714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216759 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 2, 4]
def baseStart_216759 : Nat := 118140960795 + 216759 * 2 ^ 59
def prefixEnd_216759 : Nat := 4983230072969 + 3 ^ 40 * 216759 * 2
def baseEnd_216759 : Nat := 74201035458681775410433

theorem tailTrace_216759 : CollatzResearch.WordTrace tailWord_216759 prefixEnd_216759 74201035458681775410433 := by
  unfold tailWord_216759
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905850221726637335037331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5270566814484424890024887 7905850221726637335037331)
  ·
    refine ⟨11858775332589956002555997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7905850221726637335037331 11858775332589956002555997)
    ·
      refine ⟨4447040749721233500958499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11858775332589956002555997 4447040749721233500958499)
      ·
        refine ⟨6670561124581850251437749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447040749721233500958499 6670561124581850251437749)
        ·
          refine ⟨625365105429548461072289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6670561124581850251437749 625365105429548461072289)
          ·
            refine ⟨469023829072161345804217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625365105429548461072289 469023829072161345804217)
            ·
              refine ⟨351767871804121009353163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469023829072161345804217 351767871804121009353163)
              ·
                refine ⟨527651807706181514029745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351767871804121009353163 527651807706181514029745)
                ·
                  refine ⟨395738855779636135522309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527651807706181514029745 395738855779636135522309)
                  ·
                    refine ⟨74201035458681775410433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395738855779636135522309 74201035458681775410433)
                    ·
                      rfl

theorem cell22_216759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_216759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216759 prefixEnd_216759 := by exact prefixLift 216759
  have htrace : WordTrace (prefixWord ++ tailWord_216759) baseStart_216759 baseEnd_216759 := by
    simpa [prefixWord, tailWord_216759, baseEnd_216759] using wordTrace_append hprefix tailTrace_216759
  have hstable : (prefixWord ++ tailWord_216759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216759).length < 2 ^ (prefixWord ++ tailWord_216759).sum := by decide
  have hdescent : baseEnd_216759 < baseStart_216759 := by decide
  rcases family_descends (prefixWord ++ tailWord_216759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216780 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 4]
def baseStart_216780 : Nat := 118140960795 + 216780 * 2 ^ 59
def prefixEnd_216780 : Nat := 4983230072969 + 3 ^ 40 * 216780 * 2
def baseEnd_216780 : Nat := 24736074729281573545123

theorem tailTrace_216780 : CollatzResearch.WordTrace tailWord_216780 prefixEnd_216780 24736074729281573545123 := by
  unfold tailWord_216780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953308077325278960775897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5271077436433705281034529 3953308077325278960775897)
  ·
    refine ⟨2964981057993959220581923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3953308077325278960775897 2964981057993959220581923)
    ·
      refine ⟨4447471586990938830872885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964981057993959220581923 4447471586990938830872885)
      ·
        refine ⟨416950461280400515394333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4447471586990938830872885 416950461280400515394333)
        ·
          refine ⟨156356422980150193272875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416950461280400515394333 156356422980150193272875)
          ·
            refine ⟨234534634470225289909313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156356422980150193272875 234534634470225289909313)
            ·
              refine ⟨175900975852668967431985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234534634470225289909313 175900975852668967431985)
              ·
                refine ⟨131925731889501725573989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175900975852668967431985 131925731889501725573989)
                ·
                  refine ⟨24736074729281573545123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131925731889501725573989 24736074729281573545123)
                  ·
                    rfl

theorem cell22_216780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_216780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216780 prefixEnd_216780 := by exact prefixLift 216780
  have htrace : WordTrace (prefixWord ++ tailWord_216780) baseStart_216780 baseEnd_216780 := by
    simpa [prefixWord, tailWord_216780, baseEnd_216780] using wordTrace_append hprefix tailTrace_216780
  have hstable : (prefixWord ++ tailWord_216780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216780).length < 2 ^ (prefixWord ++ tailWord_216780).sum := by decide
  have hdescent : baseEnd_216780 < baseStart_216780 := by decide
  rcases family_descends (prefixWord ++ tailWord_216780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216834 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_216834 : Nat := 118140960795 + 216834 * 2 ^ 59
def prefixEnd_216834 : Nat := 4983230072969 + 3 ^ 40 * 216834 * 2
def baseEnd_216834 : Nat := 74226709491406579785203

theorem tailTrace_216834 : CollatzResearch.WordTrace tailWord_216834 prefixEnd_216834 74226709491406579785203 := by
  unfold tailWord_216834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977146424113731286004389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5272390464303283429345037 1977146424113731286004389)
  ·
    refine ⟨370714954521324616125823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1977146424113731286004389 370714954521324616125823)
    ·
      refine ⟨556072431781986924188735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370714954521324616125823 556072431781986924188735)
      ·
        refine ⟨834108647672980386283103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556072431781986924188735 834108647672980386283103)
        ·
          refine ⟨1251162971509470579424655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834108647672980386283103 1251162971509470579424655)
          ·
            refine ⟨1876744457264205869136983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251162971509470579424655 1876744457264205869136983)
            ·
              refine ⟨2815116685896308803705475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876744457264205869136983 2815116685896308803705475)
              ·
                refine ⟨4222675028844463205558213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815116685896308803705475 4222675028844463205558213)
                ·
                  refine ⟨791751567908336851042165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4222675028844463205558213 791751567908336851042165)
                  ·
                    refine ⟨74226709491406579785203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 791751567908336851042165 74226709491406579785203)
                    ·
                      rfl

theorem cell22_216834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_216834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216834 prefixEnd_216834 := by exact prefixLift 216834
  have htrace : WordTrace (prefixWord ++ tailWord_216834) baseStart_216834 baseEnd_216834 := by
    simpa [prefixWord, tailWord_216834, baseEnd_216834] using wordTrace_append hprefix tailTrace_216834
  have hstable : (prefixWord ++ tailWord_216834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216834).length < 2 ^ (prefixWord ++ tailWord_216834).sum := by decide
  have hdescent : baseEnd_216834 < baseStart_216834 := by decide
  rcases family_descends (prefixWord ++ tailWord_216834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216836 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 5]
def baseStart_216836 : Nat := 118140960795 + 216836 * 2 ^ 59
def prefixEnd_216836 : Nat := 4983230072969 + 3 ^ 40 * 216836 * 2
def baseEnd_216836 : Nat := 24742464710759747078399

theorem tailTrace_216836 : CollatzResearch.WordTrace tailWord_216836 prefixEnd_216836 24742464710759747078399 := by
  unfold tailWord_216836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954329321223839742795181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5272439094965119657060241 3954329321223839742795181)
  ·
    refine ⟨1482873495458939903548193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3954329321223839742795181 1482873495458939903548193)
    ·
      refine ⟨1112155121594204927661145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1482873495458939903548193 1112155121594204927661145)
      ·
        refine ⟨834116341195653695745859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1112155121594204927661145 834116341195653695745859)
        ·
          refine ⟨1251174511793480543618789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834116341195653695745859 1251174511793480543618789)
          ·
            refine ⟨234595220961277601928523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1251174511793480543618789 234595220961277601928523)
            ·
              refine ⟨351892831441916402892785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234595220961277601928523 351892831441916402892785)
              ·
                refine ⟨263919623581437302169589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351892831441916402892785 263919623581437302169589)
                ·
                  refine ⟨24742464710759747078399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263919623581437302169589 24742464710759747078399)
                  ·
                    rfl

theorem cell22_216836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_216836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216836 prefixEnd_216836 := by exact prefixLift 216836
  have htrace : WordTrace (prefixWord ++ tailWord_216836) baseStart_216836 baseEnd_216836 := by
    simpa [prefixWord, tailWord_216836, baseEnd_216836] using wordTrace_append hprefix tailTrace_216836
  have hstable : (prefixWord ++ tailWord_216836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216836).length < 2 ^ (prefixWord ++ tailWord_216836).sum := by decide
  have hdescent : baseEnd_216836 < baseStart_216836 := by decide
  rcases family_descends (prefixWord ++ tailWord_216836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216866 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_216866 : Nat := 118140960795 + 216866 * 2 ^ 59
def prefixEnd_216866 : Nat := 4983230072969 + 3 ^ 40 * 216866 * 2
def baseEnd_216866 : Nat := 74237663745369162985105

theorem tailTrace_216866 : CollatzResearch.WordTrace tailWord_216866 prefixEnd_216866 74237663745369162985105 := by
  unfold tailWord_216866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977438208084748652295613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5273168554892663072788301 1977438208084748652295613)
  ·
    refine ⟨741539328031780744610855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1977438208084748652295613 741539328031780744610855)
    ·
      refine ⟨1112308992047671116916283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741539328031780744610855 1112308992047671116916283)
      ·
        refine ⟨1668463488071506675374425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112308992047671116916283 1668463488071506675374425)
        ·
          refine ⟨1251347616053630006530819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668463488071506675374425 1251347616053630006530819)
          ·
            refine ⟨1877021424080445009796229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251347616053630006530819 1877021424080445009796229)
            ·
              refine ⟨351941517015083439336793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1877021424080445009796229 351941517015083439336793)
              ·
                refine ⟨263956137761312579502595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351941517015083439336793 263956137761312579502595)
                ·
                  refine ⟨395934206641968869253893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263956137761312579502595 395934206641968869253893)
                  ·
                    refine ⟨74237663745369162985105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395934206641968869253893 74237663745369162985105)
                    ·
                      rfl

theorem cell22_216866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_216866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216866 prefixEnd_216866 := by exact prefixLift 216866
  have htrace : WordTrace (prefixWord ++ tailWord_216866) baseStart_216866 baseEnd_216866 := by
    simpa [prefixWord, tailWord_216866, baseEnd_216866] using wordTrace_append hprefix tailTrace_216866
  have hstable : (prefixWord ++ tailWord_216866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216866).length < 2 ^ (prefixWord ++ tailWord_216866).sum := by decide
  have hdescent : baseEnd_216866 < baseStart_216866 := by decide
  rcases family_descends (prefixWord ++ tailWord_216866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216881 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 4]
def baseStart_216881 : Nat := 118140960795 + 216881 * 2 ^ 59
def prefixEnd_216881 : Nat := 4983230072969 + 3 ^ 40 * 216881 * 2
def baseEnd_216881 : Nat := 24747599517304707953353

theorem tailTrace_216881 : CollatzResearch.WordTrace tailWord_216881 prefixEnd_216881 24747599517304707953353 := by
  unfold tailWord_216881
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910299927284652170978497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5273533284856434780652331 7910299927284652170978497)
  ·
    refine ⟨5932724945463489128233873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7910299927284652170978497 5932724945463489128233873)
    ·
      refine ⟨4449543709097616846175405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5932724945463489128233873 4449543709097616846175405)
      ·
        refine ⟨1668578890911606317315777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4449543709097616846175405 1668578890911606317315777)
        ·
          refine ⟨1251434168183704737986833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668578890911606317315777 1251434168183704737986833)
          ·
            refine ⟨938575626137778553490125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1251434168183704737986833 938575626137778553490125)
            ·
              refine ⟨351965859801666957558797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 938575626137778553490125 351965859801666957558797)
              ·
                refine ⟨131987197425625109084549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351965859801666957558797 131987197425625109084549)
                ·
                  refine ⟨24747599517304707953353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131987197425625109084549 24747599517304707953353)
                  ·
                    rfl

theorem cell22_216881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_216881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216881 prefixEnd_216881 := by exact prefixLift 216881
  have htrace : WordTrace (prefixWord ++ tailWord_216881) baseStart_216881 baseEnd_216881 := by
    simpa [prefixWord, tailWord_216881, baseEnd_216881] using wordTrace_append hprefix tailTrace_216881
  have hstable : (prefixWord ++ tailWord_216881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216881).length < 2 ^ (prefixWord ++ tailWord_216881).sum := by decide
  have hdescent : baseEnd_216881 < baseStart_216881 := by decide
  rcases family_descends (prefixWord ++ tailWord_216881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216892 : List Nat := [2, 2, 2, 2, 1, 1, 12]
def baseStart_216892 : Nat := 118140960795 + 216892 * 2 ^ 59
def prefixEnd_216892 : Nat := 4983230072969 + 3 ^ 40 * 216892 * 2
def baseEnd_216892 : Nat := 2749872743581991179075

theorem tailTrace_216892 : CollatzResearch.WordTrace tailWord_216892 prefixEnd_216892 2749872743581991179075 := by
  unfold tailWord_216892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955350565122400524814465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5273800753496534033085953 3955350565122400524814465)
  ·
    refine ⟨2966512923841800393610849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955350565122400524814465 2966512923841800393610849)
    ·
      refine ⟨2224884692881350295208137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2966512923841800393610849 2224884692881350295208137)
      ·
        refine ⟨1668663519661012721406103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224884692881350295208137 1668663519661012721406103)
        ·
          refine ⟨2502995279491519082109155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668663519661012721406103 2502995279491519082109155)
          ·
            refine ⟨3754492919237278623163733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502995279491519082109155 3754492919237278623163733)
            ·
              refine ⟨2749872743581991179075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 3754492919237278623163733 2749872743581991179075)
              ·
                rfl

theorem cell22_216892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 12].length) (baseStart_216892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216892 prefixEnd_216892 := by exact prefixLift 216892
  have htrace : WordTrace (prefixWord ++ tailWord_216892) baseStart_216892 baseEnd_216892 := by
    simpa [prefixWord, tailWord_216892, baseEnd_216892] using wordTrace_append hprefix tailTrace_216892
  have hstable : (prefixWord ++ tailWord_216892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216892).length < 2 ^ (prefixWord ++ tailWord_216892).sum := by decide
  have hdescent : baseEnd_216892 < baseStart_216892 := by decide
  rcases family_descends (prefixWord ++ tailWord_216892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216913 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 2, 3]
def baseStart_216913 : Nat := 118140960795 + 216913 * 2 ^ 59
def prefixEnd_216913 : Nat := 4983230072969 + 3 ^ 40 * 216913 * 2
def baseEnd_216913 : Nat := 74253752805876707059961

theorem tailTrace_216913 : CollatzResearch.WordTrace tailWord_216913 prefixEnd_216913 74253752805876707059961 := by
  unfold tailWord_216913
  simp only [CollatzResearch.WordTrace]
  refine ⟨7911467063168721636143393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5274311375445814424095595 7911467063168721636143393)
  ·
    refine ⟨5933600297376541227107545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7911467063168721636143393 5933600297376541227107545)
    ·
      refine ⟨4450200223032405920330659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5933600297376541227107545 4450200223032405920330659)
      ·
        refine ⟨6675300334548608880495989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450200223032405920330659 6675300334548608880495989)
        ·
          refine ⟨625809406363932082546499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6675300334548608880495989 625809406363932082546499)
          ·
            refine ⟨938714109545898123819749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625809406363932082546499 938714109545898123819749)
            ·
              refine ⟨176008895539855898216203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 938714109545898123819749 176008895539855898216203)
              ·
                refine ⟨264013343309783847324305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176008895539855898216203 264013343309783847324305)
                ·
                  refine ⟨198010007482337885493229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264013343309783847324305 198010007482337885493229)
                  ·
                    refine ⟨74253752805876707059961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198010007482337885493229 74253752805876707059961)
                    ·
                      rfl

theorem cell22_216913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_216913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216913 prefixEnd_216913 := by exact prefixLift 216913
  have htrace : WordTrace (prefixWord ++ tailWord_216913) baseStart_216913 baseEnd_216913 := by
    simpa [prefixWord, tailWord_216913, baseEnd_216913] using wordTrace_append hprefix tailTrace_216913
  have hstable : (prefixWord ++ tailWord_216913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216913).length < 2 ^ (prefixWord ++ tailWord_216913).sum := by decide
  have hdescent : baseEnd_216913 < baseStart_216913 := by decide
  rcases family_descends (prefixWord ++ tailWord_216913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216937 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 9]
def baseStart_216937 : Nat := 118140960795 + 216937 * 2 ^ 59
def prefixEnd_216937 : Nat := 4983230072969 + 3 ^ 40 * 216937 * 2
def baseEnd_216937 : Nat := 24753989498782881486629

theorem tailTrace_216937 : CollatzResearch.WordTrace tailWord_216937 prefixEnd_216937 24753989498782881486629 := by
  unfold tailWord_216937
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912342415081773735017065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5274894943387849156678043 7912342415081773735017065)
  ·
    refine ⟨5934256811311330301262799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7912342415081773735017065 5934256811311330301262799)
    ·
      refine ⟨8901385216966995451894199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934256811311330301262799 8901385216966995451894199)
      ·
        refine ⟨13352077825450493177841299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8901385216966995451894199 13352077825450493177841299)
        ·
          refine ⟨20028116738175739766761949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13352077825450493177841299 20028116738175739766761949)
          ·
            refine ⟨7510543776815902412535731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20028116738175739766761949 7510543776815902412535731)
            ·
              refine ⟨11265815665223853618803597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510543776815902412535731 11265815665223853618803597)
              ·
                refine ⟨4224680874458945107051349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11265815665223853618803597 4224680874458945107051349)
                ·
                  refine ⟨24753989498782881486629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4224680874458945107051349 24753989498782881486629)
                  ·
                    rfl

theorem cell22_216937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_216937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216937 prefixEnd_216937 := by exact prefixLift 216937
  have htrace : WordTrace (prefixWord ++ tailWord_216937) baseStart_216937 baseEnd_216937 := by
    simpa [prefixWord, tailWord_216937, baseEnd_216937] using wordTrace_append hprefix tailTrace_216937
  have hstable : (prefixWord ++ tailWord_216937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216937).length < 2 ^ (prefixWord ++ tailWord_216937).sum := by decide
  have hdescent : baseEnd_216937 < baseStart_216937 := by decide
  rcases family_descends (prefixWord ++ tailWord_216937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216954 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_216954 : Nat := 118140960795 + 216954 * 2 ^ 59
def prefixEnd_216954 : Nat := 4983230072969 + 3 ^ 40 * 216954 * 2
def baseEnd_216954 : Nat := 24755929314588755594945

theorem tailTrace_216954 : CollatzResearch.WordTrace tailWord_216954 prefixEnd_216954 24755929314588755594945 := by
  unfold tailWord_216954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978240614005046409596479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5275308304013457092257277 1978240614005046409596479)
  ·
    refine ⟨2967360921007569614394719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978240614005046409596479 2967360921007569614394719)
    ·
      refine ⟨4451041381511354421592079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967360921007569614394719 4451041381511354421592079)
      ·
        refine ⟨6676562072267031632388119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451041381511354421592079 6676562072267031632388119)
        ·
          refine ⟨10014843108400547448582179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676562072267031632388119 10014843108400547448582179)
          ·
            refine ⟨15022264662600821172873269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10014843108400547448582179 15022264662600821172873269)
            ·
              refine ⟨1408337312118826984956869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15022264662600821172873269 1408337312118826984956869)
              ·
                refine ⟨264063246022280059679413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1408337312118826984956869 264063246022280059679413)
                ·
                  refine ⟨24755929314588755594945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264063246022280059679413 24755929314588755594945)
                  ·
                    rfl

theorem cell22_216954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_216954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216954 prefixEnd_216954 := by exact prefixLift 216954
  have htrace : WordTrace (prefixWord ++ tailWord_216954) baseStart_216954 baseEnd_216954 := by
    simpa [prefixWord, tailWord_216954, baseEnd_216954] using wordTrace_append hprefix tailTrace_216954
  have hstable : (prefixWord ++ tailWord_216954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216954).length < 2 ^ (prefixWord ++ tailWord_216954).sum := by decide
  have hdescent : baseEnd_216954 < baseStart_216954 := by decide
  rcases family_descends (prefixWord ++ tailWord_216954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216969 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_216969 : Nat := 118140960795 + 216969 * 2 ^ 59
def prefixEnd_216969 : Nat := 4983230072969 + 3 ^ 40 * 216969 * 2
def baseEnd_216969 : Nat := 74272922750311227659789

theorem tailTrace_216969 : CollatzResearch.WordTrace tailWord_216969 prefixEnd_216969 74272922750311227659789 := by
  unfold tailWord_216969
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913509550965843200181961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5275673033977228800121307 7913509550965843200181961)
  ·
    refine ⟨5935132163224382400136471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7913509550965843200181961 5935132163224382400136471)
    ·
      refine ⟨8902698244836573600204707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935132163224382400136471 8902698244836573600204707)
      ·
        refine ⟨13354047367254860400307061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8902698244836573600204707 13354047367254860400307061)
        ·
          refine ⟨1251941940680143162528787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13354047367254860400307061 1251941940680143162528787)
          ·
            refine ⟨1877912911020214743793181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251941940680143162528787 1877912911020214743793181)
            ·
              refine ⟨704217341632580528922443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1877912911020214743793181 704217341632580528922443)
              ·
                refine ⟨1056326012448870793383665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704217341632580528922443 1056326012448870793383665)
                ·
                  refine ⟨792244509336653095037749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056326012448870793383665 792244509336653095037749)
                  ·
                    refine ⟨74272922750311227659789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 792244509336653095037749 74272922750311227659789)
                    ·
                      rfl

theorem cell22_216969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_216969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_216969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_216969 prefixEnd_216969 := by exact prefixLift 216969
  have htrace : WordTrace (prefixWord ++ tailWord_216969) baseStart_216969 baseEnd_216969 := by
    simpa [prefixWord, tailWord_216969, baseEnd_216969] using wordTrace_append hprefix tailTrace_216969
  have hstable : (prefixWord ++ tailWord_216969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216969).length < 2 ^ (prefixWord ++ tailWord_216969).sum := by decide
  have hdescent : baseEnd_216969 < baseStart_216969 := by decide
  rcases family_descends (prefixWord ++ tailWord_216969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217016 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 4]
def baseStart_217016 : Nat := 118140960795 + 217016 * 2 ^ 59
def prefixEnd_217016 : Nat := 4983230072969 + 3 ^ 40 * 217016 * 2
def baseEnd_217016 : Nat := 24763003936939590578215

theorem tailTrace_217016 : CollatzResearch.WordTrace tailWord_217016 prefixEnd_217016 24763003936939590578215 := by
  unfold tailWord_217016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957611890897785113571451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5276815854530380151428601 3957611890897785113571451)
  ·
    refine ⟨5936417836346677670357177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3957611890897785113571451 5936417836346677670357177)
    ·
      refine ⟨4452313377260008252767883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5936417836346677670357177 4452313377260008252767883)
      ·
        refine ⟨6678470065890012379151825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452313377260008252767883 6678470065890012379151825)
        ·
          refine ⟨5008852549417509284363869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6678470065890012379151825 5008852549417509284363869)
          ·
            refine ⟨1878319706031565981636451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5008852549417509284363869 1878319706031565981636451)
            ·
              refine ⟨2817479559047348972454677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878319706031565981636451 2817479559047348972454677)
              ·
                refine ⟨132069354330344483083813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2817479559047348972454677 132069354330344483083813)
                ·
                  refine ⟨24763003936939590578215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132069354330344483083813 24763003936939590578215)
                  ·
                    rfl

theorem cell22_217016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_217016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217016 prefixEnd_217016 := by exact prefixLift 217016
  have htrace : WordTrace (prefixWord ++ tailWord_217016) baseStart_217016 baseEnd_217016 := by
    simpa [prefixWord, tailWord_217016, baseEnd_217016] using wordTrace_append hprefix tailTrace_217016
  have hstable : (prefixWord ++ tailWord_217016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217016).length < 2 ^ (prefixWord ++ tailWord_217016).sum := by decide
  have hdescent : baseEnd_217016 < baseStart_217016 := by decide
  rcases family_descends (prefixWord ++ tailWord_217016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217029 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_217029 : Nat := 118140960795 + 217029 * 2 ^ 59
def prefixEnd_217029 : Nat := 4983230072969 + 3 ^ 40 * 217029 * 2
def baseEnd_217029 : Nat := 74293461976491071159605

theorem tailTrace_217029 : CollatzResearch.WordTrace tailWord_217029 prefixEnd_217029 74293461976491071159605 := by
  unfold tailWord_217029
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915697930748473447366141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5277131953832315631577427 7915697930748473447366141)
  ·
    refine ⟨2968386724030677542762303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7915697930748473447366141 2968386724030677542762303)
    ·
      refine ⟨4452580086046016314143455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968386724030677542762303 4452580086046016314143455)
      ·
        refine ⟨6678870129069024471215183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452580086046016314143455 6678870129069024471215183)
        ·
          refine ⟨10018305193603536706822775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6678870129069024471215183 10018305193603536706822775)
          ·
            refine ⟨15027457790405305060234163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018305193603536706822775 15027457790405305060234163)
            ·
              refine ⟨22541186685607957590351245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15027457790405305060234163 22541186685607957590351245)
              ·
                refine ⟨8452945007102984096381717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22541186685607957590351245 8452945007102984096381717)
                ·
                  refine ⟨396231797207952379517893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8452945007102984096381717 396231797207952379517893)
                  ·
                    refine ⟨74293461976491071159605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396231797207952379517893 74293461976491071159605)
                    ·
                      rfl

theorem cell22_217029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_217029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217029 prefixEnd_217029 := by exact prefixLift 217029
  have htrace : WordTrace (prefixWord ++ tailWord_217029) baseStart_217029 baseEnd_217029 := by
    simpa [prefixWord, tailWord_217029, baseEnd_217029] using wordTrace_append hprefix tailTrace_217029
  have hstable : (prefixWord ++ tailWord_217029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217029).length < 2 ^ (prefixWord ++ tailWord_217029).sum := by decide
  have hdescent : baseEnd_217029 < baseStart_217029 := by decide
  rcases family_descends (prefixWord ++ tailWord_217029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217050 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_217050 : Nat := 118140960795 + 217050 * 2 ^ 59
def prefixEnd_217050 : Nat := 4983230072969 + 3 ^ 40 * 217050 * 2
def baseEnd_217050 : Nat := 24766883568551338794847

theorem tailTrace_217050 : CollatzResearch.WordTrace tailWord_217050 prefixEnd_217050 24766883568551338794847 := by
  unfold tailWord_217050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979115965918098508470151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5277642575781596022587069 1979115965918098508470151)
  ·
    refine ⟨2968673948877147762705227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1979115965918098508470151 2968673948877147762705227)
    ·
      refine ⟨4453010923315721644057841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968673948877147762705227 4453010923315721644057841)
      ·
        refine ⟨3339758192486791233043381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4453010923315721644057841 3339758192486791233043381)
        ·
          refine ⟨313102330545636678097817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3339758192486791233043381 313102330545636678097817)
          ·
            refine ⟨234826747909227508573363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313102330545636678097817 234826747909227508573363)
            ·
              refine ⟨352240121863841262860045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234826747909227508573363 352240121863841262860045)
              ·
                refine ⟨132090045698940473572517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352240121863841262860045 132090045698940473572517)
                ·
                  refine ⟨24766883568551338794847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132090045698940473572517 24766883568551338794847)
                  ·
                    rfl

theorem cell22_217050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_217050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217050 prefixEnd_217050 := by exact prefixLift 217050
  have htrace : WordTrace (prefixWord ++ tailWord_217050) baseStart_217050 baseEnd_217050 := by
    simpa [prefixWord, tailWord_217050, baseEnd_217050] using wordTrace_append hprefix tailTrace_217050
  have hstable : (prefixWord ++ tailWord_217050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217050).length < 2 ^ (prefixWord ++ tailWord_217050).sum := by decide
  have hdescent : baseEnd_217050 < baseStart_217050 := by decide
  rcases family_descends (prefixWord ++ tailWord_217050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217063 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 2, 4]
def baseStart_217063 : Nat := 118140960795 + 217063 * 2 ^ 59
def prefixEnd_217063 : Nat := 4983230072969 + 3 ^ 40 * 217063 * 2
def baseEnd_217063 : Nat := 74305100871326315809501

theorem tailTrace_217063 : CollatzResearch.WordTrace tailWord_217063 prefixEnd_217063 74305100871326315809501 := by
  unfold tailWord_217063
  simp only [CollatzResearch.WordTrace]
  refine ⟨7916938012625297254103843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5277958675083531502735895 7916938012625297254103843)
  ·
    refine ⟨11875407018937945881155765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7916938012625297254103843 11875407018937945881155765)
    ·
      refine ⟨1113319408025432426358353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11875407018937945881155765 1113319408025432426358353)
      ·
        refine ⟨834989556019074319768765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1113319408025432426358353 834989556019074319768765)
        ·
          refine ⟨313121083507152869913287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 834989556019074319768765 313121083507152869913287)
          ·
            refine ⟨469681625260729304869931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313121083507152869913287 469681625260729304869931)
            ·
              refine ⟨704522437891093957304897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469681625260729304869931 704522437891093957304897)
              ·
                refine ⟨528391828418320467978673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704522437891093957304897 528391828418320467978673)
                ·
                  refine ⟨396293871313740350984005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528391828418320467978673 396293871313740350984005)
                  ·
                    refine ⟨74305100871326315809501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396293871313740350984005 74305100871326315809501)
                    ·
                      rfl

theorem cell22_217063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_217063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217063 prefixEnd_217063 := by exact prefixLift 217063
  have htrace : WordTrace (prefixWord ++ tailWord_217063) baseStart_217063 baseEnd_217063 := by
    simpa [prefixWord, tailWord_217063, baseEnd_217063] using wordTrace_append hprefix tailTrace_217063
  have hstable : (prefixWord ++ tailWord_217063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217063).length < 2 ^ (prefixWord ++ tailWord_217063).sum := by decide
  have hdescent : baseEnd_217063 < baseStart_217063 := by decide
  rcases family_descends (prefixWord ++ tailWord_217063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217078 : List Nat := [5, 1, 1, 1, 4, 1, 2, 7]
def baseStart_217078 : Nat := 118140960795 + 217078 * 2 ^ 59
def prefixEnd_217078 : Nat := 4983230072969 + 3 ^ 40 * 217078 * 2
def baseEnd_217078 : Nat := 8256692853096808520495

theorem tailTrace_217078 : CollatzResearch.WordTrace tailWord_217078 prefixEnd_217078 8256692853096808520495 := by
  unfold tailWord_217078
  simp only [CollatzResearch.WordTrace]
  refine ⟨494842819223184675993743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5278323405047303210599925 494842819223184675993743)
  ·
    refine ⟨742264228834777013990615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494842819223184675993743 742264228834777013990615)
    ·
      refine ⟨1113396343252165520985923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742264228834777013990615 1113396343252165520985923)
      ·
        refine ⟨1670094514878248281478885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113396343252165520985923 1670094514878248281478885)
        ·
          refine ⟨313142721539671552777291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1670094514878248281478885 313142721539671552777291)
          ·
            refine ⟨469714082309507329165937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313142721539671552777291 469714082309507329165937)
            ·
              refine ⟨352285561732130496874453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469714082309507329165937 352285561732130496874453)
              ·
                refine ⟨8256692853096808520495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 352285561732130496874453 8256692853096808520495)
                ·
                  rfl

theorem cell22_217078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_217078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217078 prefixEnd_217078 := by exact prefixLift 217078
  have htrace : WordTrace (prefixWord ++ tailWord_217078) baseStart_217078 baseEnd_217078 := by
    simpa [prefixWord, tailWord_217078, baseEnd_217078] using wordTrace_append hprefix tailTrace_217078
  have hstable : (prefixWord ++ tailWord_217078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217078).length < 2 ^ (prefixWord ++ tailWord_217078).sum := by decide
  have hdescent : baseEnd_217078 < baseStart_217078 := by decide
  rcases family_descends (prefixWord ++ tailWord_217078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217104 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_217104 : Nat := 118140960795 + 217104 * 2 ^ 59
def prefixEnd_217104 : Nat := 4983230072969 + 3 ^ 40 * 217104 * 2
def baseEnd_217104 : Nat := 74319136009215875534375

theorem tailTrace_217104 : CollatzResearch.WordTrace tailWord_217104 prefixEnd_217104 74319136009215875534375 := by
  unfold tailWord_217104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959216702738380628173183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5278955603651174170897577 3959216702738380628173183)
  ·
    refine ⟨5938825054107570942259775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959216702738380628173183 5938825054107570942259775)
    ·
      refine ⟨8908237581161356413389663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5938825054107570942259775 8908237581161356413389663)
      ·
        refine ⟨13362356371742034620084495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908237581161356413389663 13362356371742034620084495)
        ·
          refine ⟨20043534557613051930126743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13362356371742034620084495 20043534557613051930126743)
          ·
            refine ⟨30065301836419577895190115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20043534557613051930126743 30065301836419577895190115)
            ·
              refine ⟨45097952754629366842785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30065301836419577895190115 45097952754629366842785173)
              ·
                refine ⟨2113966535373251570755555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45097952754629366842785173 2113966535373251570755555)
                ·
                  refine ⟨3170949803059877356133333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113966535373251570755555 3170949803059877356133333)
                  ·
                    refine ⟨74319136009215875534375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3170949803059877356133333 74319136009215875534375)
                    ·
                      rfl

theorem cell22_217104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_217104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217104 prefixEnd_217104 := by exact prefixLift 217104
  have htrace : WordTrace (prefixWord ++ tailWord_217104) baseStart_217104 baseEnd_217104 := by
    simpa [prefixWord, tailWord_217104, baseEnd_217104] using wordTrace_append hprefix tailTrace_217104
  have hstable : (prefixWord ++ tailWord_217104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217104).length < 2 ^ (prefixWord ++ tailWord_217104).sum := by decide
  have hdescent : baseEnd_217104 < baseStart_217104 := by decide
  rcases family_descends (prefixWord ++ tailWord_217104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217136 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_217136 : Nat := 118140960795 + 217136 * 2 ^ 59
def prefixEnd_217136 : Nat := 4983230072969 + 3 ^ 40 * 217136 * 2
def baseEnd_217136 : Nat := 74330090263178458734277

theorem tailTrace_217136 : CollatzResearch.WordTrace tailWord_217136 prefixEnd_217136 74330090263178458734277 := by
  unfold tailWord_217136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959800270680415360755631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5279733694240553814340841 3959800270680415360755631)
  ·
    refine ⟨5939700406020623041133447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959800270680415360755631 5939700406020623041133447)
    ·
      refine ⟨8909550609030934561700171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5939700406020623041133447 8909550609030934561700171)
      ·
        refine ⟨13364325913546401842550257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8909550609030934561700171 13364325913546401842550257)
        ·
          refine ⟨10023244435159801381912693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13364325913546401842550257 10023244435159801381912693)
          ·
            refine ⟨939679165796231379554315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10023244435159801381912693 939679165796231379554315)
            ·
              refine ⟨1409518748694347069331473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939679165796231379554315 1409518748694347069331473)
              ·
                refine ⟨1057139061520760301998605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409518748694347069331473 1057139061520760301998605)
                ·
                  refine ⟨396427148070285113249477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057139061520760301998605 396427148070285113249477)
                  ·
                    refine ⟨74330090263178458734277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396427148070285113249477 74330090263178458734277)
                    ·
                      rfl

theorem cell22_217136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_217136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217136 prefixEnd_217136 := by exact prefixLift 217136
  have htrace : WordTrace (prefixWord ++ tailWord_217136) baseStart_217136 baseEnd_217136 := by
    simpa [prefixWord, tailWord_217136, baseEnd_217136] using wordTrace_append hprefix tailTrace_217136
  have hstable : (prefixWord ++ tailWord_217136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217136).length < 2 ^ (prefixWord ++ tailWord_217136).sum := by decide
  have hdescent : baseEnd_217136 < baseStart_217136 := by decide
  rcases family_descends (prefixWord ++ tailWord_217136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217153 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_217153 : Nat := 118140960795 + 217153 * 2 ^ 59
def prefixEnd_217153 : Nat := 4983230072969 + 3 ^ 40 * 217153 * 2
def baseEnd_217153 : Nat := 74335909710596081059225

theorem tailTrace_217153 : CollatzResearch.WordTrace tailWord_217153 prefixEnd_217153 74335909710596081059225 := by
  unfold tailWord_217153
  simp only [CollatzResearch.WordTrace]
  refine ⟨7920220582299242624880113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5280147054866161749920075 7920220582299242624880113)
  ·
    refine ⟨5940165436724431968660085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7920220582299242624880113 5940165436724431968660085)
    ·
      refine ⟨556890509692915497061883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5940165436724431968660085 556890509692915497061883)
      ·
        refine ⟨835335764539373245592825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556890509692915497061883 835335764539373245592825)
        ·
          refine ⟨626501823404529934194619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835335764539373245592825 626501823404529934194619)
          ·
            refine ⟨939752735106794901291929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626501823404529934194619 939752735106794901291929)
            ·
              refine ⟨704814551330096175968947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939752735106794901291929 704814551330096175968947)
              ·
                refine ⟨1057221826995144263953421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704814551330096175968947 1057221826995144263953421)
                ·
                  refine ⟨396458185123179098982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057221826995144263953421 396458185123179098982533)
                  ·
                    refine ⟨74335909710596081059225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396458185123179098982533 74335909710596081059225)
                    ·
                      rfl

theorem cell22_217153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_217153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217153 prefixEnd_217153 := by exact prefixLift 217153
  have htrace : WordTrace (prefixWord ++ tailWord_217153) baseStart_217153 baseEnd_217153 := by
    simpa [prefixWord, tailWord_217153, baseEnd_217153] using wordTrace_append hprefix tailTrace_217153
  have hstable : (prefixWord ++ tailWord_217153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217153).length < 2 ^ (prefixWord ++ tailWord_217153).sum := by decide
  have hdescent : baseEnd_217153 < baseStart_217153 := by decide
  rcases family_descends (prefixWord ++ tailWord_217153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217170 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_217170 : Nat := 118140960795 + 217170 * 2 ^ 59
def prefixEnd_217170 : Nat := 4983230072969 + 3 ^ 40 * 217170 * 2
def baseEnd_217170 : Nat := 74341729158013703384173

theorem tailTrace_217170 : CollatzResearch.WordTrace tailWord_217170 prefixEnd_217170 74341729158013703384173 := by
  unfold tailWord_217170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980210155809413632062241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5280560415491769685499309 1980210155809413632062241)
  ·
    refine ⟨1485157616857060224046681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1980210155809413632062241 1485157616857060224046681)
    ·
      refine ⟨1113868212642795168035011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485157616857060224046681 1113868212642795168035011)
      ·
        refine ⟨1670802318964192752052517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113868212642795168035011 1670802318964192752052517)
        ·
          refine ⟨313275434805786141009847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1670802318964192752052517 313275434805786141009847)
          ·
            refine ⟨469913152208679211514771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313275434805786141009847 469913152208679211514771)
            ·
              refine ⟨704869728313018817272157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469913152208679211514771 704869728313018817272157)
              ·
                refine ⟨264326148117382056477059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704869728313018817272157 264326148117382056477059)
                ·
                  refine ⟨396489222176073084715589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264326148117382056477059 396489222176073084715589)
                  ·
                    refine ⟨74341729158013703384173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396489222176073084715589 74341729158013703384173)
                    ·
                      rfl

theorem cell22_217170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_217170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217170 prefixEnd_217170 := by exact prefixLift 217170
  have htrace : WordTrace (prefixWord ++ tailWord_217170) baseStart_217170 baseEnd_217170 := by
    simpa [prefixWord, tailWord_217170, baseEnd_217170] using wordTrace_append hprefix tailTrace_217170
  have hstable : (prefixWord ++ tailWord_217170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217170).length < 2 ^ (prefixWord ++ tailWord_217170).sum := by decide
  have hdescent : baseEnd_217170 < baseStart_217170 := by decide
  rcases family_descends (prefixWord ++ tailWord_217170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217183 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 2, 3]
def baseStart_217183 : Nat := 118140960795 + 217183 * 2 ^ 59
def prefixEnd_217183 : Nat := 4983230072969 + 3 ^ 40 * 217183 * 2
def baseEnd_217183 : Nat := 74346179323686002809133

theorem tailTrace_217183 : CollatzResearch.WordTrace tailWord_217183 prefixEnd_217183 74346179323686002809133 := by
  unfold tailWord_217183
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921314772190557748472203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5280876514793705165648135 7921314772190557748472203)
  ·
    refine ⟨11881972158285836622708305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7921314772190557748472203 11881972158285836622708305)
    ·
      refine ⟨8911479118714377467031229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11881972158285836622708305 8911479118714377467031229)
      ·
        refine ⟨3341804669517891550136711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8911479118714377467031229 3341804669517891550136711)
        ·
          refine ⟨5012707004276837325205067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341804669517891550136711 5012707004276837325205067)
          ·
            refine ⟨7519060506415255987807601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012707004276837325205067 7519060506415255987807601)
            ·
              refine ⟨5639295379811441990855701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7519060506415255987807601 5639295379811441990855701)
              ·
                refine ⟨264341970928661343321361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5639295379811441990855701 264341970928661343321361)
                ·
                  refine ⟨198256478196496007491021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264341970928661343321361 198256478196496007491021)
                  ·
                    refine ⟨74346179323686002809133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198256478196496007491021 74346179323686002809133)
                    ·
                      rfl

theorem cell22_217183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_217183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217183 prefixEnd_217183 := by exact prefixLift 217183
  have htrace : WordTrace (prefixWord ++ tailWord_217183) baseStart_217183 baseEnd_217183 := by
    simpa [prefixWord, tailWord_217183, baseEnd_217183] using wordTrace_append hprefix tailTrace_217183
  have hstable : (prefixWord ++ tailWord_217183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217183).length < 2 ^ (prefixWord ++ tailWord_217183).sum := by decide
  have hdescent : baseEnd_217183 < baseStart_217183 := by decide
  rcases family_descends (prefixWord ++ tailWord_217183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217213 : List Nat := [1, 4, 1, 1, 3, 2, 4, 6]
def baseStart_217213 : Nat := 118140960795 + 217213 * 2 ^ 59
def prefixEnd_217213 : Nat := 4983230072969 + 3 ^ 40 * 217213 * 2
def baseEnd_217213 : Nat := 8261827659641769395449

theorem tailTrace_217213 : CollatzResearch.WordTrace tailWord_217213 prefixEnd_217213 8261827659641769395449 := by
  unfold tailWord_217213
  simp only [CollatzResearch.WordTrace]
  refine ⟨7922408962081872872064293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5281605974721248581376195 7922408962081872872064293)
  ·
    refine ⟨1485451680390351163512055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7922408962081872872064293 1485451680390351163512055)
    ·
      refine ⟨2228177520585526745268083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485451680390351163512055 2228177520585526745268083)
      ·
        refine ⟨3342266280878290117902125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228177520585526745268083 3342266280878290117902125)
        ·
          refine ⟨1253349855329358794213297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3342266280878290117902125 1253349855329358794213297)
          ·
            refine ⟨940012391497019095659973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253349855329358794213297 940012391497019095659973)
            ·
              refine ⟨176252323405691080436245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 940012391497019095659973 176252323405691080436245)
              ·
                refine ⟨8261827659641769395449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176252323405691080436245 8261827659641769395449)
                ·
                  rfl

theorem cell22_217213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 6].length) (baseStart_217213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217213 prefixEnd_217213 := by exact prefixLift 217213
  have htrace : WordTrace (prefixWord ++ tailWord_217213) baseStart_217213 baseEnd_217213 := by
    simpa [prefixWord, tailWord_217213, baseEnd_217213] using wordTrace_append hprefix tailTrace_217213
  have hstable : (prefixWord ++ tailWord_217213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217213).length < 2 ^ (prefixWord ++ tailWord_217213).sum := by decide
  have hdescent : baseEnd_217213 < baseStart_217213 := by decide
  rcases family_descends (prefixWord ++ tailWord_217213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217230 : List Nat := [4, 1, 1, 3, 4, 1, 8]
def baseStart_217230 : Nat := 118140960795 + 217230 * 2 ^ 59
def prefixEnd_217230 : Nat := 4983230072969 + 3 ^ 40 * 217230 * 2
def baseEnd_217230 : Nat := 2754158088303464699407

theorem tailTrace_217230 : CollatzResearch.WordTrace tailWord_217230 prefixEnd_217230 2754158088303464699407 := by
  unfold tailWord_217230
  simp only [CollatzResearch.WordTrace]
  refine ⟨990378625377535596929143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5282019335346856516955429 990378625377535596929143)
  ·
    refine ⟨1485567938066303395393715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990378625377535596929143 1485567938066303395393715)
    ·
      refine ⟨2228351907099455093090573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485567938066303395393715 2228351907099455093090573)
      ·
        refine ⟨835631965162295659908965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2228351907099455093090573 835631965162295659908965)
        ·
          refine ⟨156680993467930436232931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 835631965162295659908965 156680993467930436232931)
          ·
            refine ⟨235021490201895654349397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156680993467930436232931 235021490201895654349397)
            ·
              refine ⟨2754158088303464699407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 235021490201895654349397 2754158088303464699407)
              ·
                rfl

theorem cell22_217230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 8].length) (baseStart_217230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217230 prefixEnd_217230 := by exact prefixLift 217230
  have htrace : WordTrace (prefixWord ++ tailWord_217230) baseStart_217230 baseEnd_217230 := by
    simpa [prefixWord, tailWord_217230, baseEnd_217230] using wordTrace_append hprefix tailTrace_217230
  have hstable : (prefixWord ++ tailWord_217230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217230).length < 2 ^ (prefixWord ++ tailWord_217230).sum := by decide
  have hdescent : baseEnd_217230 < baseStart_217230 := by decide
  rcases family_descends (prefixWord ++ tailWord_217230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217245 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_217245 : Nat := 118140960795 + 217245 * 2 ^ 59
def prefixEnd_217245 : Nat := 4983230072969 + 3 ^ 40 * 217245 * 2
def baseEnd_217245 : Nat := 74367403190738507758943

theorem tailTrace_217245 : CollatzResearch.WordTrace tailWord_217245 prefixEnd_217245 74367403190738507758943 := by
  unfold tailWord_217245
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923576097965942337229189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5282384065310628224819459 7923576097965942337229189)
  ·
    refine ⟨1485670518368614188230473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7923576097965942337229189 1485670518368614188230473)
    ·
      refine ⟨1114252888776460641172855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485670518368614188230473 1114252888776460641172855)
      ·
        refine ⟨1671379333164690961759283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114252888776460641172855 1671379333164690961759283)
        ·
          refine ⟨2507068999747036442638925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671379333164690961759283 2507068999747036442638925)
          ·
            refine ⟨940150874905138665989597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2507068999747036442638925 940150874905138665989597)
            ·
              refine ⟨352556578089426999746099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 940150874905138665989597 352556578089426999746099)
              ·
                refine ⟨528834867134140499619149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352556578089426999746099 528834867134140499619149)
                ·
                  refine ⟨198313075175302687357181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528834867134140499619149 198313075175302687357181)
                  ·
                    refine ⟨74367403190738507758943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198313075175302687357181 74367403190738507758943)
                    ·
                      rfl

theorem cell22_217245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_217245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217245 prefixEnd_217245 := by exact prefixLift 217245
  have htrace : WordTrace (prefixWord ++ tailWord_217245) baseStart_217245 baseEnd_217245 := by
    simpa [prefixWord, tailWord_217245, baseEnd_217245] using wordTrace_append hprefix tailTrace_217245
  have hstable : (prefixWord ++ tailWord_217245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217245).length < 2 ^ (prefixWord ++ tailWord_217245).sum := by decide
  have hdescent : baseEnd_217245 < baseStart_217245 := by decide
  rcases family_descends (prefixWord ++ tailWord_217245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217292 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 5]
def baseStart_217292 : Nat := 118140960795 + 217292 * 2 ^ 59
def prefixEnd_217292 : Nat := 4983230072969 + 3 ^ 40 * 217292 * 2
def baseEnd_217292 : Nat := 24794497417082017277933

theorem tailTrace_217292 : CollatzResearch.WordTrace tailWord_217292 prefixEnd_217292 24794497417082017277933 := by
  unfold tailWord_217292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962645164397834682095065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5283526885863779576126753 3962645164397834682095065)
  ·
    refine ⟨2971983873298376011571299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3962645164397834682095065 2971983873298376011571299)
    ·
      refine ⟨4457975809947564017356949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971983873298376011571299 4457975809947564017356949)
      ·
        refine ⟨208967616091292063313607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4457975809947564017356949 208967616091292063313607)
        ·
          refine ⟨313451424136938094970411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208967616091292063313607 313451424136938094970411)
          ·
            refine ⟨470177136205407142455617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313451424136938094970411 470177136205407142455617)
            ·
              refine ⟨352632852154055356841713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470177136205407142455617 352632852154055356841713)
              ·
                refine ⟨264474639115541517631285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352632852154055356841713 264474639115541517631285)
                ·
                  refine ⟨24794497417082017277933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264474639115541517631285 24794497417082017277933)
                  ·
                    rfl

theorem cell22_217292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_217292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217292 prefixEnd_217292 := by exact prefixLift 217292
  have htrace : WordTrace (prefixWord ++ tailWord_217292) baseStart_217292 baseEnd_217292 := by
    simpa [prefixWord, tailWord_217292, baseEnd_217292] using wordTrace_append hprefix tailTrace_217292
  have hstable : (prefixWord ++ tailWord_217292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217292).length < 2 ^ (prefixWord ++ tailWord_217292).sum := by decide
  have hdescent : baseEnd_217292 < baseStart_217292 := by decide
  rcases family_descends (prefixWord ++ tailWord_217292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217352 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_217352 : Nat := 118140960795 + 217352 * 2 ^ 59
def prefixEnd_217352 : Nat := 4983230072969 + 3 ^ 40 * 217352 * 2
def baseEnd_217352 : Nat := 74404031477425895333615

theorem tailTrace_217352 : CollatzResearch.WordTrace tailWord_217352 prefixEnd_217352 74404031477425895333615 := by
  unfold tailWord_217352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963739354289149805687155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5284985805718866407582873 3963739354289149805687155)
  ·
    refine ⟨5945609031433724708530733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3963739354289149805687155 5945609031433724708530733)
    ·
      refine ⟨2229603386787646765699025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5945609031433724708530733 2229603386787646765699025)
      ·
        refine ⟨1672202540090735074274269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229603386787646765699025 1672202540090735074274269)
        ·
          refine ⟨627075952534025652852851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1672202540090735074274269 627075952534025652852851)
          ·
            refine ⟨940613928801038479279277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627075952534025652852851 940613928801038479279277)
            ·
              refine ⟨352730223300389429729729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 940613928801038479279277 352730223300389429729729)
              ·
                refine ⟨264547667475292072297297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352730223300389429729729 264547667475292072297297)
                ·
                  refine ⟨198410750606469054222973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264547667475292072297297 198410750606469054222973)
                  ·
                    refine ⟨74404031477425895333615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198410750606469054222973 74404031477425895333615)
                    ·
                      rfl

theorem cell22_217352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_217352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217352 prefixEnd_217352 := by exact prefixLift 217352
  have htrace : WordTrace (prefixWord ++ tailWord_217352) baseStart_217352 baseEnd_217352 := by
    simpa [prefixWord, tailWord_217352, baseEnd_217352] using wordTrace_append hprefix tailTrace_217352
  have hstable : (prefixWord ++ tailWord_217352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217352).length < 2 ^ (prefixWord ++ tailWord_217352).sum := by decide
  have hdescent : baseEnd_217352 < baseStart_217352 := by decide
  rcases family_descends (prefixWord ++ tailWord_217352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217408 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_217408 : Nat := 118140960795 + 217408 * 2 ^ 59
def prefixEnd_217408 : Nat := 4983230072969 + 3 ^ 40 * 217408 * 2
def baseEnd_217408 : Nat := 74423201421860415933443

theorem tailTrace_217408 : CollatzResearch.WordTrace tailWord_217408 prefixEnd_217408 74423201421860415933443 := by
  unfold tailWord_217408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964760598187710587706439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5286347464250280783608585 3964760598187710587706439)
  ·
    refine ⟨5947140897281565881559659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3964760598187710587706439 5947140897281565881559659)
    ·
      refine ⟨8920711345922348822339489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5947140897281565881559659 8920711345922348822339489)
      ·
        refine ⟨6690533509441761616754617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8920711345922348822339489 6690533509441761616754617)
        ·
          refine ⟨5017900132081321212565963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6690533509441761616754617 5017900132081321212565963)
          ·
            refine ⟨7526850198121981818848945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017900132081321212565963 7526850198121981818848945)
            ·
              refine ⟨5645137648591486364136709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526850198121981818848945 5645137648591486364136709)
              ·
                refine ⟨1058463309110903693275633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5645137648591486364136709 1058463309110903693275633)
                ·
                  refine ⟨793847481833177769956725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058463309110903693275633 793847481833177769956725)
                  ·
                    refine ⟨74423201421860415933443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 793847481833177769956725 74423201421860415933443)
                    ·
                      rfl

theorem cell22_217408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_217408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217408 prefixEnd_217408 := by exact prefixLift 217408
  have htrace : WordTrace (prefixWord ++ tailWord_217408) baseStart_217408 baseEnd_217408 := by
    simpa [prefixWord, tailWord_217408, baseEnd_217408] using wordTrace_append hprefix tailTrace_217408
  have hstable : (prefixWord ++ tailWord_217408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217408).length < 2 ^ (prefixWord ++ tailWord_217408).sum := by decide
  have hdescent : baseEnd_217408 < baseStart_217408 := by decide
  rcases family_descends (prefixWord ++ tailWord_217408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217517 : List Nat := [1, 5, 2, 2, 2, 1, 9]
def baseStart_217517 : Nat := 118140960795 + 217517 * 2 ^ 59
def prefixEnd_217517 : Nat := 4983230072969 + 3 ^ 40 * 217517 * 2
def baseEnd_217517 : Nat := 2757796827756313516967

theorem tailTrace_217517 : CollatzResearch.WordTrace tailWord_217517 prefixEnd_217517 2757796827756313516967 := by
  unfold tailWord_217517
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933496752980532791130805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5288997835320355194087203 7933496752980532791130805)
  ·
    refine ⟨743765320591924949168513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7933496752980532791130805 743765320591924949168513)
    ·
      refine ⟨557823990443943711876385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 743765320591924949168513 557823990443943711876385)
      ·
        refine ⟨418367992832957783907289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557823990443943711876385 418367992832957783907289)
        ·
          refine ⟨313775994624718337930467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418367992832957783907289 313775994624718337930467)
          ·
            refine ⟨470663991937077506895701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313775994624718337930467 470663991937077506895701)
            ·
              refine ⟨2757796827756313516967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 470663991937077506895701 2757796827756313516967)
              ·
                rfl

theorem cell22_217517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 9].length) (baseStart_217517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217517 prefixEnd_217517 := by exact prefixLift 217517
  have htrace : WordTrace (prefixWord ++ tailWord_217517) baseStart_217517 baseEnd_217517 := by
    simpa [prefixWord, tailWord_217517, baseEnd_217517] using wordTrace_append hprefix tailTrace_217517
  have hstable : (prefixWord ++ tailWord_217517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217517).length < 2 ^ (prefixWord ++ tailWord_217517).sum := by decide
  have hdescent : baseEnd_217517 < baseStart_217517 := by decide
  rcases family_descends (prefixWord ++ tailWord_217517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217545 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 5]
def baseStart_217545 : Nat := 118140960795 + 217545 * 2 ^ 59
def prefixEnd_217545 : Nat := 4983230072969 + 3 ^ 40 * 217545 * 2
def baseEnd_217545 : Nat := 24823366440545908419341

theorem tailTrace_217545 : CollatzResearch.WordTrace tailWord_217545 prefixEnd_217545 24823366440545908419341 := by
  unfold tailWord_217545
  simp only [CollatzResearch.WordTrace]
  refine ⟨7934517996879093573150089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5289678664586062382100059 7934517996879093573150089)
  ·
    refine ⟨5950888497659320179862567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7934517996879093573150089 5950888497659320179862567)
    ·
      refine ⟨8926332746488980269793851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950888497659320179862567 8926332746488980269793851)
      ·
        refine ⟨13389499119733470404690777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8926332746488980269793851 13389499119733470404690777)
        ·
          refine ⟨10042124339800102803518083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13389499119733470404690777 10042124339800102803518083)
          ·
            refine ⟨15063186509700154205277125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10042124339800102803518083 15063186509700154205277125)
            ·
              refine ⟨2824347470568778913489461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15063186509700154205277125 2824347470568778913489461)
              ·
                refine ⟨264782575365823023139637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2824347470568778913489461 264782575365823023139637)
                ·
                  refine ⟨24823366440545908419341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264782575365823023139637 24823366440545908419341)
                  ·
                    rfl

theorem cell22_217545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_217545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217545 prefixEnd_217545 := by exact prefixLift 217545
  have htrace : WordTrace (prefixWord ++ tailWord_217545) baseStart_217545 baseEnd_217545 := by
    simpa [prefixWord, tailWord_217545, baseEnd_217545] using wordTrace_append hprefix tailTrace_217545
  have hstable : (prefixWord ++ tailWord_217545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217545).length < 2 ^ (prefixWord ++ tailWord_217545).sum := by decide
  have hdescent : baseEnd_217545 < baseStart_217545 := by decide
  rcases family_descends (prefixWord ++ tailWord_217545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217635 : List Nat := [1, 1, 1, 4, 4, 11]
def baseStart_217635 : Nat := 118140960795 + 217635 * 2 ^ 59
def prefixEnd_217635 : Nat := 4983230072969 + 3 ^ 40 * 217635 * 2
def baseEnd_217635 : Nat := 919764298282808524787

theorem tailTrace_217635 : CollatzResearch.WordTrace tailWord_217635 prefixEnd_217635 919764298282808524787 := by
  unfold tailWord_217635
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937800566553038943926359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5291867044368692629284239 7937800566553038943926359)
  ·
    refine ⟨11906700849829558415889539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7937800566553038943926359 11906700849829558415889539)
    ·
      refine ⟨17860051274744337623834309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11906700849829558415889539 17860051274744337623834309)
      ·
        refine ⟨3348759614014563304468933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17860051274744337623834309 3348759614014563304468933)
        ·
          refine ⟨627892427627730619587925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3348759614014563304468933 627892427627730619587925)
          ·
            refine ⟨919764298282808524787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 627892427627730619587925 919764298282808524787)
            ·
              rfl

theorem cell22_217635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 11].length) (baseStart_217635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217635 prefixEnd_217635 := by exact prefixLift 217635
  have htrace : WordTrace (prefixWord ++ tailWord_217635) baseStart_217635 baseEnd_217635 := by
    simpa [prefixWord, tailWord_217635, baseEnd_217635] using wordTrace_append hprefix tailTrace_217635
  have hstable : (prefixWord ++ tailWord_217635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217635).length < 2 ^ (prefixWord ++ tailWord_217635).sum := by decide
  have hdescent : baseEnd_217635 < baseStart_217635 := by decide
  rcases family_descends (prefixWord ++ tailWord_217635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217637 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_217637 : Nat := 118140960795 + 217637 * 2 ^ 59
def prefixEnd_217637 : Nat := 4983230072969 + 3 ^ 40 * 217637 * 2
def baseEnd_217637 : Nat := 74501592801780151957741

theorem tailTrace_217637 : CollatzResearch.WordTrace tailWord_217637 prefixEnd_217637 74501592801780151957741 := by
  unfold tailWord_217637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937873512545793285499165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5291915675030528856999443 7937873512545793285499165)
  ·
    refine ⟨2976702567204672482062187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7937873512545793285499165 2976702567204672482062187)
    ·
      refine ⟨4465053850807008723093281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2976702567204672482062187 4465053850807008723093281)
      ·
        refine ⟨3348790388105256542319961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4465053850807008723093281 3348790388105256542319961)
        ·
          refine ⟨2511592791078942406739971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348790388105256542319961 2511592791078942406739971)
          ·
            refine ⟨3767389186618413610109957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511592791078942406739971 3767389186618413610109957)
            ·
              refine ⟨706385472490952551895617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3767389186618413610109957 706385472490952551895617)
              ·
                refine ⟨529789104368214413921713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706385472490952551895617 529789104368214413921713)
                ·
                  refine ⟨397341828276160810441285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529789104368214413921713 397341828276160810441285)
                  ·
                    refine ⟨74501592801780151957741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 397341828276160810441285 74501592801780151957741)
                    ·
                      rfl

theorem cell22_217637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_217637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217637 prefixEnd_217637 := by exact prefixLift 217637
  have htrace : WordTrace (prefixWord ++ tailWord_217637) baseStart_217637 baseEnd_217637 := by
    simpa [prefixWord, tailWord_217637, baseEnd_217637] using wordTrace_append hprefix tailTrace_217637
  have hstable : (prefixWord ++ tailWord_217637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217637).length < 2 ^ (prefixWord ++ tailWord_217637).sum := by decide
  have hdescent : baseEnd_217637 < baseStart_217637 := by decide
  rcases family_descends (prefixWord ++ tailWord_217637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217697 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 7]
def baseStart_217697 : Nat := 118140960795 + 217697 * 2 ^ 59
def prefixEnd_217697 : Nat := 4983230072969 + 3 ^ 40 * 217697 * 2
def baseEnd_217697 : Nat := 24840710675986665152519

theorem tailTrace_217697 : CollatzResearch.WordTrace tailWord_217697 prefixEnd_217697 24840710675986665152519 := by
  unfold tailWord_217697
  simp only [CollatzResearch.WordTrace]
  refine ⟨7940061892328423532683345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5293374594885615688455563 7940061892328423532683345)
  ·
    refine ⟨5955046419246317649512509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7940061892328423532683345 5955046419246317649512509)
    ·
      refine ⟨2233142407217369118567191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5955046419246317649512509 2233142407217369118567191)
      ·
        refine ⟨3349713610826053677850787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233142407217369118567191 3349713610826053677850787)
        ·
          refine ⟨5024570416239080516776181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349713610826053677850787 5024570416239080516776181)
          ·
            refine ⟨471053476522413798447767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5024570416239080516776181 471053476522413798447767)
            ·
              refine ⟨706580214783620697671651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471053476522413798447767 706580214783620697671651)
              ·
                refine ⟨1059870322175431046507477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706580214783620697671651 1059870322175431046507477)
                ·
                  refine ⟨24840710675986665152519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1059870322175431046507477 24840710675986665152519)
                  ·
                    rfl

theorem cell22_217697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_217697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217697 prefixEnd_217697 := by exact prefixLift 217697
  have htrace : WordTrace (prefixWord ++ tailWord_217697) baseStart_217697 baseEnd_217697 := by
    simpa [prefixWord, tailWord_217697, baseEnd_217697] using wordTrace_append hprefix tailTrace_217697
  have hstable : (prefixWord ++ tailWord_217697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217697).length < 2 ^ (prefixWord ++ tailWord_217697).sum := by decide
  have hdescent : baseEnd_217697 < baseStart_217697 := by decide
  rcases family_descends (prefixWord ++ tailWord_217697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217701 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_217701 : Nat := 118140960795 + 217701 * 2 ^ 59
def prefixEnd_217701 : Nat := 4983230072969 + 3 ^ 40 * 217701 * 2
def baseEnd_217701 : Nat := 74523501309705318357545

theorem tailTrace_217701 : CollatzResearch.WordTrace tailWord_217701 prefixEnd_217701 74523501309705318357545 := by
  unfold tailWord_217701
  simp only [CollatzResearch.WordTrace]
  refine ⟨7940207784313932215828957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5293471856209288143885971 7940207784313932215828957)
  ·
    refine ⟨2977577919117724580935859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7940207784313932215828957 2977577919117724580935859)
    ·
      refine ⟨4466366878676586871403789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977577919117724580935859 4466366878676586871403789)
      ·
        refine ⟨1674887579503720076776421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4466366878676586871403789 1674887579503720076776421)
        ·
          refine ⟨314041421156947514395579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1674887579503720076776421 314041421156947514395579)
          ·
            refine ⟨471062131735421271593369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314041421156947514395579 471062131735421271593369)
            ·
              refine ⟨353296598801565953695027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471062131735421271593369 353296598801565953695027)
              ·
                refine ⟨529944898202348930542541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353296598801565953695027 529944898202348930542541)
                ·
                  refine ⟨198729336825880848953453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529944898202348930542541 198729336825880848953453)
                  ·
                    refine ⟨74523501309705318357545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198729336825880848953453 74523501309705318357545)
                    ·
                      rfl

theorem cell22_217701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_217701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217701 prefixEnd_217701 := by exact prefixLift 217701
  have htrace : WordTrace (prefixWord ++ tailWord_217701) baseStart_217701 baseEnd_217701 := by
    simpa [prefixWord, tailWord_217701, baseEnd_217701] using wordTrace_append hprefix tailTrace_217701
  have hstable : (prefixWord ++ tailWord_217701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217701).length < 2 ^ (prefixWord ++ tailWord_217701).sum := by decide
  have hdescent : baseEnd_217701 < baseStart_217701 := by decide
  rcases family_descends (prefixWord ++ tailWord_217701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217789 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_217789 : Nat := 118140960795 + 217789 * 2 ^ 59
def prefixEnd_217789 : Nat := 4983230072969 + 3 ^ 40 * 217789 * 2
def baseEnd_217789 : Nat := 74553625508102422157275

theorem tailTrace_217789 : CollatzResearch.WordTrace tailWord_217789 prefixEnd_217789 74553625508102422157275 := by
  unfold tailWord_217789
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943417407995123245032421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5295611605330082163354947 7943417407995123245032421)
  ·
    refine ⟨1489390763999085608443579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7943417407995123245032421 1489390763999085608443579)
    ·
      refine ⟨2234086145998628412665369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489390763999085608443579 2234086145998628412665369)
      ·
        refine ⟨1675564609498971309499027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2234086145998628412665369 1675564609498971309499027)
        ·
          refine ⟨2513346914248456964248541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675564609498971309499027 2513346914248456964248541)
          ·
            refine ⟨942505092843171361593203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2513346914248456964248541 942505092843171361593203)
            ·
              refine ⟨1413757639264757042389805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942505092843171361593203 1413757639264757042389805)
              ·
                refine ⟨530159114724283890896177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413757639264757042389805 530159114724283890896177)
                ·
                  refine ⟨397619336043212918172133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530159114724283890896177 397619336043212918172133)
                  ·
                    refine ⟨74553625508102422157275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 397619336043212918172133 74553625508102422157275)
                    ·
                      rfl

theorem cell22_217789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_217789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217789 prefixEnd_217789 := by exact prefixLift 217789
  have htrace : WordTrace (prefixWord ++ tailWord_217789) baseStart_217789 baseEnd_217789 := by
    simpa [prefixWord, tailWord_217789, baseEnd_217789] using wordTrace_append hprefix tailTrace_217789
  have hstable : (prefixWord ++ tailWord_217789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217789).length < 2 ^ (prefixWord ++ tailWord_217789).sum := by decide
  have hdescent : baseEnd_217789 < baseStart_217789 := by decide
  rcases family_descends (prefixWord ++ tailWord_217789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217810 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_217810 : Nat := 118140960795 + 217810 * 2 ^ 59
def prefixEnd_217810 : Nat := 4983230072969 + 3 ^ 40 * 217810 * 2
def baseEnd_217810 : Nat := 24853604745755122460737

theorem tailTrace_217810 : CollatzResearch.WordTrace tailWord_217810 prefixEnd_217810 24853604745755122460737 := by
  unfold tailWord_217810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986045835229760957886721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5296122227279362554364589 1986045835229760957886721)
  ·
    refine ⟨1489534376422320718415041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1986045835229760957886721 1489534376422320718415041)
    ·
      refine ⟨1117150782316740538811281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1489534376422320718415041 1117150782316740538811281)
      ·
        refine ⟨837863086737555404108461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1117150782316740538811281 837863086737555404108461)
        ·
          refine ⟨314198657526583276540673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 837863086737555404108461 314198657526583276540673)
          ·
            refine ⟨235648993144937457405505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314198657526583276540673 235648993144937457405505)
            ·
              refine ⟨176736744858703093054129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235648993144937457405505 176736744858703093054129)
              ·
                refine ⟨132552558644027319790597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176736744858703093054129 132552558644027319790597)
                ·
                  refine ⟨24853604745755122460737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132552558644027319790597 24853604745755122460737)
                  ·
                    rfl

theorem cell22_217810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_217810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217810 prefixEnd_217810 := by exact prefixLift 217810
  have htrace : WordTrace (prefixWord ++ tailWord_217810) baseStart_217810 baseEnd_217810 := by
    simpa [prefixWord, tailWord_217810, baseEnd_217810] using wordTrace_append hprefix tailTrace_217810
  have hstable : (prefixWord ++ tailWord_217810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217810).length < 2 ^ (prefixWord ++ tailWord_217810).sum := by decide
  have hdescent : baseEnd_217810 < baseStart_217810 := by decide
  rcases family_descends (prefixWord ++ tailWord_217810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217817 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_217817 : Nat := 118140960795 + 217817 * 2 ^ 59
def prefixEnd_217817 : Nat := 4983230072969 + 3 ^ 40 * 217817 * 2
def baseEnd_217817 : Nat := 74563210480319682457189

theorem tailTrace_217817 : CollatzResearch.WordTrace tailWord_217817 prefixEnd_217817 74563210480319682457189 := by
  unfold tailWord_217817
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944438651893684027051705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5296292434595789351367803 7944438651893684027051705)
  ·
    refine ⟨5958328988920263020288779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7944438651893684027051705 5958328988920263020288779)
    ·
      refine ⟨8937493483380394530433169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958328988920263020288779 8937493483380394530433169)
      ·
        refine ⟨6703120112535295897824877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8937493483380394530433169 6703120112535295897824877)
        ·
          refine ⟨2513670042200735961684329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6703120112535295897824877 2513670042200735961684329)
          ·
            refine ⟨1885252531650551971263247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513670042200735961684329 1885252531650551971263247)
            ·
              refine ⟨2827878797475827956894871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885252531650551971263247 2827878797475827956894871)
              ·
                refine ⟨4241818196213741935342307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827878797475827956894871 4241818196213741935342307)
                ·
                  refine ⟨6362727294320612903013461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241818196213741935342307 6362727294320612903013461)
                  ·
                    refine ⟨74563210480319682457189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6362727294320612903013461 74563210480319682457189)
                    ·
                      rfl

theorem cell22_217817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_217817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217817 prefixEnd_217817 := by exact prefixLift 217817
  have htrace : WordTrace (prefixWord ++ tailWord_217817) baseStart_217817 baseEnd_217817 := by
    simpa [prefixWord, tailWord_217817, baseEnd_217817] using wordTrace_append hprefix tailTrace_217817
  have hstable : (prefixWord ++ tailWord_217817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217817).length < 2 ^ (prefixWord ++ tailWord_217817).sum := by decide
  have hdescent : baseEnd_217817 < baseStart_217817 := by decide
  rcases family_descends (prefixWord ++ tailWord_217817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217847 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_217847 : Nat := 118140960795 + 217847 * 2 ^ 59
def prefixEnd_217847 : Nat := 4983230072969 + 3 ^ 40 * 217847 * 2
def baseEnd_217847 : Nat := 74573480093409604207097

theorem tailTrace_217847 : CollatzResearch.WordTrace tailWord_217847 prefixEnd_217847 74573480093409604207097 := by
  unfold tailWord_217847
  simp only [CollatzResearch.WordTrace]
  refine ⟨7945532841784999150643795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5297021894523332767095863 7945532841784999150643795)
  ·
    refine ⟨11918299262677498725965693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7945532841784999150643795 11918299262677498725965693)
    ·
      refine ⟨4469362223504062022237135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11918299262677498725965693 4469362223504062022237135)
      ·
        refine ⟨6704043335256093033355703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469362223504062022237135 6704043335256093033355703)
        ·
          refine ⟨10056065002884139550033555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704043335256093033355703 10056065002884139550033555)
          ·
            refine ⟨15084097504326209325050333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10056065002884139550033555 15084097504326209325050333)
            ·
              refine ⟨5656536564122328496893875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15084097504326209325050333 5656536564122328496893875)
              ·
                refine ⟨8484804846183492745340813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656536564122328496893875 8484804846183492745340813)
                ·
                  refine ⟨3181801817318809779502805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8484804846183492745340813 3181801817318809779502805)
                  ·
                    refine ⟨74573480093409604207097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3181801817318809779502805 74573480093409604207097)
                    ·
                      rfl

theorem cell22_217847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_217847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217847 prefixEnd_217847 := by exact prefixLift 217847
  have htrace : WordTrace (prefixWord ++ tailWord_217847) baseStart_217847 baseEnd_217847 := by
    simpa [prefixWord, tailWord_217847, baseEnd_217847] using wordTrace_append hprefix tailTrace_217847
  have hstable : (prefixWord ++ tailWord_217847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217847).length < 2 ^ (prefixWord ++ tailWord_217847).sum := by decide
  have hdescent : baseEnd_217847 < baseStart_217847 := by decide
  rcases family_descends (prefixWord ++ tailWord_217847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217853 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_217853 : Nat := 118140960795 + 217853 * 2 ^ 59
def prefixEnd_217853 : Nat := 4983230072969 + 3 ^ 40 * 217853 * 2
def baseEnd_217853 : Nat := 74575534016027588557079

theorem tailTrace_217853 : CollatzResearch.WordTrace tailWord_217853 prefixEnd_217853 74575534016027588557079 := by
  unfold tailWord_217853
  simp only [CollatzResearch.WordTrace]
  refine ⟨7945751679763262175362213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5297167786508841450241475 7945751679763262175362213)
  ·
    refine ⟨1489828439955611657880415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7945751679763262175362213 1489828439955611657880415)
    ·
      refine ⟨2234742659933417486820623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489828439955611657880415 2234742659933417486820623)
      ·
        refine ⟨3352113989900126230230935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234742659933417486820623 3352113989900126230230935)
        ·
          refine ⟨5028170984850189345346403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352113989900126230230935 5028170984850189345346403)
          ·
            refine ⟨7542256477275284018019605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028170984850189345346403 7542256477275284018019605)
            ·
              refine ⟨353543272372278938344669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7542256477275284018019605 353543272372278938344669)
              ·
                refine ⟨132578727139604601879251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353543272372278938344669 132578727139604601879251)
                ·
                  refine ⟨198868090709406902818877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132578727139604601879251 198868090709406902818877)
                  ·
                    refine ⟨74575534016027588557079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198868090709406902818877 74575534016027588557079)
                    ·
                      rfl

theorem cell22_217853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_217853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217853 prefixEnd_217853 := by exact prefixLift 217853
  have htrace : WordTrace (prefixWord ++ tailWord_217853) baseStart_217853 baseEnd_217853 := by
    simpa [prefixWord, tailWord_217853, baseEnd_217853] using wordTrace_append hprefix tailTrace_217853
  have hstable : (prefixWord ++ tailWord_217853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217853).length < 2 ^ (prefixWord ++ tailWord_217853).sum := by decide
  have hdescent : baseEnd_217853 < baseStart_217853 := by decide
  rcases family_descends (prefixWord ++ tailWord_217853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217864 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_217864 : Nat := 118140960795 + 217864 * 2 ^ 59
def prefixEnd_217864 : Nat := 4983230072969 + 3 ^ 40 * 217864 * 2
def baseEnd_217864 : Nat := 74579299540827226532045

theorem tailTrace_217864 : CollatzResearch.WordTrace tailWord_217864 prefixEnd_217864 74579299540827226532045 := by
  unfold tailWord_217864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973076441361705527006323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5297435255148940702675097 3973076441361705527006323)
  ·
    refine ⟨5959614662042558290509485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973076441361705527006323 5959614662042558290509485)
    ·
      refine ⟨2234855498265959358941057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5959614662042558290509485 2234855498265959358941057)
      ·
        refine ⟨1676141623699469519205793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2234855498265959358941057 1676141623699469519205793)
        ·
          refine ⟨1257106217774602139404345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676141623699469519205793 1257106217774602139404345)
          ·
            refine ⟨942829663330951604553259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257106217774602139404345 942829663330951604553259)
            ·
              refine ⟨1414244494996427406829889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942829663330951604553259 1414244494996427406829889)
              ·
                refine ⟨1060683371247320555122417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414244494996427406829889 1060683371247320555122417)
                ·
                  refine ⟨795512528435490416341813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060683371247320555122417 795512528435490416341813)
                  ·
                    refine ⟨74579299540827226532045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 795512528435490416341813 74579299540827226532045)
                    ·
                      rfl

theorem cell22_217864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_217864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217864 prefixEnd_217864 := by exact prefixLift 217864
  have htrace : WordTrace (prefixWord ++ tailWord_217864) baseStart_217864 baseEnd_217864 := by
    simpa [prefixWord, tailWord_217864, baseEnd_217864] using wordTrace_append hprefix tailTrace_217864
  have hstable : (prefixWord ++ tailWord_217864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217864).length < 2 ^ (prefixWord ++ tailWord_217864).sum := by decide
  have hdescent : baseEnd_217864 < baseStart_217864 := by decide
  rcases family_descends (prefixWord ++ tailWord_217864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217928 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 4]
def baseStart_217928 : Nat := 118140960795 + 217928 * 2 ^ 59
def prefixEnd_217928 : Nat := 4983230072969 + 3 ^ 40 * 217928 * 2
def baseEnd_217928 : Nat := 24867069349584130977283

theorem tailTrace_217928 : CollatzResearch.WordTrace tailWord_217928 prefixEnd_217928 24867069349584130977283 := by
  unfold tailWord_217928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974243577245774992171219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5298991436327699989561625 3974243577245774992171219)
  ·
    refine ⟨5961365365868662488256829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3974243577245774992171219 5961365365868662488256829)
    ·
      refine ⟨2235512012200748433096311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5961365365868662488256829 2235512012200748433096311)
      ·
        refine ⟨3353268018301122649644467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235512012200748433096311 3353268018301122649644467)
        ·
          refine ⟨5029902027451683974466701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353268018301122649644467 5029902027451683974466701)
          ·
            refine ⟨1886213260294381490425013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5029902027451683974466701 1886213260294381490425013)
            ·
              refine ⟨176832493152598264727345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1886213260294381490425013 176832493152598264727345)
              ·
                refine ⟨132624369864448698545509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176832493152598264727345 132624369864448698545509)
                ·
                  refine ⟨24867069349584130977283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132624369864448698545509 24867069349584130977283)
                  ·
                    rfl

theorem cell22_217928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_217928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217928 prefixEnd_217928 := by exact prefixLift 217928
  have htrace : WordTrace (prefixWord ++ tailWord_217928) baseStart_217928 baseEnd_217928 := by
    simpa [prefixWord, tailWord_217928, baseEnd_217928] using wordTrace_append hprefix tailTrace_217928
  have hstable : (prefixWord ++ tailWord_217928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217928).length < 2 ^ (prefixWord ++ tailWord_217928).sum := by decide
  have hdescent : baseEnd_217928 < baseStart_217928 := by decide
  rcases family_descends (prefixWord ++ tailWord_217928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217943 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 2, 3]
def baseStart_217943 : Nat := 118140960795 + 217943 * 2 ^ 59
def prefixEnd_217943 : Nat := 4983230072969 + 3 ^ 40 * 217943 * 2
def baseEnd_217943 : Nat := 74606342855297353806803

theorem tailTrace_217943 : CollatzResearch.WordTrace tailWord_217943 prefixEnd_217943 74606342855297353806803 := by
  unfold tailWord_217943
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949034249437207546138483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5299356166291471697425655 7949034249437207546138483)
  ·
    refine ⟨11923551374155811319207725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949034249437207546138483 11923551374155811319207725)
    ·
      refine ⟨4471331765308429244702897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11923551374155811319207725 4471331765308429244702897)
      ·
        refine ⟨3353498823981321933527173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4471331765308429244702897 3353498823981321933527173)
        ·
          refine ⟨628781029496497862536345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3353498823981321933527173 628781029496497862536345)
          ·
            refine ⟨471585772122373396902259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628781029496497862536345 471585772122373396902259)
            ·
              refine ⟨707378658183560095353389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471585772122373396902259 707378658183560095353389)
              ·
                refine ⟨265266996818835035757521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707378658183560095353389 265266996818835035757521)
                ·
                  refine ⟨198950247614126276818141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265266996818835035757521 198950247614126276818141)
                  ·
                    refine ⟨74606342855297353806803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198950247614126276818141 74606342855297353806803)
                    ·
                      rfl

theorem cell22_217943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_217943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_217943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_217943 prefixEnd_217943 := by exact prefixLift 217943
  have htrace : WordTrace (prefixWord ++ tailWord_217943) baseStart_217943 baseEnd_217943 := by
    simpa [prefixWord, tailWord_217943, baseEnd_217943] using wordTrace_append hprefix tailTrace_217943
  have hstable : (prefixWord ++ tailWord_217943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217943).length < 2 ^ (prefixWord ++ tailWord_217943).sum := by decide
  have hdescent : baseEnd_217943 < baseStart_217943 := by decide
  rcases family_descends (prefixWord ++ tailWord_217943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218052 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 5]
def baseStart_218052 : Nat := 118140960795 + 218052 * 2 ^ 59
def prefixEnd_218052 : Nat := 4983230072969 + 3 ^ 40 * 218052 * 2
def baseEnd_218052 : Nat := 24881218594285800943823

theorem tailTrace_218052 : CollatzResearch.WordTrace tailWord_218052 prefixEnd_218052 24881218594285800943823 := by
  unfold tailWord_218052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976504903021159580928205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5302006537361546107904273 3976504903021159580928205)
  ·
    refine ⟨1491189338632934842848077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3976504903021159580928205 1491189338632934842848077)
    ·
      refine ⟨559196001987350566068029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1491189338632934842848077 559196001987350566068029)
      ·
        refine ⟨209698500745256462275511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559196001987350566068029 209698500745256462275511)
        ·
          refine ⟨314547751117884693413267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209698500745256462275511 314547751117884693413267)
          ·
            refine ⟨471821626676827040119901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314547751117884693413267 471821626676827040119901)
            ·
              refine ⟨176933110003810140044963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471821626676827040119901 176933110003810140044963)
              ·
                refine ⟨265399665005715210067445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176933110003810140044963 265399665005715210067445)
                ·
                  refine ⟨24881218594285800943823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265399665005715210067445 24881218594285800943823)
                  ·
                    rfl

theorem cell22_218052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_218052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218052 prefixEnd_218052 := by exact prefixLift 218052
  have htrace : WordTrace (prefixWord ++ tailWord_218052) baseStart_218052 baseEnd_218052 := by
    simpa [prefixWord, tailWord_218052, baseEnd_218052] using wordTrace_append hprefix tailTrace_218052
  have hstable : (prefixWord ++ tailWord_218052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218052).length < 2 ^ (prefixWord ++ tailWord_218052).sum := by decide
  have hdescent : baseEnd_218052 < baseStart_218052 := by decide
  rcases family_descends (prefixWord ++ tailWord_218052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218168 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_218168 : Nat := 118140960795 + 218168 * 2 ^ 59
def prefixEnd_218168 : Nat := 4983230072969 + 3 ^ 40 * 218168 * 2
def baseEnd_218168 : Nat := 74683364953471766931113

theorem tailTrace_218168 : CollatzResearch.WordTrace tailWord_218168 prefixEnd_218168 74683364953471766931113 := by
  unfold tailWord_218168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978620336811035486539579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5304827115748047315386105 3978620336811035486539579)
  ·
    refine ⟨5967930505216553229809369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978620336811035486539579 5967930505216553229809369)
    ·
      refine ⟨4475947878912414922357027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5967930505216553229809369 4475947878912414922357027)
      ·
        refine ⟨6713921818368622383535541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475947878912414922357027 6713921818368622383535541)
        ·
          refine ⟨629430170472058348456457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6713921818368622383535541 629430170472058348456457)
          ·
            refine ⟨472072627854043761342343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629430170472058348456457 472072627854043761342343)
            ·
              refine ⟨708108941781065642013515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472072627854043761342343 708108941781065642013515)
              ·
                refine ⟨1062163412671598463020273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708108941781065642013515 1062163412671598463020273)
                ·
                  refine ⟨796622559503698847265205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062163412671598463020273 796622559503698847265205)
                  ·
                    refine ⟨74683364953471766931113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 796622559503698847265205 74683364953471766931113)
                    ·
                      rfl

theorem cell22_218168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_218168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218168 prefixEnd_218168 := by exact prefixLift 218168
  have htrace : WordTrace (prefixWord ++ tailWord_218168) baseStart_218168 baseEnd_218168 := by
    simpa [prefixWord, tailWord_218168, baseEnd_218168] using wordTrace_append hprefix tailTrace_218168
  have hstable : (prefixWord ++ tailWord_218168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218168).length < 2 ^ (prefixWord ++ tailWord_218168).sum := by decide
  have hdescent : baseEnd_218168 < baseStart_218168 := by decide
  rcases family_descends (prefixWord ++ tailWord_218168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218181 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 8]
def baseStart_218181 : Nat := 118140960795 + 218181 * 2 ^ 59
def prefixEnd_218181 : Nat := 4983230072969 + 3 ^ 40 * 218181 * 2
def baseEnd_218181 : Nat := 24895938373048022118691

theorem tailTrace_218181 : CollatzResearch.WordTrace tailWord_218181 prefixEnd_218181 24895938373048022118691 := by
  unfold tailWord_218181
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957714822574974193302397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5305143215049982795534931 7957714822574974193302397)
  ·
    refine ⟨2984143058465615322488399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7957714822574974193302397 2984143058465615322488399)
    ·
      refine ⟨4476214587698422983732599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2984143058465615322488399 4476214587698422983732599)
      ·
        refine ⟨6714321881547634475598899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4476214587698422983732599 6714321881547634475598899)
        ·
          refine ⟨10071482822321451713398349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714321881547634475598899 10071482822321451713398349)
          ·
            refine ⟨3776806058370544392524381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10071482822321451713398349 3776806058370544392524381)
            ·
              refine ⟨1416302271888954147196643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3776806058370544392524381 1416302271888954147196643)
              ·
                refine ⟨2124453407833431220794965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416302271888954147196643 2124453407833431220794965)
                ·
                  refine ⟨24895938373048022118691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2124453407833431220794965 24895938373048022118691)
                  ·
                    rfl

theorem cell22_218181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_218181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218181 prefixEnd_218181 := by exact prefixLift 218181
  have htrace : WordTrace (prefixWord ++ tailWord_218181) baseStart_218181 baseEnd_218181 := by
    simpa [prefixWord, tailWord_218181, baseEnd_218181] using wordTrace_append hprefix tailTrace_218181
  have hstable : (prefixWord ++ tailWord_218181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218181).length < 2 ^ (prefixWord ++ tailWord_218181).sum := by decide
  have hdescent : baseEnd_218181 < baseStart_218181 := by decide
  rcases family_descends (prefixWord ++ tailWord_218181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218183 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 3, 4]
def baseStart_218183 : Nat := 118140960795 + 218183 * 2 ^ 59
def prefixEnd_218183 : Nat := 4983230072969 + 3 ^ 40 * 218183 * 2
def baseEnd_218183 : Nat := 74688499760016727806067

theorem tailTrace_218183 : CollatzResearch.WordTrace tailWord_218183 prefixEnd_218183 74688499760016727806067 := by
  unfold tailWord_218183
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957787768567728534875203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5305191845711819023250135 7957787768567728534875203)
  ·
    refine ⟨11936681652851592802312805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7957787768567728534875203 11936681652851592802312805)
    ·
      refine ⟨2238127809909673650433651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11936681652851592802312805 2238127809909673650433651)
      ·
        refine ⟨3357191714864510475650477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238127809909673650433651 3357191714864510475650477)
        ·
          refine ⟨1258946893074191428368929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3357191714864510475650477 1258946893074191428368929)
          ·
            refine ⟨944210169805643571276697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1258946893074191428368929 944210169805643571276697)
            ·
              refine ⟨708157627354232678457523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944210169805643571276697 708157627354232678457523)
              ·
                refine ⟨1062236441031349017686285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708157627354232678457523 1062236441031349017686285)
                ·
                  refine ⟨398338665386755881632357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062236441031349017686285 398338665386755881632357)
                  ·
                    refine ⟨74688499760016727806067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 398338665386755881632357 74688499760016727806067)
                    ·
                      rfl

theorem cell22_218183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_218183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218183 prefixEnd_218183 := by exact prefixLift 218183
  have htrace : WordTrace (prefixWord ++ tailWord_218183) baseStart_218183 baseEnd_218183 := by
    simpa [prefixWord, tailWord_218183, baseEnd_218183] using wordTrace_append hprefix tailTrace_218183
  have hstable : (prefixWord ++ tailWord_218183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218183).length < 2 ^ (prefixWord ++ tailWord_218183).sum := by decide
  have hdescent : baseEnd_218183 < baseStart_218183 := by decide
  rcases family_descends (prefixWord ++ tailWord_218183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218215 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 4]
def baseStart_218215 : Nat := 118140960795 + 218215 * 2 ^ 59
def prefixEnd_218215 : Nat := 4983230072969 + 3 ^ 40 * 218215 * 2
def baseEnd_218215 : Nat := 24899818004659770335323

theorem tailTrace_218215 : CollatzResearch.WordTrace tailWord_218215 prefixEnd_218215 24899818004659770335323 := by
  unfold tailWord_218215
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958954904451798000040099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5305969936301198666693399 7958954904451798000040099)
  ·
    refine ⟨11938432356677697000060149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958954904451798000040099 11938432356677697000060149)
    ·
      refine ⟨1119228033438534093755639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11938432356677697000060149 1119228033438534093755639)
      ·
        refine ⟨1678842050157801140633459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119228033438534093755639 1678842050157801140633459)
        ·
          refine ⟨2518263075236701710950189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678842050157801140633459 2518263075236701710950189)
          ·
            refine ⟨944348653213763141606321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2518263075236701710950189 944348653213763141606321)
            ·
              refine ⟨708261489910322356204741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944348653213763141606321 708261489910322356204741)
              ·
                refine ⟨132799029358185441788389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708261489910322356204741 132799029358185441788389)
                ·
                  refine ⟨24899818004659770335323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132799029358185441788389 24899818004659770335323)
                  ·
                    rfl

theorem cell22_218215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 4].length) (baseStart_218215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218215 prefixEnd_218215 := by exact prefixLift 218215
  have htrace : WordTrace (prefixWord ++ tailWord_218215) baseStart_218215 baseEnd_218215 := by
    simpa [prefixWord, tailWord_218215, baseEnd_218215] using wordTrace_append hprefix tailTrace_218215
  have hstable : (prefixWord ++ tailWord_218215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218215).length < 2 ^ (prefixWord ++ tailWord_218215).sum := by decide
  have hdescent : baseEnd_218215 < baseStart_218215 := by decide
  rcases family_descends (prefixWord ++ tailWord_218215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218273 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_218273 : Nat := 118140960795 + 218273 * 2 ^ 59
def prefixEnd_218273 : Nat := 4983230072969 + 3 ^ 40 * 218273 * 2
def baseEnd_218273 : Nat := 74719308599286493055791

theorem tailTrace_218273 : CollatzResearch.WordTrace tailWord_218273 prefixEnd_218273 74719308599286493055791 := by
  unfold tailWord_218273
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961070338241673905651473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5307380225494449270434315 7961070338241673905651473)
  ·
    refine ⟨5970802753681255429238605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7961070338241673905651473 5970802753681255429238605)
    ·
      refine ⟨2239051032630470785964477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5970802753681255429238605 2239051032630470785964477)
      ·
        refine ⟨839644137236426544736679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2239051032630470785964477 839644137236426544736679)
        ·
          refine ⟨1259466205854639817105019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839644137236426544736679 1259466205854639817105019)
          ·
            refine ⟨1889199308781959725657529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259466205854639817105019 1889199308781959725657529)
            ·
              refine ⟨1416899481586469794243147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889199308781959725657529 1416899481586469794243147)
              ·
                refine ⟨2125349222379704691364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416899481586469794243147 2125349222379704691364721)
                ·
                  refine ⟨1594011916784778518523541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2125349222379704691364721 1594011916784778518523541)
                  ·
                    refine ⟨74719308599286493055791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1594011916784778518523541 74719308599286493055791)
                    ·
                      rfl

theorem cell22_218273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_218273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218273 prefixEnd_218273 := by exact prefixLift 218273
  have htrace : WordTrace (prefixWord ++ tailWord_218273) baseStart_218273 baseEnd_218273 := by
    simpa [prefixWord, tailWord_218273, baseEnd_218273] using wordTrace_append hprefix tailTrace_218273
  have hstable : (prefixWord ++ tailWord_218273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218273).length < 2 ^ (prefixWord ++ tailWord_218273).sum := by decide
  have hdescent : baseEnd_218273 < baseStart_218273 := by decide
  rcases family_descends (prefixWord ++ tailWord_218273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218288 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_218288 : Nat := 118140960795 + 218288 * 2 ^ 59
def prefixEnd_218288 : Nat := 4983230072969 + 3 ^ 40 * 218288 * 2
def baseEnd_218288 : Nat := 24908147801943817976915

theorem tailTrace_218288 : CollatzResearch.WordTrace tailWord_218288 prefixEnd_218288 24908147801943817976915 := by
  unfold tailWord_218288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980808716593665733723759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5307744955458220978298345 3980808716593665733723759)
  ·
    refine ⟨5971213074890498600585639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3980808716593665733723759 5971213074890498600585639)
    ·
      refine ⟨8956819612335747900878459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971213074890498600585639 8956819612335747900878459)
      ·
        refine ⟨13435229418503621851317689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956819612335747900878459 13435229418503621851317689)
        ·
          refine ⟨10076422063877716388488267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13435229418503621851317689 10076422063877716388488267)
          ·
            refine ⟨15114633095816574582732401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076422063877716388488267 15114633095816574582732401)
            ·
              refine ⟨11335974821862430937049301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15114633095816574582732401 11335974821862430937049301)
              ·
                refine ⟨265686909887400725087093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11335974821862430937049301 265686909887400725087093)
                ·
                  refine ⟨24908147801943817976915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265686909887400725087093 24908147801943817976915)
                  ·
                    rfl

theorem cell22_218288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_218288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218288 prefixEnd_218288 := by exact prefixLift 218288
  have htrace : WordTrace (prefixWord ++ tailWord_218288) baseStart_218288 baseEnd_218288 := by
    simpa [prefixWord, tailWord_218288, baseEnd_218288] using wordTrace_append hprefix tailTrace_218288
  have hstable : (prefixWord ++ tailWord_218288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218288).length < 2 ^ (prefixWord ++ tailWord_218288).sum := by decide
  have hdescent : baseEnd_218288 < baseStart_218288 := by decide
  rcases family_descends (prefixWord ++ tailWord_218288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218367 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 4]
def baseStart_218367 : Nat := 118140960795 + 218367 * 2 ^ 59
def prefixEnd_218367 : Nat := 4983230072969 + 3 ^ 40 * 218367 * 2
def baseEnd_218367 : Nat := 24917162240100527068501

theorem tailTrace_218367 : CollatzResearch.WordTrace tailWord_218367 prefixEnd_218367 24917162240100527068501 := by
  unfold tailWord_218367
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964498799901127959573355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5309665866600751973048903 7964498799901127959573355)
  ·
    refine ⟨11946748199851691939360033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7964498799901127959573355 11946748199851691939360033)
    ·
      refine ⟨8960061149888768954520025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11946748199851691939360033 8960061149888768954520025)
      ·
        refine ⟨6720045862416576715890019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8960061149888768954520025 6720045862416576715890019)
        ·
          refine ⟨10080068793624865073835029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6720045862416576715890019 10080068793624865073835029)
          ·
            refine ⟨472503224701165550336017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10080068793624865073835029 472503224701165550336017)
            ·
              refine ⟨354377418525874162752013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472503224701165550336017 354377418525874162752013)
              ·
                refine ⟨132891531947202811032005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354377418525874162752013 132891531947202811032005)
                ·
                  refine ⟨24917162240100527068501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132891531947202811032005 24917162240100527068501)
                  ·
                    rfl

theorem cell22_218367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 4].length) (baseStart_218367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218367 prefixEnd_218367 := by exact prefixLift 218367
  have htrace : WordTrace (prefixWord ++ tailWord_218367) baseStart_218367 baseEnd_218367 := by
    simpa [prefixWord, tailWord_218367, baseEnd_218367] using wordTrace_append hprefix tailTrace_218367
  have hstable : (prefixWord ++ tailWord_218367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218367).length < 2 ^ (prefixWord ++ tailWord_218367).sum := by decide
  have hdescent : baseEnd_218367 < baseStart_218367 := by decide
  rcases family_descends (prefixWord ++ tailWord_218367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218369 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 1, 4]
def baseStart_218369 : Nat := 118140960795 + 218369 * 2 ^ 59
def prefixEnd_218369 : Nat := 4983230072969 + 3 ^ 40 * 218369 * 2
def baseEnd_218369 : Nat := 74752171361174242655497

theorem tailTrace_218369 : CollatzResearch.WordTrace tailWord_218369 prefixEnd_218369 74752171361174242655497 := by
  unfold tailWord_218369
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964571745893882301146161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5309714497262588200764107 7964571745893882301146161)
  ·
    refine ⟨5973428809420411725859621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7964571745893882301146161 5973428809420411725859621)
    ·
      refine ⟨1120017901766327198598679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5973428809420411725859621 1120017901766327198598679)
      ·
        refine ⟨1680026852649490797898019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120017901766327198598679 1680026852649490797898019)
        ·
          refine ⟨2520040278974236196847029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680026852649490797898019 2520040278974236196847029)
          ·
            refine ⟨236253776153834643454409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2520040278974236196847029 236253776153834643454409)
            ·
              refine ⟨177190332115375982590807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236253776153834643454409 177190332115375982590807)
              ·
                refine ⟨265785498173063973886211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177190332115375982590807 265785498173063973886211)
                ·
                  refine ⟨398678247259595960829317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265785498173063973886211 398678247259595960829317)
                  ·
                    refine ⟨74752171361174242655497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 398678247259595960829317 74752171361174242655497)
                    ·
                      rfl

theorem cell22_218369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_218369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218369 prefixEnd_218369 := by exact prefixLift 218369
  have htrace : WordTrace (prefixWord ++ tailWord_218369) baseStart_218369 baseEnd_218369 := by
    simpa [prefixWord, tailWord_218369, baseEnd_218369] using wordTrace_append hprefix tailTrace_218369
  have hstable : (prefixWord ++ tailWord_218369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218369).length < 2 ^ (prefixWord ++ tailWord_218369).sum := by decide
  have hdescent : baseEnd_218369 < baseStart_218369 := by decide
  rcases family_descends (prefixWord ++ tailWord_218369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218382 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_218382 : Nat := 118140960795 + 218382 * 2 ^ 59
def prefixEnd_218382 : Nat := 4983230072969 + 3 ^ 40 * 218382 * 2
def baseEnd_218382 : Nat := 74756621526846542080457

theorem tailTrace_218382 : CollatzResearch.WordTrace tailWord_218382 prefixEnd_218382 74756621526846542080457 := by
  unfold tailWord_218382
  simp only [CollatzResearch.WordTrace]
  refine ⟨995630736855848190171175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5310030596564523680912933 995630736855848190171175)
  ·
    refine ⟨1493446105283772285256763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995630736855848190171175 1493446105283772285256763)
    ·
      refine ⟨2240169157925658427885145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493446105283772285256763 2240169157925658427885145)
      ·
        refine ⟨1680126868444243820913859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240169157925658427885145 1680126868444243820913859)
        ·
          refine ⟨2520190302666365731370789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680126868444243820913859 2520190302666365731370789)
          ·
            refine ⟨472535681749943574632023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2520190302666365731370789 472535681749943574632023)
            ·
              refine ⟨708803522624915361948035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472535681749943574632023 708803522624915361948035)
              ·
                refine ⟨1063205283937373042922053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708803522624915361948035 1063205283937373042922053)
                ·
                  refine ⟨199350990738257445547885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063205283937373042922053 199350990738257445547885)
                  ·
                    refine ⟨74756621526846542080457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199350990738257445547885 74756621526846542080457)
                    ·
                      rfl

theorem cell22_218382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_218382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218382 prefixEnd_218382 := by exact prefixLift 218382
  have htrace : WordTrace (prefixWord ++ tailWord_218382) baseStart_218382 baseEnd_218382 := by
    simpa [prefixWord, tailWord_218382, baseEnd_218382] using wordTrace_append hprefix tailTrace_218382
  have hstable : (prefixWord ++ tailWord_218382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218382).length < 2 ^ (prefixWord ++ tailWord_218382).sum := by decide
  have hdescent : baseEnd_218382 < baseStart_218382 := by decide
  rcases family_descends (prefixWord ++ tailWord_218382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218399 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 1, 5]
def baseStart_218399 : Nat := 118140960795 + 218399 * 2 ^ 59
def prefixEnd_218399 : Nat := 4983230072969 + 3 ^ 40 * 218399 * 2
def baseEnd_218399 : Nat := 74762440974264164405405

theorem tailTrace_218399 : CollatzResearch.WordTrace tailWord_218399 prefixEnd_218399 74762440974264164405405 := by
  unfold tailWord_218399
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965665935785197424738251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5310443957190131616492167 7965665935785197424738251)
  ·
    refine ⟨11948498903677796137107377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7965665935785197424738251 11948498903677796137107377)
    ·
      refine ⟨8961374177758347102830533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11948498903677796137107377 8961374177758347102830533)
      ·
        refine ⟨1680257658329690081780725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8961374177758347102830533 1680257658329690081780725)
        ·
          refine ⟨157524155468408445166943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1680257658329690081780725 157524155468408445166943)
          ·
            refine ⟨236286233202612667750415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157524155468408445166943 236286233202612667750415)
            ·
              refine ⟨354429349803919001625623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236286233202612667750415 354429349803919001625623)
              ·
                refine ⟨531644024705878502438435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354429349803919001625623 531644024705878502438435)
                ·
                  refine ⟨797466037058817753657653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531644024705878502438435 797466037058817753657653)
                  ·
                    refine ⟨74762440974264164405405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 797466037058817753657653 74762440974264164405405)
                    ·
                      rfl

theorem cell22_218399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_218399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218399 prefixEnd_218399 := by exact prefixLift 218399
  have htrace : WordTrace (prefixWord ++ tailWord_218399) baseStart_218399 baseEnd_218399 := by
    simpa [prefixWord, tailWord_218399, baseEnd_218399] using wordTrace_append hprefix tailTrace_218399
  have hstable : (prefixWord ++ tailWord_218399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218399).length < 2 ^ (prefixWord ++ tailWord_218399).sum := by decide
  have hdescent : baseEnd_218399 < baseStart_218399 := by decide
  rcases family_descends (prefixWord ++ tailWord_218399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218429 : List Nat := [1, 4, 1, 5, 2, 1, 8]
def baseStart_218429 : Nat := 118140960795 + 218429 * 2 ^ 59
def prefixEnd_218429 : Nat := 4983230072969 + 3 ^ 40 * 218429 * 2
def baseEnd_218429 : Nat := 2769359651383484672419

theorem tailTrace_218429 : CollatzResearch.WordTrace tailWord_218429 prefixEnd_218429 2769359651383484672419 := by
  unfold tailWord_218429
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966760125676512548330341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5311173417117675032220227 7966760125676512548330341)
  ·
    refine ⟨1493767523564346102811939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7966760125676512548330341 1493767523564346102811939)
    ·
      refine ⟨2240651285346519154217909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493767523564346102811939 2240651285346519154217909)
      ·
        refine ⟨210061058001236170707929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2240651285346519154217909 210061058001236170707929)
        ·
          refine ⟨157545793500927128030947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210061058001236170707929 157545793500927128030947)
          ·
            refine ⟨236318690251390692046421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157545793500927128030947 236318690251390692046421)
            ·
              refine ⟨2769359651383484672419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 236318690251390692046421 2769359651383484672419)
              ·
                rfl

theorem cell22_218429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 8].length) (baseStart_218429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218429 prefixEnd_218429 := by exact prefixLift 218429
  have htrace : WordTrace (prefixWord ++ tailWord_218429) baseStart_218429 baseEnd_218429 := by
    simpa [prefixWord, tailWord_218429, baseEnd_218429] using wordTrace_append hprefix tailTrace_218429
  have hstable : (prefixWord ++ tailWord_218429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218429).length < 2 ^ (prefixWord ++ tailWord_218429).sum := by decide
  have hdescent : baseEnd_218429 < baseStart_218429 := by decide
  rcases family_descends (prefixWord ++ tailWord_218429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218440 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_218440 : Nat := 118140960795 + 218440 * 2 ^ 59
def prefixEnd_218440 : Nat := 4983230072969 + 3 ^ 40 * 218440 * 2
def baseEnd_218440 : Nat := 24925492037384574710093

theorem tailTrace_218440 : CollatzResearch.WordTrace tailWord_218440 prefixEnd_218440 24925492037384574710093 := by
  unfold tailWord_218440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983580664318330713490387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5311440885757774284653849 3983580664318330713490387)
  ·
    refine ⟨5975370996477496070235581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3983580664318330713490387 5975370996477496070235581)
    ·
      refine ⟨2240764123679061026338343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5975370996477496070235581 2240764123679061026338343)
      ·
        refine ⟨3361146185518591539507515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240764123679061026338343 3361146185518591539507515)
        ·
          refine ⟨5041719278277887309261273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361146185518591539507515 5041719278277887309261273)
          ·
            refine ⟨3781289458708415481945955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5041719278277887309261273 3781289458708415481945955)
            ·
              refine ⟨5671934188062623222918933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781289458708415481945955 5671934188062623222918933)
              ·
                refine ⟨265871915065435463574325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5671934188062623222918933 265871915065435463574325)
                ·
                  refine ⟨24925492037384574710093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265871915065435463574325 24925492037384574710093)
                  ·
                    rfl

theorem cell22_218440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_218440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218440 prefixEnd_218440 := by exact prefixLift 218440
  have htrace : WordTrace (prefixWord ++ tailWord_218440) baseStart_218440 baseEnd_218440 := by
    simpa [prefixWord, tailWord_218440, baseEnd_218440] using wordTrace_append hprefix tailTrace_218440
  have hstable : (prefixWord ++ tailWord_218440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218440).length < 2 ^ (prefixWord ++ tailWord_218440).sum := by decide
  have hdescent : baseEnd_218440 < baseStart_218440 := by decide
  rcases family_descends (prefixWord ++ tailWord_218440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218444 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_218444 : Nat := 118140960795 + 218444 * 2 ^ 59
def prefixEnd_218444 : Nat := 4983230072969 + 3 ^ 40 * 218444 * 2
def baseEnd_218444 : Nat := 74777845393899047030267

theorem tailTrace_218444 : CollatzResearch.WordTrace tailWord_218444 prefixEnd_218444 74777845393899047030267 := by
  unfold tailWord_218444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983653610311085055063193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5311538147081446740084257 3983653610311085055063193)
  ·
    refine ⟨2987740207733313791297395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3983653610311085055063193 2987740207733313791297395)
    ·
      refine ⟨4481610311599970686946093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987740207733313791297395 4481610311599970686946093)
      ·
        refine ⟨1680603866849989007604785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4481610311599970686946093 1680603866849989007604785)
        ·
          refine ⟨1260452900137491755703589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1680603866849989007604785 1260452900137491755703589)
          ·
            refine ⟨236334918775779704194423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1260452900137491755703589 236334918775779704194423)
            ·
              refine ⟨354502378163669556291635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236334918775779704194423 354502378163669556291635)
              ·
                refine ⟨531753567245504334437453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354502378163669556291635 531753567245504334437453)
                ·
                  refine ⟨199407587717064125414045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531753567245504334437453 199407587717064125414045)
                  ·
                    refine ⟨74777845393899047030267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199407587717064125414045 74777845393899047030267)
                    ·
                      rfl

theorem cell22_218444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_218444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218444 prefixEnd_218444 := by exact prefixLift 218444
  have htrace : WordTrace (prefixWord ++ tailWord_218444) baseStart_218444 baseEnd_218444 := by
    simpa [prefixWord, tailWord_218444, baseEnd_218444] using wordTrace_append hprefix tailTrace_218444
  have hstable : (prefixWord ++ tailWord_218444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218444).length < 2 ^ (prefixWord ++ tailWord_218444).sum := by decide
  have hdescent : baseEnd_218444 < baseStart_218444 := by decide
  rcases family_descends (prefixWord ++ tailWord_218444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218457 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 5]
def baseStart_218457 : Nat := 118140960795 + 218457 * 2 ^ 59
def prefixEnd_218457 : Nat := 4983230072969 + 3 ^ 40 * 218457 * 2
def baseEnd_218457 : Nat := 24927431853190448818409

theorem tailTrace_218457 : CollatzResearch.WordTrace tailWord_218457 prefixEnd_218457 24927431853190448818409 := by
  unfold tailWord_218457
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967781369575073330349625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5311854246383382220233083 7967781369575073330349625)
  ·
    refine ⟨5975836027181304997762219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7967781369575073330349625 5975836027181304997762219)
    ·
      refine ⟨8963754040771957496643329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5975836027181304997762219 8963754040771957496643329)
      ·
        refine ⟨6722815530578968122482497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8963754040771957496643329 6722815530578968122482497)
        ·
          refine ⟨5042111647934226091861873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6722815530578968122482497 5042111647934226091861873)
          ·
            refine ⟨3781583735950669568896405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042111647934226091861873 3781583735950669568896405)
            ·
              refine ⟨177261737622687636042019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3781583735950669568896405 177261737622687636042019)
              ·
                refine ⟨265892606434031454063029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177261737622687636042019 265892606434031454063029)
                ·
                  refine ⟨24927431853190448818409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265892606434031454063029 24927431853190448818409)
                  ·
                    rfl

theorem cell22_218457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_218457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218457 prefixEnd_218457 := by exact prefixLift 218457
  have htrace : WordTrace (prefixWord ++ tailWord_218457) baseStart_218457 baseEnd_218457 := by
    simpa [prefixWord, tailWord_218457, baseEnd_218457] using wordTrace_append hprefix tailTrace_218457
  have hstable : (prefixWord ++ tailWord_218457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218457).length < 2 ^ (prefixWord ++ tailWord_218457).sum := by decide
  have hdescent : baseEnd_218457 < baseStart_218457 := by decide
  rcases family_descends (prefixWord ++ tailWord_218457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218560 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_218560 : Nat := 118140960795 + 218560 * 2 ^ 59
def prefixEnd_218560 : Nat := 4983230072969 + 3 ^ 40 * 218560 * 2
def baseEnd_218560 : Nat := 74817554564513411129911

theorem tailTrace_218560 : CollatzResearch.WordTrace tailWord_218560 prefixEnd_218560 74817554564513411129911 := by
  unfold tailWord_218560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985769044100960960674567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5314358725467947947566089 3985769044100960960674567)
  ·
    refine ⟨5978653566151441441011851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985769044100960960674567 5978653566151441441011851)
    ·
      refine ⟨8967980349227162161517777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5978653566151441441011851 8967980349227162161517777)
      ·
        refine ⟨6725985261920371621138333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8967980349227162161517777 6725985261920371621138333)
        ·
          refine ⟨2522244473220139357926875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6725985261920371621138333 2522244473220139357926875)
          ·
            refine ⟨3783366709830209036890313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522244473220139357926875 3783366709830209036890313)
            ·
              refine ⟨2837525032372656777667735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783366709830209036890313 2837525032372656777667735)
              ·
                refine ⟨4256287548558985166501603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837525032372656777667735 4256287548558985166501603)
                ·
                  refine ⟨6384431322838477749752405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256287548558985166501603 6384431322838477749752405)
                  ·
                    refine ⟨74817554564513411129911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6384431322838477749752405 74817554564513411129911)
                    ·
                      rfl

theorem cell22_218560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_218560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218560 prefixEnd_218560 := by exact prefixLift 218560
  have htrace : WordTrace (prefixWord ++ tailWord_218560) baseStart_218560 baseEnd_218560 := by
    simpa [prefixWord, tailWord_218560, baseEnd_218560] using wordTrace_append hprefix tailTrace_218560
  have hstable : (prefixWord ++ tailWord_218560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218560).length < 2 ^ (prefixWord ++ tailWord_218560).sum := by decide
  have hdescent : baseEnd_218560 < baseStart_218560 := by decide
  rcases family_descends (prefixWord ++ tailWord_218560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218613 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_218613 : Nat := 118140960795 + 218613 * 2 ^ 59
def prefixEnd_218613 : Nat := 4983230072969 + 3 ^ 40 * 218613 * 2
def baseEnd_218613 : Nat := 74835697547638939554749

theorem tailTrace_218613 : CollatzResearch.WordTrace tailWord_218613 prefixEnd_218613 74835697547638939554749 := by
  unfold tailWord_218613
  simp only [CollatzResearch.WordTrace]
  refine ⟨7973471157009911973028493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5315647438006607982018995 7973471157009911973028493)
  ·
    refine ⟨2990051683878716989885685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7973471157009911973028493 2990051683878716989885685)
    ·
      refine ⟨280317345363629717801783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2990051683878716989885685 280317345363629717801783)
      ·
        refine ⟨420476018045444576702675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280317345363629717801783 420476018045444576702675)
        ·
          refine ⟨630714027068166865054013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420476018045444576702675 630714027068166865054013)
          ·
            refine ⟨236517760150562574395255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630714027068166865054013 236517760150562574395255)
            ·
              refine ⟨354776640225843861592883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236517760150562574395255 354776640225843861592883)
              ·
                refine ⟨532164960338765792389325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354776640225843861592883 532164960338765792389325)
                ·
                  refine ⟨199561860127037172145997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532164960338765792389325 199561860127037172145997)
                  ·
                    refine ⟨74835697547638939554749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199561860127037172145997 74835697547638939554749)
                    ·
                      rfl

theorem cell22_218613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_218613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218613 prefixEnd_218613 := by exact prefixLift 218613
  have htrace : WordTrace (prefixWord ++ tailWord_218613) baseStart_218613 baseEnd_218613 := by
    simpa [prefixWord, tailWord_218613, baseEnd_218613] using wordTrace_append hprefix tailTrace_218613
  have hstable : (prefixWord ++ tailWord_218613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218613).length < 2 ^ (prefixWord ++ tailWord_218613).sum := by decide
  have hdescent : baseEnd_218613 < baseStart_218613 := by decide
  rcases family_descends (prefixWord ++ tailWord_218613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218626 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_218626 : Nat := 118140960795 + 218626 * 2 ^ 59
def prefixEnd_218626 : Nat := 4983230072969 + 3 ^ 40 * 218626 * 2
def baseEnd_218626 : Nat := 24946715904437079659903

theorem tailTrace_218626 : CollatzResearch.WordTrace tailWord_218626 prefixEnd_218626 24946715904437079659903 := by
  unfold tailWord_218626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993486326490703798312933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5315963537308543462167821 1993486326490703798312933)
  ·
    refine ⟨373778686217006962183675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1993486326490703798312933 373778686217006962183675)
    ·
      refine ⟨560668029325510443275513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373778686217006962183675 560668029325510443275513)
      ·
        refine ⟨420501021994132832456635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560668029325510443275513 420501021994132832456635)
        ·
          refine ⟨630751532991199248684953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420501021994132832456635 630751532991199248684953)
          ·
            refine ⟨473063649743399436513715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630751532991199248684953 473063649743399436513715)
            ·
              refine ⟨709595474615099154770573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473063649743399436513715 709595474615099154770573)
              ·
                refine ⟨266098302980662183038965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 709595474615099154770573 266098302980662183038965)
                ·
                  refine ⟨24946715904437079659903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266098302980662183038965 24946715904437079659903)
                  ·
                    rfl

theorem cell22_218626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_218626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218626 prefixEnd_218626 := by exact prefixLift 218626
  have htrace : WordTrace (prefixWord ++ tailWord_218626) baseStart_218626 baseEnd_218626 := by
    simpa [prefixWord, tailWord_218626, baseEnd_218626] using wordTrace_append hprefix tailTrace_218626
  have hstable : (prefixWord ++ tailWord_218626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218626).length < 2 ^ (prefixWord ++ tailWord_218626).sum := by decide
  have hdescent : baseEnd_218626 < baseStart_218626 := by decide
  rcases family_descends (prefixWord ++ tailWord_218626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218701 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_218701 : Nat := 118140960795 + 218701 * 2 ^ 59
def prefixEnd_218701 : Nat := 4983230072969 + 3 ^ 40 * 218701 * 2
def baseEnd_218701 : Nat := 74865821746036043354479

theorem tailTrace_218701 : CollatzResearch.WordTrace tailWord_218701 prefixEnd_218701 74865821746036043354479 := by
  unfold tailWord_218701
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976680780691103002231957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5317787187127402001487971 7976680780691103002231957)
  ·
    refine ⟨373906911594895453229623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7976680780691103002231957 373906911594895453229623)
    ·
      refine ⟨560860367392343179844435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373906911594895453229623 560860367392343179844435)
      ·
        refine ⟨841290551088514769766653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560860367392343179844435 841290551088514769766653)
        ·
          refine ⟨315483956658193038662495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841290551088514769766653 315483956658193038662495)
          ·
            refine ⟨473225934987289557993743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315483956658193038662495 473225934987289557993743)
            ·
              refine ⟨709838902480934336990615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473225934987289557993743 709838902480934336990615)
              ·
                refine ⟨1064758353721401505485923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709838902480934336990615 1064758353721401505485923)
                ·
                  refine ⟨1597137530582102258228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064758353721401505485923 1597137530582102258228885)
                  ·
                    refine ⟨74865821746036043354479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1597137530582102258228885 74865821746036043354479)
                    ·
                      rfl

theorem cell22_218701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_218701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218701 prefixEnd_218701 := by exact prefixLift 218701
  have htrace : WordTrace (prefixWord ++ tailWord_218701) baseStart_218701 baseEnd_218701 := by
    simpa [prefixWord, tailWord_218701, baseEnd_218701] using wordTrace_append hprefix tailTrace_218701
  have hstable : (prefixWord ++ tailWord_218701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218701).length < 2 ^ (prefixWord ++ tailWord_218701).sum := by decide
  have hdescent : baseEnd_218701 < baseStart_218701 := by decide
  rcases family_descends (prefixWord ++ tailWord_218701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218782 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_218782 : Nat := 118140960795 + 218782 * 2 ^ 59
def prefixEnd_218782 : Nat := 4983230072969 + 3 ^ 40 * 218782 * 2
def baseEnd_218782 : Nat := 74893549701378832079231

theorem tailTrace_218782 : CollatzResearch.WordTrace tailWord_218782 prefixEnd_218782 74893549701378832079231 := by
  unfold tailWord_218782
  simp only [CollatzResearch.WordTrace]
  refine ⟨997454386674706729491325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5319756728931769223953733 997454386674706729491325)
  ·
    refine ⟨374045395003015023559247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 997454386674706729491325 374045395003015023559247)
    ·
      refine ⟨561068092504522535338871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374045395003015023559247 561068092504522535338871)
      ·
        refine ⟨841602138756783803008307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561068092504522535338871 841602138756783803008307)
        ·
          refine ⟨1262403208135175704512461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841602138756783803008307 1262403208135175704512461)
          ·
            refine ⟨473401203050690889192173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1262403208135175704512461 473401203050690889192173)
            ·
              refine ⟨177525451144009083447065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473401203050690889192173 177525451144009083447065)
              ·
                refine ⟨133144088358006812585299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177525451144009083447065 133144088358006812585299)
                ·
                  refine ⟨199716132537010218877949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133144088358006812585299 199716132537010218877949)
                  ·
                    refine ⟨74893549701378832079231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199716132537010218877949 74893549701378832079231)
                    ·
                      rfl

theorem cell22_218782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_218782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218782 prefixEnd_218782 := by exact prefixLift 218782
  have htrace : WordTrace (prefixWord ++ tailWord_218782) baseStart_218782 baseEnd_218782 := by
    simpa [prefixWord, tailWord_218782, baseEnd_218782] using wordTrace_append hprefix tailTrace_218782
  have hstable : (prefixWord ++ tailWord_218782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218782).length < 2 ^ (prefixWord ++ tailWord_218782).sum := by decide
  have hdescent : baseEnd_218782 < baseStart_218782 := by decide
  rcases family_descends (prefixWord ++ tailWord_218782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218789 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 6]
def baseStart_218789 : Nat := 118140960795 + 218789 * 2 ^ 59
def prefixEnd_218789 : Nat := 4983230072969 + 3 ^ 40 * 218789 * 2
def baseEnd_218789 : Nat := 24965315314811049051403

theorem tailTrace_218789 : CollatzResearch.WordTrace tailWord_218789 prefixEnd_218789 24965315314811049051403 := by
  unfold tailWord_218789
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979890404372294031435421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5319926936248196020956947 7979890404372294031435421)
  ·
    refine ⟨2992458901639610261788283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7979890404372294031435421 2992458901639610261788283)
    ·
      refine ⟨4488688352459415392682425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2992458901639610261788283 4488688352459415392682425)
      ·
        refine ⟨3366516264344561544511819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4488688352459415392682425 3366516264344561544511819)
        ·
          refine ⟨5049774396516842316767729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366516264344561544511819 5049774396516842316767729)
          ·
            refine ⟨3787330797387631737575797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5049774396516842316767729 3787330797387631737575797)
            ·
              refine ⟨355062262255090475397731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3787330797387631737575797 355062262255090475397731)
              ·
                refine ⟨532593393382635713096597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355062262255090475397731 532593393382635713096597)
                ·
                  refine ⟨24965315314811049051403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 532593393382635713096597 24965315314811049051403)
                  ·
                    rfl

theorem cell22_218789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_218789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218789 prefixEnd_218789 := by exact prefixLift 218789
  have htrace : WordTrace (prefixWord ++ tailWord_218789) baseStart_218789 baseEnd_218789 := by
    simpa [prefixWord, tailWord_218789, baseEnd_218789] using wordTrace_append hprefix tailTrace_218789
  have hstable : (prefixWord ++ tailWord_218789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218789).length < 2 ^ (prefixWord ++ tailWord_218789).sum := by decide
  have hdescent : baseEnd_218789 < baseStart_218789 := by decide
  rcases family_descends (prefixWord ++ tailWord_218789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218834 : List Nat := [3, 2, 2, 2, 2, 11]
def baseStart_218834 : Nat := 118140960795 + 218834 * 2 ^ 59
def prefixEnd_218834 : Nat := 4983230072969 + 3 ^ 40 * 218834 * 2
def baseEnd_218834 : Nat := 924831485976148515791

theorem tailTrace_218834 : CollatzResearch.WordTrace tailWord_218834 prefixEnd_218834 924831485976148515791 := by
  unfold tailWord_218834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995382922302316679205889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5321021126139511144549037 1995382922302316679205889)
  ·
    refine ⟨1496537191726737509404417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1995382922302316679205889 1496537191726737509404417)
    ·
      refine ⟨1122402893795053132053313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496537191726737509404417 1122402893795053132053313)
      ·
        refine ⟨841802170346289849039985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1122402893795053132053313 841802170346289849039985)
        ·
          refine ⟨631351627759717386779989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841802170346289849039985 631351627759717386779989)
          ·
            refine ⟨924831485976148515791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 631351627759717386779989 924831485976148515791)
            ·
              rfl

theorem cell22_218834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 11].length) (baseStart_218834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218834 prefixEnd_218834 := by exact prefixLift 218834
  have htrace : WordTrace (prefixWord ++ tailWord_218834) baseStart_218834 baseEnd_218834 := by
    simpa [prefixWord, tailWord_218834, baseEnd_218834] using wordTrace_append hprefix tailTrace_218834
  have hstable : (prefixWord ++ tailWord_218834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218834).length < 2 ^ (prefixWord ++ tailWord_218834).sum := by decide
  have hdescent : baseEnd_218834 < baseStart_218834 := by decide
  rcases family_descends (prefixWord ++ tailWord_218834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218883 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 1, 3]
def baseStart_218883 : Nat := 118140960795 + 218883 * 2 ^ 59
def prefixEnd_218883 : Nat := 4983230072969 + 3 ^ 40 * 218883 * 2
def baseEnd_218883 : Nat := 74928124065448235303921

theorem tailTrace_218883 : CollatzResearch.WordTrace tailWord_218883 prefixEnd_218883 74928124065448235303921 := by
  unfold tailWord_218883
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983318866031748085357303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5322212577354498723571535 7983318866031748085357303)
  ·
    refine ⟨11974978299047622128035955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7983318866031748085357303 11974978299047622128035955)
    ·
      refine ⟨17962467448571433192053933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11974978299047622128035955 17962467448571433192053933)
      ·
        refine ⟨6735925293214287447020225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17962467448571433192053933 6735925293214287447020225)
        ·
          refine ⟨5051943969910715585265169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6735925293214287447020225 5051943969910715585265169)
          ·
            refine ⟨3788957977433036688948877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5051943969910715585265169 3788957977433036688948877)
            ·
              refine ⟨1420859241537388758355829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3788957977433036688948877 1420859241537388758355829)
              ·
                refine ⟨133205553894130196095859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1420859241537388758355829 133205553894130196095859)
                ·
                  refine ⟨199808330841195294143789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133205553894130196095859 199808330841195294143789)
                  ·
                    refine ⟨74928124065448235303921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199808330841195294143789 74928124065448235303921)
                    ·
                      rfl

theorem cell22_218883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 3].length) (baseStart_218883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218883 prefixEnd_218883 := by exact prefixLift 218883
  have htrace : WordTrace (prefixWord ++ tailWord_218883) baseStart_218883 baseEnd_218883 := by
    simpa [prefixWord, tailWord_218883, baseEnd_218883] using wordTrace_append hprefix tailTrace_218883
  have hstable : (prefixWord ++ tailWord_218883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218883).length < 2 ^ (prefixWord ++ tailWord_218883).sum := by decide
  have hdescent : baseEnd_218883 < baseStart_218883 := by decide
  rcases family_descends (prefixWord ++ tailWord_218883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218913 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 5]
def baseStart_218913 : Nat := 118140960795 + 218913 * 2 ^ 59
def prefixEnd_218913 : Nat := 4983230072969 + 3 ^ 40 * 218913 * 2
def baseEnd_218913 : Nat := 24979464559512719017943

theorem tailTrace_218913 : CollatzResearch.WordTrace tailWord_218913 prefixEnd_218913 24979464559512719017943 := by
  unfold tailWord_218913
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984413055923063208949393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5322942037282042139299595 7984413055923063208949393)
  ·
    refine ⟨5988309791942297406712045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7984413055923063208949393 5988309791942297406712045)
    ·
      refine ⟨2245616171978361527517017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5988309791942297406712045 2245616171978361527517017)
      ·
        refine ⟨1684212128983771145637763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2245616171978361527517017 1684212128983771145637763)
        ·
          refine ⟨2526318193475656718456645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684212128983771145637763 2526318193475656718456645)
          ·
            refine ⟨473684661276685634710621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2526318193475656718456645 473684661276685634710621)
            ·
              refine ⟨177631747978757113016483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473684661276685634710621 177631747978757113016483)
              ·
                refine ⟨266447621968135669524725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177631747978757113016483 266447621968135669524725)
                ·
                  refine ⟨24979464559512719017943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266447621968135669524725 24979464559512719017943)
                  ·
                    rfl

theorem cell22_218913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_218913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218913 prefixEnd_218913 := by exact prefixLift 218913
  have htrace : WordTrace (prefixWord ++ tailWord_218913) baseStart_218913 baseEnd_218913 := by
    simpa [prefixWord, tailWord_218913, baseEnd_218913] using wordTrace_append hprefix tailTrace_218913
  have hstable : (prefixWord ++ tailWord_218913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218913).length < 2 ^ (prefixWord ++ tailWord_218913).sum := by decide
  have hdescent : baseEnd_218913 < baseStart_218913 := by decide
  rcases family_descends (prefixWord ++ tailWord_218913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218934 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_218934 : Nat := 118140960795 + 218934 * 2 ^ 59
def prefixEnd_218934 : Nat := 4983230072969 + 3 ^ 40 * 218934 * 2
def baseEnd_218934 : Nat := 74945582407701102278765

theorem tailTrace_218934 : CollatzResearch.WordTrace tailWord_218934 prefixEnd_218934 74945582407701102278765 := by
  unfold tailWord_218934
  simp only [CollatzResearch.WordTrace]
  refine ⟨499073686802936487216491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5323452659231322530309237 499073686802936487216491)
  ·
    refine ⟨748610530204404730824737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499073686802936487216491 748610530204404730824737)
    ·
      refine ⟨561457897653303548118553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748610530204404730824737 561457897653303548118553)
      ·
        refine ⟨421093423239977661088915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561457897653303548118553 421093423239977661088915)
        ·
          refine ⟨631640134859966491633373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421093423239977661088915 631640134859966491633373)
          ·
            refine ⟨236865050572487434362515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 631640134859966491633373 236865050572487434362515)
            ·
              refine ⟨355297575858731151543773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236865050572487434362515 355297575858731151543773)
              ·
                refine ⟨133236590947024181828915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355297575858731151543773 133236590947024181828915)
                ·
                  refine ⟨199854886420536272743373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133236590947024181828915 199854886420536272743373)
                  ·
                    refine ⟨74945582407701102278765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199854886420536272743373 74945582407701102278765)
                    ·
                      rfl

theorem cell22_218934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_218934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218934 prefixEnd_218934 := by exact prefixLift 218934
  have htrace : WordTrace (prefixWord ++ tailWord_218934) baseStart_218934 baseEnd_218934 := by
    simpa [prefixWord, tailWord_218934, baseEnd_218934] using wordTrace_append hprefix tailTrace_218934
  have hstable : (prefixWord ++ tailWord_218934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218934).length < 2 ^ (prefixWord ++ tailWord_218934).sum := by decide
  have hdescent : baseEnd_218934 < baseStart_218934 := by decide
  rcases family_descends (prefixWord ++ tailWord_218934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218988 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_218988 : Nat := 118140960795 + 218988 * 2 ^ 59
def prefixEnd_218988 : Nat := 4983230072969 + 3 ^ 40 * 218988 * 2
def baseEnd_218988 : Nat := 74964067711262961428599

theorem tailTrace_218988 : CollatzResearch.WordTrace tailWord_218988 prefixEnd_218988 74964067711262961428599 := by
  unfold tailWord_218988
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993574265325675508964809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5324765687100900678619745 3993574265325675508964809)
  ·
    refine ⟨2995180698994256631723607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3993574265325675508964809 2995180698994256631723607)
    ·
      refine ⟨4492771048491384947585411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995180698994256631723607 4492771048491384947585411)
      ·
        refine ⟨6739156572737077421378117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492771048491384947585411 6739156572737077421378117)
        ·
          refine ⟨1263591857388202016508397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6739156572737077421378117 1263591857388202016508397)
          ·
            refine ⟨473846946520575756190649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263591857388202016508397 473846946520575756190649)
            ·
              refine ⟨355385209890431817142987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473846946520575756190649 355385209890431817142987)
              ·
                refine ⟨533077814835647725714481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355385209890431817142987 533077814835647725714481)
                ·
                  refine ⟨399808361126735794285861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533077814835647725714481 399808361126735794285861)
                  ·
                    refine ⟨74964067711262961428599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399808361126735794285861 74964067711262961428599)
                    ·
                      rfl

theorem cell22_218988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_218988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_218988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_218988 prefixEnd_218988 := by exact prefixLift 218988
  have htrace : WordTrace (prefixWord ++ tailWord_218988) baseStart_218988 baseEnd_218988 := by
    simpa [prefixWord, tailWord_218988, baseEnd_218988] using wordTrace_append hprefix tailTrace_218988
  have hstable : (prefixWord ++ tailWord_218988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218988).length < 2 ^ (prefixWord ++ tailWord_218988).sum := by decide
  have hdescent : baseEnd_218988 < baseStart_218988 := by decide
  rcases family_descends (prefixWord ++ tailWord_218988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219009 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 4]
def baseStart_219009 : Nat := 118140960795 + 219009 * 2 ^ 59
def prefixEnd_219009 : Nat := 4983230072969 + 3 ^ 40 * 219009 * 2
def baseEnd_219009 : Nat := 24990418813475302217845

theorem tailTrace_219009 : CollatzResearch.WordTrace tailWord_219009 prefixEnd_219009 24990418813475302217845 := by
  unfold tailWord_219009
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987914463575271604444081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5325276309050181069629387 7987914463575271604444081)
  ·
    refine ⟨5990935847681453703333061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7987914463575271604444081 5990935847681453703333061)
    ·
      refine ⟨1123300471440272569374949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5990935847681453703333061 1123300471440272569374949)
      ·
        refine ⟨210618838395051106757803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1123300471440272569374949 210618838395051106757803)
        ·
          refine ⟨315928257592576660136705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210618838395051106757803 315928257592576660136705)
          ·
            refine ⟨236946193194432495102529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315928257592576660136705 236946193194432495102529)
            ·
              refine ⟨177709644895824371326897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236946193194432495102529 177709644895824371326897)
              ·
                refine ⟨133282233671868278495173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177709644895824371326897 133282233671868278495173)
                ·
                  refine ⟨24990418813475302217845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133282233671868278495173 24990418813475302217845)
                  ·
                    rfl

theorem cell22_219009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_219009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219009 prefixEnd_219009 := by exact prefixLift 219009
  have htrace : WordTrace (prefixWord ++ tailWord_219009) baseStart_219009 baseEnd_219009 := by
    simpa [prefixWord, tailWord_219009, baseEnd_219009] using wordTrace_append hprefix tailTrace_219009
  have hstable : (prefixWord ++ tailWord_219009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219009).length < 2 ^ (prefixWord ++ tailWord_219009).sum := by decide
  have hdescent : baseEnd_219009 < baseStart_219009 := by decide
  rcases family_descends (prefixWord ++ tailWord_219009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219093 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 6]
def baseStart_219093 : Nat := 118140960795 + 219093 * 2 ^ 59
def prefixEnd_219093 : Nat := 4983230072969 + 3 ^ 40 * 219093 * 2
def baseEnd_219093 : Nat := 25000003785692562517759

theorem tailTrace_219093 : CollatzResearch.WordTrace tailWord_219093 prefixEnd_219093 25000003785692562517759 := by
  unfold tailWord_219093
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990978195270953950501933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5327318796847302633667955 7990978195270953950501933)
  ·
    refine ⟨2996616823226607731438225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7990978195270953950501933 2996616823226607731438225)
    ·
      refine ⟨2247462617419955798578669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996616823226607731438225 2247462617419955798578669)
      ·
        refine ⟨842798481532483424467001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2247462617419955798578669 842798481532483424467001)
        ·
          refine ⟨632098861149362568350251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842798481532483424467001 632098861149362568350251)
          ·
            refine ⟨948148291724043852525377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632098861149362568350251 948148291724043852525377)
            ·
              refine ⟨711111218793032889394033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948148291724043852525377 711111218793032889394033)
              ·
                refine ⟨533333414094774667045525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711111218793032889394033 533333414094774667045525)
                ·
                  refine ⟨25000003785692562517759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 533333414094774667045525 25000003785692562517759)
                  ·
                    rfl

theorem cell22_219093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_219093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219093 prefixEnd_219093 := by exact prefixLift 219093
  have htrace : WordTrace (prefixWord ++ tailWord_219093) baseStart_219093 baseEnd_219093 := by
    simpa [prefixWord, tailWord_219093, baseEnd_219093] using wordTrace_append hprefix tailTrace_219093
  have hstable : (prefixWord ++ tailWord_219093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219093).length < 2 ^ (prefixWord ++ tailWord_219093).sum := by decide
  have hdescent : baseEnd_219093 < baseStart_219093 := by decide
  rcases family_descends (prefixWord ++ tailWord_219093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219108 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_219108 : Nat := 118140960795 + 219108 * 2 ^ 59
def prefixEnd_219108 : Nat := 4983230072969 + 3 ^ 40 * 219108 * 2
def baseEnd_219108 : Nat := 75005146163622648428231

theorem tailTrace_219108 : CollatzResearch.WordTrace tailWord_219108 prefixEnd_219108 75005146163622648428231 := by
  unfold tailWord_219108
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995762645108305756148989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5327683526811074341531985 3995762645108305756148989)
  ·
    refine ⟨1498410991915614658555871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3995762645108305756148989 1498410991915614658555871)
    ·
      refine ⟨2247616487873421987833807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1498410991915614658555871 2247616487873421987833807)
      ·
        refine ⟨3371424731810132981750711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247616487873421987833807 3371424731810132981750711)
        ·
          refine ⟨5057137097715199472626067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371424731810132981750711 5057137097715199472626067)
          ·
            refine ⟨7585705646572799208939101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057137097715199472626067 7585705646572799208939101)
            ·
              refine ⟨2844639617464799703352163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7585705646572799208939101 2844639617464799703352163)
              ·
                refine ⟨4266959426197199555028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844639617464799703352163 4266959426197199555028245)
                ·
                  refine ⟨200013723102993729141949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4266959426197199555028245 200013723102993729141949)
                  ·
                    refine ⟨75005146163622648428231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200013723102993729141949 75005146163622648428231)
                    ·
                      rfl

theorem cell22_219108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_219108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219108 prefixEnd_219108 := by exact prefixLift 219108
  have htrace : WordTrace (prefixWord ++ tailWord_219108) baseStart_219108 baseEnd_219108 := by
    simpa [prefixWord, tailWord_219108, baseEnd_219108] using wordTrace_append hprefix tailTrace_219108
  have hstable : (prefixWord ++ tailWord_219108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219108).length < 2 ^ (prefixWord ++ tailWord_219108).sum := by decide
  have hdescent : baseEnd_219108 < baseStart_219108 := by decide
  rcases family_descends (prefixWord ++ tailWord_219108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219136 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_219136 : Nat := 118140960795 + 219136 * 2 ^ 59
def prefixEnd_219136 : Nat := 4983230072969 + 3 ^ 40 * 219136 * 2
def baseEnd_219136 : Nat := 75014731135839908728145

theorem tailTrace_219136 : CollatzResearch.WordTrace tailWord_219136 prefixEnd_219136 75014731135839908728145 := by
  unfold tailWord_219136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3996273267057586147158631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5328364356076781529544841 3996273267057586147158631)
  ·
    refine ⟨5994409900586379220737947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3996273267057586147158631 5994409900586379220737947)
    ·
      refine ⟨8991614850879568831106921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5994409900586379220737947 8991614850879568831106921)
      ·
        refine ⟨6743711138159676623330191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8991614850879568831106921 6743711138159676623330191)
        ·
          refine ⟨10115566707239514934995287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743711138159676623330191 10115566707239514934995287)
          ·
            refine ⟨15173350060859272402492931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115566707239514934995287 15173350060859272402492931)
            ·
              refine ⟨22760025091288908603739397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15173350060859272402492931 22760025091288908603739397)
              ·
                refine ⟨4267504704616670363201137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22760025091288908603739397 4267504704616670363201137)
                ·
                  refine ⟨3200628528462502772400853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4267504704616670363201137 3200628528462502772400853)
                  ·
                    refine ⟨75014731135839908728145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3200628528462502772400853 75014731135839908728145)
                    ·
                      rfl

theorem cell22_219136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_219136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219136 prefixEnd_219136 := by exact prefixLift 219136
  have htrace : WordTrace (prefixWord ++ tailWord_219136) baseStart_219136 baseEnd_219136 := by
    simpa [prefixWord, tailWord_219136, baseEnd_219136] using wordTrace_append hprefix tailTrace_219136
  have hstable : (prefixWord ++ tailWord_219136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219136).length < 2 ^ (prefixWord ++ tailWord_219136).sum := by decide
  have hdescent : baseEnd_219136 < baseStart_219136 := by decide
  rcases family_descends (prefixWord ++ tailWord_219136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219234 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_219234 : Nat := 118140960795 + 219234 * 2 ^ 59
def prefixEnd_219234 : Nat := 4983230072969 + 3 ^ 40 * 219234 * 2
def baseEnd_219234 : Nat := 25016092846200106592615

theorem tailTrace_219234 : CollatzResearch.WordTrace tailWord_219234 prefixEnd_219234 25016092846200106592615 := by
  unfold tailWord_219234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999030221940033757846189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5330747258506756687589837 1999030221940033757846189)
  ·
    refine ⟨749636333227512659192321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1999030221940033757846189 749636333227512659192321)
    ·
      refine ⟨562227249920634494394241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 749636333227512659192321 562227249920634494394241)
      ·
        refine ⟨421670437440475870795681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562227249920634494394241 421670437440475870795681)
        ·
          refine ⟨316252828080356903096761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421670437440475870795681 316252828080356903096761)
          ·
            refine ⟨237189621060267677322571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316252828080356903096761 237189621060267677322571)
            ·
              refine ⟨355784431590401515983857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237189621060267677322571 355784431590401515983857)
              ·
                refine ⟨266838323692801136987893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355784431590401515983857 266838323692801136987893)
                ·
                  refine ⟨25016092846200106592615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266838323692801136987893 25016092846200106592615)
                  ·
                    rfl

theorem cell22_219234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_219234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219234 prefixEnd_219234 := by exact prefixLift 219234
  have htrace : WordTrace (prefixWord ++ tailWord_219234) baseStart_219234 baseEnd_219234 := by
    simpa [prefixWord, tailWord_219234, baseEnd_219234] using wordTrace_append hprefix tailTrace_219234
  have hstable : (prefixWord ++ tailWord_219234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219234).length < 2 ^ (prefixWord ++ tailWord_219234).sum := by decide
  have hdescent : baseEnd_219234 < baseStart_219234 := by decide
  rcases family_descends (prefixWord ++ tailWord_219234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219245 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 6]
def baseStart_219245 : Nat := 118140960795 + 219245 * 2 ^ 59
def prefixEnd_219245 : Nat := 4983230072969 + 3 ^ 40 * 219245 * 2
def baseEnd_219245 : Nat := 25017348021133319250937

theorem tailTrace_219245 : CollatzResearch.WordTrace tailWord_219245 prefixEnd_219245 25017348021133319250937 := by
  unfold tailWord_219245
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996522090720283910035189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5331014727146855940023459 7996522090720283910035189)
  ·
    refine ⟨749673946005026616565799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7996522090720283910035189 749673946005026616565799)
    ·
      refine ⟨1124510919007539924848699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749673946005026616565799 1124510919007539924848699)
      ·
        refine ⟨1686766378511309887273049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124510919007539924848699 1686766378511309887273049)
        ·
          refine ⟨1265074783883482415454787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1686766378511309887273049 1265074783883482415454787)
          ·
            refine ⟨1897612175825223623182181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265074783883482415454787 1897612175825223623182181)
            ·
              refine ⟨355802282967229429346659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1897612175825223623182181 355802282967229429346659)
              ·
                refine ⟨533703424450844144019989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355802282967229429346659 533703424450844144019989)
                ·
                  refine ⟨25017348021133319250937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 533703424450844144019989 25017348021133319250937)
                  ·
                    rfl

theorem cell22_219245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_219245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219245 prefixEnd_219245 := by exact prefixLift 219245
  have htrace : WordTrace (prefixWord ++ tailWord_219245) baseStart_219245 baseEnd_219245 := by
    simpa [prefixWord, tailWord_219245, baseEnd_219245] using wordTrace_append hprefix tailTrace_219245
  have hstable : (prefixWord ++ tailWord_219245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219245).length < 2 ^ (prefixWord ++ tailWord_219245).sum := by decide
  have hdescent : baseEnd_219245 < baseStart_219245 := by decide
  rcases family_descends (prefixWord ++ tailWord_219245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219260 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_219260 : Nat := 118140960795 + 219260 * 2 ^ 59
def prefixEnd_219260 : Nat := 4983230072969 + 3 ^ 40 * 219260 * 2
def baseEnd_219260 : Nat := 75057178869944918627765

theorem tailTrace_219260 : CollatzResearch.WordTrace tailWord_219260 prefixEnd_219260 75057178869944918627765 := by
  unfold tailWord_219260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998534592832970735915617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5331379457110627647887489 3998534592832970735915617)
  ·
    refine ⟨2998900944624728051936713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3998534592832970735915617 2998900944624728051936713)
    ·
      refine ⟨2249175708468546038952535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2998900944624728051936713 2249175708468546038952535)
      ·
        refine ⟨3373763562702819058428803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249175708468546038952535 3373763562702819058428803)
        ·
          refine ⟨5060645344054228587643205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373763562702819058428803 5060645344054228587643205)
          ·
            refine ⟨948871002010167860183101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5060645344054228587643205 948871002010167860183101)
            ·
              refine ⟨355826625753812947568663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 948871002010167860183101 355826625753812947568663)
              ·
                refine ⟨533739938630719421352995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355826625753812947568663 533739938630719421352995)
                ·
                  refine ⟨800609907946079132029493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533739938630719421352995 800609907946079132029493)
                  ·
                    refine ⟨75057178869944918627765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 800609907946079132029493 75057178869944918627765)
                    ·
                      rfl

theorem cell22_219260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_219260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219260 prefixEnd_219260 := by exact prefixLift 219260
  have htrace : WordTrace (prefixWord ++ tailWord_219260) baseStart_219260 baseEnd_219260 := by
    simpa [prefixWord, tailWord_219260, baseEnd_219260] using wordTrace_append hprefix tailTrace_219260
  have hstable : (prefixWord ++ tailWord_219260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219260).length < 2 ^ (prefixWord ++ tailWord_219260).sum := by decide
  have hdescent : baseEnd_219260 < baseStart_219260 := by decide
  rcases family_descends (prefixWord ++ tailWord_219260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219273 : List Nat := [1, 2, 1, 1, 4, 2, 3, 8]
def baseStart_219273 : Nat := 118140960795 + 219273 * 2 ^ 59
def prefixEnd_219273 : Nat := 4983230072969 + 3 ^ 40 * 219273 * 2
def baseEnd_219273 : Nat := 8340181003957468672525

theorem tailTrace_219273 : CollatzResearch.WordTrace tailWord_219273 prefixEnd_219273 8340181003957468672525 := by
  unfold tailWord_219273
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997543334618844692054473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5331695556412563128036315 7997543334618844692054473)
  ·
    refine ⟨5998157500964133519040855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7997543334618844692054473 5998157500964133519040855)
    ·
      refine ⟨8997236251446200278561283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998157500964133519040855 8997236251446200278561283)
      ·
        refine ⟨13495854377169300417841925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8997236251446200278561283 13495854377169300417841925)
        ·
          refine ⟨2530472695719243828345361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13495854377169300417841925 2530472695719243828345361)
          ·
            refine ⟨1897854521789432871259021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2530472695719243828345361 1897854521789432871259021)
            ·
              refine ⟨711695445671037326722133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1897854521789432871259021 711695445671037326722133)
              ·
                refine ⟨8340181003957468672525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 711695445671037326722133 8340181003957468672525)
                ·
                  rfl

theorem cell22_219273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 8].length) (baseStart_219273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219273 prefixEnd_219273 := by exact prefixLift 219273
  have htrace : WordTrace (prefixWord ++ tailWord_219273) baseStart_219273 baseEnd_219273 := by
    simpa [prefixWord, tailWord_219273, baseEnd_219273] using wordTrace_append hprefix tailTrace_219273
  have hstable : (prefixWord ++ tailWord_219273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219273).length < 2 ^ (prefixWord ++ tailWord_219273).sum := by decide
  have hdescent : baseEnd_219273 < baseStart_219273 := by decide
  rcases family_descends (prefixWord ++ tailWord_219273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219352 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_219352 : Nat := 118140960795 + 219352 * 2 ^ 59
def prefixEnd_219352 : Nat := 4983230072969 + 3 ^ 40 * 219352 * 2
def baseEnd_219352 : Nat := 25029557450029115109161

theorem tailTrace_219352 : CollatzResearch.WordTrace tailWord_219352 prefixEnd_219352 25029557450029115109161 := by
  unfold tailWord_219352
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000212350666320592090155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5333616467555094122786873 4000212350666320592090155)
  ·
    refine ⟨6000318525999480888135233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4000212350666320592090155 6000318525999480888135233)
    ·
      refine ⟨4500238894499610666101425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6000318525999480888135233 4500238894499610666101425)
      ·
        refine ⟨3375179170874707999576069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500238894499610666101425 3375179170874707999576069)
        ·
          refine ⟨632846094539007749920513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3375179170874707999576069 632846094539007749920513)
          ·
            refine ⟨474634570904255812440385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632846094539007749920513 474634570904255812440385)
            ·
              refine ⟨355975928178191859330289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474634570904255812440385 355975928178191859330289)
              ·
                refine ⟨266981946133643894497717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355975928178191859330289 266981946133643894497717)
                ·
                  refine ⟨25029557450029115109161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266981946133643894497717 25029557450029115109161)
                  ·
                    rfl

theorem cell22_219352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_219352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219352 prefixEnd_219352 := by exact prefixLift 219352
  have htrace : WordTrace (prefixWord ++ tailWord_219352) baseStart_219352 baseEnd_219352 := by
    simpa [prefixWord, tailWord_219352, baseEnd_219352] using wordTrace_append hprefix tailTrace_219352
  have hstable : (prefixWord ++ tailWord_219352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219352).length < 2 ^ (prefixWord ++ tailWord_219352).sum := by decide
  have hdescent : baseEnd_219352 < baseStart_219352 := by decide
  rcases family_descends (prefixWord ++ tailWord_219352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219367 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 2, 5]
def baseStart_219367 : Nat := 118140960795 + 219367 * 2 ^ 59
def prefixEnd_219367 : Nat := 4983230072969 + 3 ^ 40 * 219367 * 2
def baseEnd_219367 : Nat := 75093807156632306202437

theorem tailTrace_219367 : CollatzResearch.WordTrace tailWord_219367 prefixEnd_219367 75093807156632306202437 := by
  unfold tailWord_219367
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000971796278298745976355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5333981197518865830650903 8000971796278298745976355)
  ·
    refine ⟨12001457694417448118964533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000971796278298745976355 12001457694417448118964533)
    ·
      refine ⟨1125136658851635761152925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12001457694417448118964533 1125136658851635761152925)
      ·
        refine ⟨421926247069363410432347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1125136658851635761152925 421926247069363410432347)
        ·
          refine ⟨632889370604045115648521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421926247069363410432347 632889370604045115648521)
          ·
            refine ⟨474667027953033836736391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632889370604045115648521 474667027953033836736391)
            ·
              refine ⟨712000541929550755104587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474667027953033836736391 712000541929550755104587)
              ·
                refine ⟨1068000812894326132656881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712000541929550755104587 1068000812894326132656881)
                ·
                  refine ⟨801000609670744599492661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1068000812894326132656881 801000609670744599492661)
                  ·
                    refine ⟨75093807156632306202437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 801000609670744599492661 75093807156632306202437)
                    ·
                      rfl

theorem cell22_219367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_219367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219367 prefixEnd_219367 := by exact prefixLift 219367
  have htrace : WordTrace (prefixWord ++ tailWord_219367) baseStart_219367 baseEnd_219367 := by
    simpa [prefixWord, tailWord_219367, baseEnd_219367] using wordTrace_append hprefix tailTrace_219367
  have hstable : (prefixWord ++ tailWord_219367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219367).length < 2 ^ (prefixWord ++ tailWord_219367).sum := by decide
  have hdescent : baseEnd_219367 < baseStart_219367 := by decide
  rcases family_descends (prefixWord ++ tailWord_219367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219382 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_219382 : Nat := 118140960795 + 219382 * 2 ^ 59
def prefixEnd_219382 : Nat := 4983230072969 + 3 ^ 40 * 219382 * 2
def baseEnd_219382 : Nat := 75098941963177267077391

theorem tailTrace_219382 : CollatzResearch.WordTrace tailWord_219382 prefixEnd_219382 75098941963177267077391 := by
  unfold tailWord_219382
  simp only [CollatzResearch.WordTrace]
  refine ⟨500094930701497269235775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5334345927482637538514933 500094930701497269235775)
  ·
    refine ⟨750142396052245903853663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 500094930701497269235775 750142396052245903853663)
    ·
      refine ⟨1125213594078368855780495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750142396052245903853663 1125213594078368855780495)
      ·
        refine ⟨1687820391117553283670743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125213594078368855780495 1687820391117553283670743)
        ·
          refine ⟨2531730586676329925506115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687820391117553283670743 2531730586676329925506115)
          ·
            refine ⟨3797595880014494888259173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531730586676329925506115 3797595880014494888259173)
            ·
              refine ⟨712049227502717791548595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3797595880014494888259173 712049227502717791548595)
              ·
                refine ⟨1068073841254076687322893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712049227502717791548595 1068073841254076687322893)
                ·
                  refine ⟨400527690470278757746085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068073841254076687322893 400527690470278757746085)
                  ·
                    refine ⟨75098941963177267077391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400527690470278757746085 75098941963177267077391)
                    ·
                      rfl

theorem cell22_219382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_219382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219382 prefixEnd_219382 := by exact prefixLift 219382
  have htrace : WordTrace (prefixWord ++ tailWord_219382) baseStart_219382 baseEnd_219382 := by
    simpa [prefixWord, tailWord_219382, baseEnd_219382] using wordTrace_append hprefix tailTrace_219382
  have hstable : (prefixWord ++ tailWord_219382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219382).length < 2 ^ (prefixWord ++ tailWord_219382).sum := by decide
  have hdescent : baseEnd_219382 < baseStart_219382 := by decide
  rcases family_descends (prefixWord ++ tailWord_219382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219395 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 1, 5]
def baseStart_219395 : Nat := 118140960795 + 219395 * 2 ^ 59
def prefixEnd_219395 : Nat := 4983230072969 + 3 ^ 40 * 219395 * 2
def baseEnd_219395 : Nat := 75103392128849566502351

theorem tailTrace_219395 : CollatzResearch.WordTrace tailWord_219395 prefixEnd_219395 75103392128849566502351 := by
  unfold tailWord_219395
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001993040176859527995639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5334662026784573018663759 8001993040176859527995639)
  ·
    refine ⟨12002989560265289291993459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8001993040176859527995639 12002989560265289291993459)
    ·
      refine ⟨18004484340397933937990189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12002989560265289291993459 18004484340397933937990189)
      ·
        refine ⟨6751681627649225226746321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18004484340397933937990189 6751681627649225226746321)
        ·
          refine ⟨5063761220736918920059741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6751681627649225226746321 5063761220736918920059741)
          ·
            refine ⟨1898910457776344595022403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5063761220736918920059741 1898910457776344595022403)
            ·
              refine ⟨2848365686664516892533605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898910457776344595022403 2848365686664516892533605)
              ·
                refine ⟨534068566249596917350051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2848365686664516892533605 534068566249596917350051)
                ·
                  refine ⟨801102849374395376025077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534068566249596917350051 801102849374395376025077)
                  ·
                    refine ⟨75103392128849566502351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 801102849374395376025077 75103392128849566502351)
                    ·
                      rfl

theorem cell22_219395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_219395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219395 prefixEnd_219395 := by exact prefixLift 219395
  have htrace : WordTrace (prefixWord ++ tailWord_219395) baseStart_219395 baseEnd_219395 := by
    simpa [prefixWord, tailWord_219395, baseEnd_219395] using wordTrace_append hprefix tailTrace_219395
  have hstable : (prefixWord ++ tailWord_219395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219395).length < 2 ^ (prefixWord ++ tailWord_219395).sum := by decide
  have hdescent : baseEnd_219395 < baseStart_219395 := by decide
  rcases family_descends (prefixWord ++ tailWord_219395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219429 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_219429 : Nat := 118140960795 + 219429 * 2 ^ 59
def prefixEnd_219429 : Nat := 4983230072969 + 3 ^ 40 * 219429 * 2
def baseEnd_219429 : Nat := 75115031023684811152247

theorem tailTrace_219429 : CollatzResearch.WordTrace tailWord_219429 prefixEnd_219429 75115031023684811152247 := by
  unfold tailWord_219429
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003233122053683334733341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5335488748035788889822227 8003233122053683334733341)
  ·
    refine ⟨3001212420770131250525003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8003233122053683334733341 3001212420770131250525003)
    ·
      refine ⟨4501818631155196875787505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001212420770131250525003 4501818631155196875787505)
      ·
        refine ⟨3376363973366397656840629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4501818631155196875787505 3376363973366397656840629)
        ·
          refine ⟨316534122503099780328809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3376363973366397656840629 316534122503099780328809)
          ·
            refine ⟨237400591877324835246607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316534122503099780328809 237400591877324835246607)
            ·
              refine ⟨356100887815987252869911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237400591877324835246607 356100887815987252869911)
              ·
                refine ⟨534151331723980879304867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356100887815987252869911 534151331723980879304867)
                ·
                  refine ⟨801226997585971318957301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534151331723980879304867 801226997585971318957301)
                  ·
                    refine ⟨75115031023684811152247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 801226997585971318957301 75115031023684811152247)
                    ·
                      rfl

theorem cell22_219429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_219429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219429 prefixEnd_219429 := by exact prefixLift 219429
  have htrace : WordTrace (prefixWord ++ tailWord_219429) baseStart_219429 baseEnd_219429 := by
    simpa [prefixWord, tailWord_219429, baseEnd_219429] using wordTrace_append hprefix tailTrace_219429
  have hstable : (prefixWord ++ tailWord_219429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219429).length < 2 ^ (prefixWord ++ tailWord_219429).sum := by decide
  have hdescent : baseEnd_219429 < baseStart_219429 := by decide
  rcases family_descends (prefixWord ++ tailWord_219429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219442 : List Nat := [3, 2, 1, 1, 5, 1, 1, 8]
def baseStart_219442 : Nat := 118140960795 + 219442 * 2 ^ 59
def prefixEnd_219442 : Nat := 4983230072969 + 3 ^ 40 * 219442 * 2
def baseEnd_219442 : Nat := 8346609021039678953023

theorem tailTrace_219442 : CollatzResearch.WordTrace tailWord_219442 prefixEnd_219442 8346609021039678953023 := by
  unfold tailWord_219442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000926817751646638739145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5335804847337724369971053 2000926817751646638739145)
  ·
    refine ⟨1500695113313734979054359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2000926817751646638739145 1500695113313734979054359)
    ·
      refine ⟨2251042669970602468581539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500695113313734979054359 2251042669970602468581539)
      ·
        refine ⟨3376564004955903702872309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251042669970602468581539 3376564004955903702872309)
        ·
          refine ⟨316552875464615972144279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3376564004955903702872309 316552875464615972144279)
          ·
            refine ⟨474829313196923958216419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316552875464615972144279 474829313196923958216419)
            ·
              refine ⟨712243969795385937324629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474829313196923958216419 712243969795385937324629)
              ·
                refine ⟨8346609021039678953023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 712243969795385937324629 8346609021039678953023)
                ·
                  rfl

theorem cell22_219442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_219442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219442 prefixEnd_219442 := by exact prefixLift 219442
  have htrace : WordTrace (prefixWord ++ tailWord_219442) baseStart_219442 baseEnd_219442 := by
    simpa [prefixWord, tailWord_219442, baseEnd_219442] using wordTrace_append hprefix tailTrace_219442
  have hstable : (prefixWord ++ tailWord_219442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219442).length < 2 ^ (prefixWord ++ tailWord_219442).sum := by decide
  have hdescent : baseEnd_219442 < baseStart_219442 := by decide
  rcases family_descends (prefixWord ++ tailWord_219442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219474 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_219474 : Nat := 118140960795 + 219474 * 2 ^ 59
def prefixEnd_219474 : Nat := 4983230072969 + 3 ^ 40 * 219474 * 2
def baseEnd_219474 : Nat := 75130435443319693777109

theorem tailTrace_219474 : CollatzResearch.WordTrace tailWord_219474 prefixEnd_219474 75130435443319693777109 := by
  unfold tailWord_219474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001218601722664005030369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5336582937927104013414317 2001218601722664005030369)
  ·
    refine ⟨1500913951291998003772777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2001218601722664005030369 1500913951291998003772777)
    ·
      refine ⟨1125685463468998502829583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1500913951291998003772777 1125685463468998502829583)
      ·
        refine ⟨1688528195203497754244375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125685463468998502829583 1688528195203497754244375)
        ·
          refine ⟨2532792292805246631366563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688528195203497754244375 2532792292805246631366563)
          ·
            refine ⟨3799188439207869947049845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532792292805246631366563 3799188439207869947049845)
            ·
              refine ⟨356173916175737807535923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3799188439207869947049845 356173916175737807535923)
              ·
                refine ⟨534260874263606711303885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356173916175737807535923 534260874263606711303885)
                ·
                  refine ⟨200347827848852516738957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534260874263606711303885 200347827848852516738957)
                  ·
                    refine ⟨75130435443319693777109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200347827848852516738957 75130435443319693777109)
                    ·
                      rfl

theorem cell22_219474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_219474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219474 prefixEnd_219474 := by exact prefixLift 219474
  have htrace : WordTrace (prefixWord ++ tailWord_219474) baseStart_219474 baseEnd_219474 := by
    simpa [prefixWord, tailWord_219474, baseEnd_219474] using wordTrace_append hprefix tailTrace_219474
  have hstable : (prefixWord ++ tailWord_219474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219474).length < 2 ^ (prefixWord ++ tailWord_219474).sum := by decide
  have hdescent : baseEnd_219474 < baseStart_219474 := by decide
  rcases family_descends (prefixWord ++ tailWord_219474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219534 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_219534 : Nat := 118140960795 + 219534 * 2 ^ 59
def prefixEnd_219534 : Nat := 4983230072969 + 3 ^ 40 * 219534 * 2
def baseEnd_219534 : Nat := 75150974669499537276925

theorem tailTrace_219534 : CollatzResearch.WordTrace tailWord_219534 prefixEnd_219534 75150974669499537276925 := by
  unfold tailWord_219534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000882848334160783413207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5338041857782190844870437 1000882848334160783413207)
  ·
    refine ⟨1501324272501241175119811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000882848334160783413207 1501324272501241175119811)
    ·
      refine ⟨2251986408751861762679717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1501324272501241175119811 2251986408751861762679717)
      ·
        refine ⟨422247451640974080502447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2251986408751861762679717 422247451640974080502447)
        ·
          refine ⟨633371177461461120753671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422247451640974080502447 633371177461461120753671)
          ·
            refine ⟨950056766192191681130507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633371177461461120753671 950056766192191681130507)
            ·
              refine ⟨1425085149288287521695761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950056766192191681130507 1425085149288287521695761)
              ·
                refine ⟨1068813861966215641271821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425085149288287521695761 1068813861966215641271821)
                ·
                  refine ⟨400805198237330865476933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068813861966215641271821 400805198237330865476933)
                  ·
                    refine ⟨75150974669499537276925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400805198237330865476933 75150974669499537276925)
                    ·
                      rfl

theorem cell22_219534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_219534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219534 prefixEnd_219534 := by exact prefixLift 219534
  have htrace : WordTrace (prefixWord ++ tailWord_219534) baseStart_219534 baseEnd_219534 := by
    simpa [prefixWord, tailWord_219534, baseEnd_219534] using wordTrace_append hprefix tailTrace_219534
  have hstable : (prefixWord ++ tailWord_219534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219534).length < 2 ^ (prefixWord ++ tailWord_219534).sum := by decide
  have hdescent : baseEnd_219534 < baseStart_219534 := by decide
  rcases family_descends (prefixWord ++ tailWord_219534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219549 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 6]
def baseStart_219549 : Nat := 118140960795 + 219549 * 2 ^ 59
def prefixEnd_219549 : Nat := 4983230072969 + 3 ^ 40 * 219549 * 2
def baseEnd_219549 : Nat := 25052036492014832717293

theorem tailTrace_219549 : CollatzResearch.WordTrace tailWord_219549 prefixEnd_219549 25052036492014832717293 := by
  unfold tailWord_219549
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007609881618943829101701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5338406587745962552734467 8007609881618943829101701)
  ·
    refine ⟨1501426852803551967956569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8007609881618943829101701 1501426852803551967956569)
    ·
      refine ⟨1126070139602663975967427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1501426852803551967956569 1126070139602663975967427)
      ·
        refine ⟨1689105209403995963951141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126070139602663975967427 1689105209403995963951141)
        ·
          refine ⟨316707226763249243240839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1689105209403995963951141 316707226763249243240839)
          ·
            refine ⟨475060840144873864861259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316707226763249243240839 475060840144873864861259)
            ·
              refine ⟨712591260217310797291889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475060840144873864861259 712591260217310797291889)
              ·
                refine ⟨534443445162983097968917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712591260217310797291889 534443445162983097968917)
                ·
                  refine ⟨25052036492014832717293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 534443445162983097968917 25052036492014832717293)
                  ·
                    rfl

theorem cell22_219549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_219549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219549 prefixEnd_219549 := by exact prefixLift 219549
  have htrace : WordTrace (prefixWord ++ tailWord_219549) baseStart_219549 baseEnd_219549 := by
    simpa [prefixWord, tailWord_219549, baseEnd_219549] using wordTrace_append hprefix tailTrace_219549
  have hstable : (prefixWord ++ tailWord_219549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219549).length < 2 ^ (prefixWord ++ tailWord_219549).sum := by decide
  have hdescent : baseEnd_219549 < baseStart_219549 := by decide
  rcases family_descends (prefixWord ++ tailWord_219549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219577 : List Nat := [1, 2, 1, 4, 3, 2, 9]
def baseStart_219577 : Nat := 118140960795 + 219577 * 2 ^ 59
def prefixEnd_219577 : Nat := 4983230072969 + 3 ^ 40 * 219577 * 2
def baseEnd_219577 : Nat := 2783914609194879942659

theorem tailTrace_219577 : CollatzResearch.WordTrace tailWord_219577 prefixEnd_219577 2783914609194879942659 := by
  unfold tailWord_219577
  simp only [CollatzResearch.WordTrace]
  refine ⟨8008631125517504611120985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5339087417011669740747323 8008631125517504611120985)
  ·
    refine ⟨6006473344138128458340739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8008631125517504611120985 6006473344138128458340739)
    ·
      refine ⟨9009710016207192687511109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006473344138128458340739 9009710016207192687511109)
      ·
        refine ⟨1689320628038848628908333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9009710016207192687511109 1689320628038848628908333)
        ·
          refine ⟨633495235514568235840625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1689320628038848628908333 633495235514568235840625)
          ·
            refine ⟨475121426635926176880469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633495235514568235840625 475121426635926176880469)
            ·
              refine ⟨2783914609194879942659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 475121426635926176880469 2783914609194879942659)
              ·
                rfl

theorem cell22_219577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 9].length) (baseStart_219577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219577 prefixEnd_219577 := by exact prefixLift 219577
  have htrace : WordTrace (prefixWord ++ tailWord_219577) baseStart_219577 baseEnd_219577 := by
    simpa [prefixWord, tailWord_219577, baseEnd_219577] using wordTrace_append hprefix tailTrace_219577
  have hstable : (prefixWord ++ tailWord_219577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219577).length < 2 ^ (prefixWord ++ tailWord_219577).sum := by decide
  have hdescent : baseEnd_219577 < baseStart_219577 := by decide
  rcases family_descends (prefixWord ++ tailWord_219577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219581 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_219581 : Nat := 118140960795 + 219581 * 2 ^ 59
def prefixEnd_219581 : Nat := 4983230072969 + 3 ^ 40 * 219581 * 2
def baseEnd_219581 : Nat := 75167063730007081351781

theorem tailTrace_219581 : CollatzResearch.WordTrace tailWord_219581 prefixEnd_219581 75167063730007081351781 := by
  unfold tailWord_219581
  simp only [CollatzResearch.WordTrace]
  refine ⟨8008777017503013294266597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5339184678335342196177731 8008777017503013294266597)
  ·
    refine ⟨1501645690781814992674987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8008777017503013294266597 1501645690781814992674987)
    ·
      refine ⟨2252468536172722489012481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1501645690781814992674987 2252468536172722489012481)
      ·
        refine ⟨1689351402129541866759361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2252468536172722489012481 1689351402129541866759361)
        ·
          refine ⟨1267013551597156400069521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1689351402129541866759361 1267013551597156400069521)
          ·
            refine ⟨950260163697867300052141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267013551597156400069521 950260163697867300052141)
            ·
              refine ⟨356347561386700237519553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950260163697867300052141 356347561386700237519553)
              ·
                refine ⟨267260671040025178139665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356347561386700237519553 267260671040025178139665)
                ·
                  refine ⟨200445503280018883604749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267260671040025178139665 200445503280018883604749)
                  ·
                    refine ⟨75167063730007081351781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200445503280018883604749 75167063730007081351781)
                    ·
                      rfl

theorem cell22_219581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_219581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219581 prefixEnd_219581 := by exact prefixLift 219581
  have htrace : WordTrace (prefixWord ++ tailWord_219581) baseStart_219581 baseEnd_219581 := by
    simpa [prefixWord, tailWord_219581, baseEnd_219581] using wordTrace_append hprefix tailTrace_219581
  have hstable : (prefixWord ++ tailWord_219581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219581).length < 2 ^ (prefixWord ++ tailWord_219581).sum := by decide
  have hdescent : baseEnd_219581 < baseStart_219581 := by decide
  rcases family_descends (prefixWord ++ tailWord_219581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219609 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_219609 : Nat := 118140960795 + 219609 * 2 ^ 59
def prefixEnd_219609 : Nat := 4983230072969 + 3 ^ 40 * 219609 * 2
def baseEnd_219609 : Nat := 75176648702224341651695

theorem tailTrace_219609 : CollatzResearch.WordTrace tailWord_219609 prefixEnd_219609 75176648702224341651695 := by
  unfold tailWord_219609
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009798261401574076285881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5339865507601049384190587 8009798261401574076285881)
  ·
    refine ⟨6007348696051180557214411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8009798261401574076285881 6007348696051180557214411)
    ·
      refine ⟨9011023044076770835821617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007348696051180557214411 9011023044076770835821617)
      ·
        refine ⟨6758267283057578126866213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011023044076770835821617 6758267283057578126866213)
        ·
          refine ⟨1267175115573295898787415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6758267283057578126866213 1267175115573295898787415)
          ·
            refine ⟨1900762673359943848181123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267175115573295898787415 1900762673359943848181123)
            ·
              refine ⟨2851144010039915772271685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900762673359943848181123 2851144010039915772271685)
              ·
                refine ⟨534589501882484207300941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2851144010039915772271685 534589501882484207300941)
                ·
                  refine ⟨200471063205931577737853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534589501882484207300941 200471063205931577737853)
                  ·
                    refine ⟨75176648702224341651695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200471063205931577737853 75176648702224341651695)
                    ·
                      rfl

theorem cell22_219609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_219609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219609 prefixEnd_219609 := by exact prefixLift 219609
  have htrace : WordTrace (prefixWord ++ tailWord_219609) baseStart_219609 baseEnd_219609 := by
    simpa [prefixWord, tailWord_219609, baseEnd_219609] using wordTrace_append hprefix tailTrace_219609
  have hstable : (prefixWord ++ tailWord_219609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219609).length < 2 ^ (prefixWord ++ tailWord_219609).sum := by decide
  have hdescent : baseEnd_219609 < baseStart_219609 := by decide
  rcases family_descends (prefixWord ++ tailWord_219609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219667 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 8]
def baseStart_219667 : Nat := 118140960795 + 219667 * 2 ^ 59
def prefixEnd_219667 : Nat := 4983230072969 + 3 ^ 40 * 219667 * 2
def baseEnd_219667 : Nat := 25065501095843841233839

theorem tailTrace_219667 : CollatzResearch.WordTrace tailWord_219667 prefixEnd_219667 25065501095843841233839 := by
  unfold tailWord_219667
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011913695191449981897255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5341275796794299987931503 8011913695191449981897255)
  ·
    refine ⟨12017870542787174972845883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8011913695191449981897255 12017870542787174972845883)
    ·
      refine ⟨18026805814180762459268825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12017870542787174972845883 18026805814180762459268825)
      ·
        refine ⟨13520104360635571844451619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18026805814180762459268825 13520104360635571844451619)
        ·
          refine ⟨20280156540953357766677429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520104360635571844451619 20280156540953357766677429)
          ·
            refine ⟨1901264675714377290626009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20280156540953357766677429 1901264675714377290626009)
            ·
              refine ⟨1425948506785782967969507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901264675714377290626009 1425948506785782967969507)
              ·
                refine ⟨2138922760178674451954261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425948506785782967969507 2138922760178674451954261)
                ·
                  refine ⟨25065501095843841233839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2138922760178674451954261 25065501095843841233839)
                  ·
                    rfl

theorem cell22_219667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_219667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219667 prefixEnd_219667 := by exact prefixLift 219667
  have htrace : WordTrace (prefixWord ++ tailWord_219667) baseStart_219667 baseEnd_219667 := by
    simpa [prefixWord, tailWord_219667, baseEnd_219667] using wordTrace_append hprefix tailTrace_219667
  have hstable : (prefixWord ++ tailWord_219667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219667).length < 2 ^ (prefixWord ++ tailWord_219667).sum := by decide
  have hdescent : baseEnd_219667 < baseStart_219667 := by decide
  rcases family_descends (prefixWord ++ tailWord_219667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219669 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_219669 : Nat := 118140960795 + 219669 * 2 ^ 59
def prefixEnd_219669 : Nat := 4983230072969 + 3 ^ 40 * 219669 * 2
def baseEnd_219669 : Nat := 75197187928404185151511

theorem tailTrace_219669 : CollatzResearch.WordTrace tailWord_219669 prefixEnd_219669 75197187928404185151511 := by
  unfold tailWord_219669
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011986641184204323470061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5341324427456136215646707 8011986641184204323470061)
  ·
    refine ⟨3004494990444076621301273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8011986641184204323470061 3004494990444076621301273)
    ·
      refine ⟨2253371242833057465975955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3004494990444076621301273 2253371242833057465975955)
      ·
        refine ⟨3380056864249586198963933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253371242833057465975955 3380056864249586198963933)
        ·
          refine ⟨1267521324093594824611475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3380056864249586198963933 1267521324093594824611475)
          ·
            refine ⟨1901281986140392236917213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267521324093594824611475 1901281986140392236917213)
            ·
              refine ⟨712980744802647088843955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901281986140392236917213 712980744802647088843955)
              ·
                refine ⟨1069471117203970633265933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712980744802647088843955 1069471117203970633265933)
                ·
                  refine ⟨401051668951488987474725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069471117203970633265933 401051668951488987474725)
                  ·
                    refine ⟨75197187928404185151511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401051668951488987474725 75197187928404185151511)
                    ·
                      rfl

theorem cell22_219669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_219669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219669 prefixEnd_219669 := by exact prefixLift 219669
  have htrace : WordTrace (prefixWord ++ tailWord_219669) baseStart_219669 baseEnd_219669 := by
    simpa [prefixWord, tailWord_219669, baseEnd_219669] using wordTrace_append hprefix tailTrace_219669
  have hstable : (prefixWord ++ tailWord_219669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219669).length < 2 ^ (prefixWord ++ tailWord_219669).sum := by decide
  have hdescent : baseEnd_219669 < baseStart_219669 := by decide
  rcases family_descends (prefixWord ++ tailWord_219669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219694 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_219694 : Nat := 118140960795 + 219694 * 2 ^ 59
def prefixEnd_219694 : Nat := 4983230072969 + 3 ^ 40 * 219694 * 2
def baseEnd_219694 : Nat := 75205745939312453276435

theorem tailTrace_219694 : CollatzResearch.WordTrace tailWord_219694 prefixEnd_219694 75205745939312453276435 := by
  unfold tailWord_219694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001612308261704199141267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5341932310729089062086757 1001612308261704199141267)
  ·
    refine ⟨1502418462392556298711901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001612308261704199141267 1502418462392556298711901)
    ·
      refine ⟨563406923397208612016963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1502418462392556298711901 563406923397208612016963)
      ·
        refine ⟨845110385095812918025445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563406923397208612016963 845110385095812918025445)
        ·
          refine ⟨158458197205464922129771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 845110385095812918025445 158458197205464922129771)
          ·
            refine ⟨237687295808197383194657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158458197205464922129771 237687295808197383194657)
            ·
              refine ⟨178265471856148037395993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237687295808197383194657 178265471856148037395993)
              ·
                refine ⟨133699103892111028046995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178265471856148037395993 133699103892111028046995)
                ·
                  refine ⟨200548655838166542070493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133699103892111028046995 200548655838166542070493)
                  ·
                    refine ⟨75205745939312453276435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200548655838166542070493 75205745939312453276435)
                    ·
                      rfl

theorem cell22_219694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_219694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219694 prefixEnd_219694 := by exact prefixLift 219694
  have htrace : WordTrace (prefixWord ++ tailWord_219694) baseStart_219694 baseEnd_219694 := by
    simpa [prefixWord, tailWord_219694, baseEnd_219694] using wordTrace_append hprefix tailTrace_219694
  have hstable : (prefixWord ++ tailWord_219694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219694).length < 2 ^ (prefixWord ++ tailWord_219694).sum := by decide
  have hdescent : baseEnd_219694 < baseStart_219694 := by decide
  rcases family_descends (prefixWord ++ tailWord_219694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219701 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 4]
def baseStart_219701 : Nat := 118140960795 + 219701 * 2 ^ 59
def prefixEnd_219701 : Nat := 4983230072969 + 3 ^ 40 * 219701 * 2
def baseEnd_219701 : Nat := 25069380727455589450471

theorem tailTrace_219701 : CollatzResearch.WordTrace tailWord_219701 prefixEnd_219701 25069380727455589450471 := by
  unfold tailWord_219701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013153777068273788634957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5342102518045515859089971 8013153777068273788634957)
  ·
    refine ⟨3004932666400602670738109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8013153777068273788634957 3004932666400602670738109)
    ·
      refine ⟨1126849749900226001526791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3004932666400602670738109 1126849749900226001526791)
      ·
        refine ⟨1690274624850339002290187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126849749900226001526791 1690274624850339002290187)
        ·
          refine ⟨2535411937275508503435281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690274624850339002290187 2535411937275508503435281)
          ·
            refine ⟨1901558952956631377576461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535411937275508503435281 1901558952956631377576461)
            ·
              refine ⟨713084607358736766591173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901558952956631377576461 713084607358736766591173)
              ·
                refine ⟨133703363879763143735845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713084607358736766591173 133703363879763143735845)
                ·
                  refine ⟨25069380727455589450471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133703363879763143735845 25069380727455589450471)
                  ·
                    rfl

theorem cell22_219701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_219701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219701 prefixEnd_219701 := by exact prefixLift 219701
  have htrace : WordTrace (prefixWord ++ tailWord_219701) baseStart_219701 baseEnd_219701 := by
    simpa [prefixWord, tailWord_219701, baseEnd_219701] using wordTrace_append hprefix tailTrace_219701
  have hstable : (prefixWord ++ tailWord_219701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219701).length < 2 ^ (prefixWord ++ tailWord_219701).sum := by decide
  have hdescent : baseEnd_219701 < baseStart_219701 := by decide
  rcases family_descends (prefixWord ++ tailWord_219701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219718 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_219718 : Nat := 118140960795 + 219718 * 2 ^ 59
def prefixEnd_219718 : Nat := 4983230072969 + 3 ^ 40 * 219718 * 2
def baseEnd_219718 : Nat := 25071320543261463558787

theorem tailTrace_219718 : CollatzResearch.WordTrace tailWord_219718 prefixEnd_219718 25071320543261463558787 := by
  unfold tailWord_219718
  simp only [CollatzResearch.WordTrace]
  refine ⟨250430431812708927875119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5342515878671123794669205 250430431812708927875119)
  ·
    refine ⟨375645647719063391812679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250430431812708927875119 375645647719063391812679)
    ·
      refine ⟨563468471578595087719019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375645647719063391812679 563468471578595087719019)
      ·
        refine ⟨845202707367892631578529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563468471578595087719019 845202707367892631578529)
        ·
          refine ⟨633902030525919473683897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845202707367892631578529 633902030525919473683897)
          ·
            refine ⟨475426522894439605262923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633902030525919473683897 475426522894439605262923)
            ·
              refine ⟨713139784341659407894385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475426522894439605262923 713139784341659407894385)
              ·
                refine ⟨534854838256244555920789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713139784341659407894385 534854838256244555920789)
                ·
                  refine ⟨25071320543261463558787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 534854838256244555920789 25071320543261463558787)
                  ·
                    rfl

theorem cell22_219718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_219718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219718 prefixEnd_219718 := by exact prefixLift 219718
  have htrace : WordTrace (prefixWord ++ tailWord_219718) baseStart_219718 baseEnd_219718 := by
    simpa [prefixWord, tailWord_219718, baseEnd_219718] using wordTrace_append hprefix tailTrace_219718
  have hstable : (prefixWord ++ tailWord_219718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219718).length < 2 ^ (prefixWord ++ tailWord_219718).sum := by decide
  have hdescent : baseEnd_219718 < baseStart_219718 := by decide
  rcases family_descends (prefixWord ++ tailWord_219718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219864 : List Nat := [2, 1, 2, 2, 3, 12]
def baseStart_219864 : Nat := 118140960795 + 219864 * 2 ^ 59
def prefixEnd_219864 : Nat := 4983230072969 + 3 ^ 40 * 219864 * 2
def baseEnd_219864 : Nat := 929184449549242920073

theorem tailTrace_219864 : CollatzResearch.WordTrace tailWord_219864 prefixEnd_219864 929184449549242920073 := by
  unfold tailWord_219864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009549437738876313409323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5346065916985168417879097 4009549437738876313409323)
  ·
    refine ⟨6014324156608314470113985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4009549437738876313409323 6014324156608314470113985)
    ·
      refine ⟨4510743117456235852585489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6014324156608314470113985 4510743117456235852585489)
      ·
        refine ⟨3383057338092176889439117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4510743117456235852585489 3383057338092176889439117)
        ·
          refine ⟨1268646501784566333539669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3383057338092176889439117 1268646501784566333539669)
          ·
            refine ⟨929184449549242920073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1268646501784566333539669 929184449549242920073)
            ·
              rfl

theorem cell22_219864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 12].length) (baseStart_219864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219864 prefixEnd_219864 := by exact prefixLift 219864
  have htrace : WordTrace (prefixWord ++ tailWord_219864) baseStart_219864 baseEnd_219864 := by
    simpa [prefixWord, tailWord_219864, baseEnd_219864] using wordTrace_append hprefix tailTrace_219864
  have hstable : (prefixWord ++ tailWord_219864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219864).length < 2 ^ (prefixWord ++ tailWord_219864).sum := by decide
  have hdescent : baseEnd_219864 < baseStart_219864 := by decide
  rcases family_descends (prefixWord ++ tailWord_219864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219866 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_219866 : Nat := 118140960795 + 219866 * 2 ^ 59
def prefixEnd_219866 : Nat := 4983230072969 + 3 ^ 40 * 219866 * 2
def baseEnd_219866 : Nat := 75264625054361337975907

theorem tailTrace_219866 : CollatzResearch.WordTrace tailWord_219866 prefixEnd_219866 75264625054361337975907 := by
  unfold tailWord_219866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004792955367626742097863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5346114547647004645594301 2004792955367626742097863)
  ·
    refine ⟨3007189433051440113146795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004792955367626742097863 3007189433051440113146795)
    ·
      refine ⟨4510784149577160169720193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3007189433051440113146795 4510784149577160169720193)
      ·
        refine ⟨3383088112182870127290145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4510784149577160169720193 3383088112182870127290145)
        ·
          refine ⟨2537316084137152595467609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3383088112182870127290145 2537316084137152595467609)
          ·
            refine ⟨1902987063102864446600707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537316084137152595467609 1902987063102864446600707)
            ·
              refine ⟨2854480594654296669901061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902987063102864446600707 2854480594654296669901061)
              ·
                refine ⟨535215111497680625606449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2854480594654296669901061 535215111497680625606449)
                ·
                  refine ⟨401411333623260469204837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535215111497680625606449 401411333623260469204837)
                  ·
                    refine ⟨75264625054361337975907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401411333623260469204837 75264625054361337975907)
                    ·
                      rfl

theorem cell22_219866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_219866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219866 prefixEnd_219866 := by exact prefixLift 219866
  have htrace : WordTrace (prefixWord ++ tailWord_219866) baseStart_219866 baseEnd_219866 := by
    simpa [prefixWord, tailWord_219866, baseEnd_219866] using wordTrace_append hprefix tailTrace_219866
  have hstable : (prefixWord ++ tailWord_219866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219866).length < 2 ^ (prefixWord ++ tailWord_219866).sum := by decide
  have hdescent : baseEnd_219866 < baseStart_219866 := by decide
  rcases family_descends (prefixWord ++ tailWord_219866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219930 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_219930 : Nat := 118140960795 + 219930 * 2 ^ 59
def prefixEnd_219930 : Nat := 4983230072969 + 3 ^ 40 * 219930 * 2
def baseEnd_219930 : Nat := 75286533562286504375711

theorem tailTrace_219930 : CollatzResearch.WordTrace tailWord_219930 prefixEnd_219930 75286533562286504375711 := by
  unfold tailWord_219930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005376523309661474680311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5347670728825763932480829 2005376523309661474680311)
  ·
    refine ⟨3008064784964492212020467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2005376523309661474680311 3008064784964492212020467)
    ·
      refine ⟨4512097177446738318030701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3008064784964492212020467 4512097177446738318030701)
      ·
        refine ⟨1692036441542526869261513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4512097177446738318030701 1692036441542526869261513)
        ·
          refine ⟨1269027331156895151946135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692036441542526869261513 1269027331156895151946135)
          ·
            refine ⟨1903540996735342727919203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269027331156895151946135 1903540996735342727919203)
            ·
              refine ⟨2855311495103014091878805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903540996735342727919203 2855311495103014091878805)
              ·
                refine ⟨133842726332953785556819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2855311495103014091878805 133842726332953785556819)
                ·
                  refine ⟨200764089499430678335229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133842726332953785556819 200764089499430678335229)
                  ·
                    refine ⟨75286533562286504375711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200764089499430678335229 75286533562286504375711)
                    ·
                      rfl

theorem cell22_219930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_219930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219930 prefixEnd_219930 := by exact prefixLift 219930
  have htrace : WordTrace (prefixWord ++ tailWord_219930) baseStart_219930 baseEnd_219930 := by
    simpa [prefixWord, tailWord_219930, baseEnd_219930] using wordTrace_append hprefix tailTrace_219930
  have hstable : (prefixWord ++ tailWord_219930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219930).length < 2 ^ (prefixWord ++ tailWord_219930).sum := by decide
  have hdescent : baseEnd_219930 < baseStart_219930 := by decide
  rcases family_descends (prefixWord ++ tailWord_219930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219941 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_219941 : Nat := 118140960795 + 219941 * 2 ^ 59
def prefixEnd_219941 : Nat := 4983230072969 + 3 ^ 40 * 219941 * 2
def baseEnd_219941 : Nat := 75290299087086142350677

theorem tailTrace_219941 : CollatzResearch.WordTrace tailWord_219941 prefixEnd_219941 75290299087086142350677 := by
  unfold tailWord_219941
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021907296198794777371677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5347938197465863184914451 8021907296198794777371677)
  ·
    refine ⟨3008215236074548041514379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8021907296198794777371677 3008215236074548041514379)
    ·
      refine ⟨4512322854111822062271569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3008215236074548041514379 4512322854111822062271569)
      ·
        refine ⟨3384242140583866546703677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512322854111822062271569 3384242140583866546703677)
        ·
          refine ⟨1269090802718949955013879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3384242140583866546703677 1269090802718949955013879)
          ·
            refine ⟨1903636204078424932520819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269090802718949955013879 1903636204078424932520819)
            ·
              refine ⟨2855454306117637398781229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903636204078424932520819 2855454306117637398781229)
              ·
                refine ⟨1070795364794114024542961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2855454306117637398781229 1070795364794114024542961)
                ·
                  refine ⟨803096523595585518407221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1070795364794114024542961 803096523595585518407221)
                  ·
                    refine ⟨75290299087086142350677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 803096523595585518407221 75290299087086142350677)
                    ·
                      rfl

theorem cell22_219941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_219941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219941 prefixEnd_219941 := by exact prefixLift 219941
  have htrace : WordTrace (prefixWord ++ tailWord_219941) baseStart_219941 baseEnd_219941 := by
    simpa [prefixWord, tailWord_219941, baseEnd_219941] using wordTrace_append hprefix tailTrace_219941
  have hstable : (prefixWord ++ tailWord_219941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219941).length < 2 ^ (prefixWord ++ tailWord_219941).sum := by decide
  have hdescent : baseEnd_219941 < baseStart_219941 := by decide
  rcases family_descends (prefixWord ++ tailWord_219941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219949 : List Nat := [1, 5, 3, 2, 2, 1, 2, 6]
def baseStart_219949 : Nat := 118140960795 + 219949 * 2 ^ 59
def prefixEnd_219949 : Nat := 4983230072969 + 3 ^ 40 * 219949 * 2
def baseEnd_219949 : Nat := 8365893072286309794517

theorem tailTrace_219949 : CollatzResearch.WordTrace tailWord_219949 prefixEnd_219949 8365893072286309794517 := by
  unfold tailWord_219949
  simp only [CollatzResearch.WordTrace]
  refine ⟨8022199080169812143662901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5348132720113208095775267 8022199080169812143662901)
  ·
    refine ⟨752081163765919888468397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8022199080169812143662901 752081163765919888468397)
    ·
      refine ⟨282030436412219958175649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 752081163765919888468397 282030436412219958175649)
      ·
        refine ⟨211522827309164968631737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282030436412219958175649 211522827309164968631737)
        ·
          refine ⟨158642120481873726473803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211522827309164968631737 158642120481873726473803)
          ·
            refine ⟨237963180722810589710705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158642120481873726473803 237963180722810589710705)
            ·
              refine ⟨178472385542107942283029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237963180722810589710705 178472385542107942283029)
              ·
                refine ⟨8365893072286309794517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178472385542107942283029 8365893072286309794517)
                ·
                  rfl

theorem cell22_219949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 6].length) (baseStart_219949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219949 prefixEnd_219949 := by exact prefixLift 219949
  have htrace : WordTrace (prefixWord ++ tailWord_219949) baseStart_219949 baseEnd_219949 := by
    simpa [prefixWord, tailWord_219949, baseEnd_219949] using wordTrace_append hprefix tailTrace_219949
  have hstable : (prefixWord ++ tailWord_219949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219949).length < 2 ^ (prefixWord ++ tailWord_219949).sum := by decide
  have hdescent : baseEnd_219949 < baseStart_219949 := by decide
  rcases family_descends (prefixWord ++ tailWord_219949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219981 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_219981 : Nat := 118140960795 + 219981 * 2 ^ 59
def prefixEnd_219981 : Nat := 4983230072969 + 3 ^ 40 * 219981 * 2
def baseEnd_219981 : Nat := 75303991904539371350555

theorem tailTrace_219981 : CollatzResearch.WordTrace tailWord_219981 prefixEnd_219981 75303991904539371350555 := by
  unfold tailWord_219981
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023366216053881608827797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5348910810702587739218531 8023366216053881608827797)
  ·
    refine ⟨376095291377525700413803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8023366216053881608827797 376095291377525700413803)
    ·
      refine ⟨564142937066288550620705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376095291377525700413803 564142937066288550620705)
      ·
        refine ⟨423107202799716412965529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564142937066288550620705 423107202799716412965529)
        ·
          refine ⟨317330402099787309724147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423107202799716412965529 317330402099787309724147)
          ·
            refine ⟨475995603149680964586221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317330402099787309724147 475995603149680964586221)
            ·
              refine ⟨178498351181130361719833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475995603149680964586221 178498351181130361719833)
              ·
                refine ⟨133873763385847771289875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178498351181130361719833 133873763385847771289875)
                ·
                  refine ⟨200810645078771656934813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133873763385847771289875 200810645078771656934813)
                  ·
                    refine ⟨75303991904539371350555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200810645078771656934813 75303991904539371350555)
                    ·
                      rfl

theorem cell22_219981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_219981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_219981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_219981 prefixEnd_219981 := by exact prefixLift 219981
  have htrace : WordTrace (prefixWord ++ tailWord_219981) baseStart_219981 baseEnd_219981 := by
    simpa [prefixWord, tailWord_219981, baseEnd_219981] using wordTrace_append hprefix tailTrace_219981
  have hstable : (prefixWord ++ tailWord_219981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219981).length < 2 ^ (prefixWord ++ tailWord_219981).sum := by decide
  have hdescent : baseEnd_219981 < baseStart_219981 := by decide
  rcases family_descends (prefixWord ++ tailWord_219981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220001 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_220001 : Nat := 118140960795 + 220001 * 2 ^ 59
def prefixEnd_220001 : Nat := 4983230072969 + 3 ^ 40 * 220001 * 2
def baseEnd_220001 : Nat := 75310838313265985850493

theorem tailTrace_220001 : CollatzResearch.WordTrace tailWord_220001 prefixEnd_220001 75310838313265985850493 := by
  unfold tailWord_220001
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024095675981425024555857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5349397117320950016370571 8024095675981425024555857)
  ·
    refine ⟨6018071756986068768416893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8024095675981425024555857 6018071756986068768416893)
    ·
      refine ⟨2256776908869775788156335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6018071756986068768416893 2256776908869775788156335)
      ·
        refine ⟨3385165363304663682234503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256776908869775788156335 3385165363304663682234503)
        ·
          refine ⟨5077748044956995523351755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385165363304663682234503 5077748044956995523351755)
          ·
            refine ⟨7616622067435493285027633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077748044956995523351755 7616622067435493285027633)
            ·
              refine ⟨5712466550576619963770725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616622067435493285027633 5712466550576619963770725)
              ·
                refine ⟨1071087478233116243207011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5712466550576619963770725 1071087478233116243207011)
                ·
                  refine ⟨1606631217349674364810517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071087478233116243207011 1606631217349674364810517)
                  ·
                    refine ⟨75310838313265985850493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1606631217349674364810517 75310838313265985850493)
                    ·
                      rfl

theorem cell22_220001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_220001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220001 prefixEnd_220001 := by exact prefixLift 220001
  have htrace : WordTrace (prefixWord ++ tailWord_220001) baseStart_220001 baseEnd_220001 := by
    simpa [prefixWord, tailWord_220001, baseEnd_220001] using wordTrace_append hprefix tailTrace_220001
  have hstable : (prefixWord ++ tailWord_220001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220001).length < 2 ^ (prefixWord ++ tailWord_220001).sum := by decide
  have hdescent : baseEnd_220001 < baseStart_220001 := by decide
  rcases family_descends (prefixWord ++ tailWord_220001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220016 : List Nat := [2, 1, 1, 1, 4, 1, 4, 8]
def baseStart_220016 : Nat := 118140960795 + 220016 * 2 ^ 59
def prefixEnd_220016 : Nat := 4983230072969 + 3 ^ 40 * 220016 * 2
def baseEnd_220016 : Nat := 8368441457756771858383

theorem tailTrace_220016 : CollatzResearch.WordTrace tailWord_220016 prefixEnd_220016 8368441457756771858383 := by
  unfold tailWord_220016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012321385463541293175951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5349761847284721724234601 4012321385463541293175951)
  ·
    refine ⟨6018482078195311939763927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012321385463541293175951 6018482078195311939763927)
    ·
      refine ⟨9027723117292967909645891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6018482078195311939763927 9027723117292967909645891)
      ·
        refine ⟨13541584675939451864468837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027723117292967909645891 13541584675939451864468837)
        ·
          refine ⟨2539047126738647224587907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13541584675939451864468837 2539047126738647224587907)
          ·
            refine ⟨3808570690107970836881861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539047126738647224587907 3808570690107970836881861)
            ·
              refine ⟨714107004395244531915349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3808570690107970836881861 714107004395244531915349)
              ·
                refine ⟨8368441457756771858383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 714107004395244531915349 8368441457756771858383)
                ·
                  rfl

theorem cell22_220016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_220016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220016 prefixEnd_220016 := by exact prefixLift 220016
  have htrace : WordTrace (prefixWord ++ tailWord_220016) baseStart_220016 baseEnd_220016 := by
    simpa [prefixWord, tailWord_220016, baseEnd_220016] using wordTrace_append hprefix tailTrace_220016
  have hstable : (prefixWord ++ tailWord_220016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220016).length < 2 ^ (prefixWord ++ tailWord_220016).sum := by decide
  have hdescent : baseEnd_220016 < baseStart_220016 := by decide
  rcases family_descends (prefixWord ++ tailWord_220016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220018 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_220018 : Nat := 118140960795 + 220018 * 2 ^ 59
def prefixEnd_220018 : Nat := 4983230072969 + 3 ^ 40 * 220018 * 2
def baseEnd_220018 : Nat := 75316657760683608175441

theorem tailTrace_220018 : CollatzResearch.WordTrace tailWord_220018 prefixEnd_220018 75316657760683608175441 := by
  unfold tailWord_220018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006178929229959231981177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5349810477946557951949805 2006178929229959231981177)
  ·
    refine ⟨1504634196922469423985883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2006178929229959231981177 1504634196922469423985883)
    ·
      refine ⟨2256951295383704135978825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504634196922469423985883 2256951295383704135978825)
      ·
        refine ⟨1692713471537778101984119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256951295383704135978825 1692713471537778101984119)
        ·
          refine ⟨2539070207306667152976179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692713471537778101984119 2539070207306667152976179)
          ·
            refine ⟨3808605310960000729464269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539070207306667152976179 3808605310960000729464269)
            ·
              refine ⟨1428226991610000273549101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3808605310960000729464269 1428226991610000273549101)
              ·
                refine ⟨535585121853750102580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1428226991610000273549101 535585121853750102580913)
                ·
                  refine ⟨401688841390312576935685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535585121853750102580913 401688841390312576935685)
                  ·
                    refine ⟨75316657760683608175441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401688841390312576935685 75316657760683608175441)
                    ·
                      rfl

theorem cell22_220018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_220018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220018 prefixEnd_220018 := by exact prefixLift 220018
  have htrace : WordTrace (prefixWord ++ tailWord_220018) baseStart_220018 baseEnd_220018 := by
    simpa [prefixWord, tailWord_220018, baseEnd_220018] using wordTrace_append hprefix tailTrace_220018
  have hstable : (prefixWord ++ tailWord_220018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220018).length < 2 ^ (prefixWord ++ tailWord_220018).sum := by decide
  have hdescent : baseEnd_220018 < baseStart_220018 := by decide
  rcases family_descends (prefixWord ++ tailWord_220018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220054 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_220054 : Nat := 118140960795 + 220054 * 2 ^ 59
def prefixEnd_220054 : Nat := 4983230072969 + 3 ^ 40 * 220054 * 2
def baseEnd_220054 : Nat := 75328981296391514275331

theorem tailTrace_220054 : CollatzResearch.WordTrace tailWord_220054 prefixEnd_220054 75328981296391514275331 := by
  unfold tailWord_220054
  simp only [CollatzResearch.WordTrace]
  refine ⟨501626796549338442264701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5350685829859610050823477 501626796549338442264701)
  ·
    refine ⟨188110048706001915849263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 501626796549338442264701 188110048706001915849263)
    ·
      refine ⟨282165073059002873773895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188110048706001915849263 282165073059002873773895)
      ·
        refine ⟨423247609588504310660843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282165073059002873773895 423247609588504310660843)
        ·
          refine ⟨634871414382756465991265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423247609588504310660843 634871414382756465991265)
          ·
            refine ⟨476153560787067349493449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634871414382756465991265 476153560787067349493449)
            ·
              refine ⟨357115170590300512120087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476153560787067349493449 357115170590300512120087)
              ·
                refine ⟨535672755885450768180131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357115170590300512120087 535672755885450768180131)
                ·
                  refine ⟨803509133828176152270197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535672755885450768180131 803509133828176152270197)
                  ·
                    refine ⟨75328981296391514275331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 803509133828176152270197 75328981296391514275331)
                    ·
                      rfl

theorem cell22_220054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_220054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220054 prefixEnd_220054 := by exact prefixLift 220054
  have htrace : WordTrace (prefixWord ++ tailWord_220054) baseStart_220054 baseEnd_220054 := by
    simpa [prefixWord, tailWord_220054, baseEnd_220054] using wordTrace_append hprefix tailTrace_220054
  have hstable : (prefixWord ++ tailWord_220054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220054).length < 2 ^ (prefixWord ++ tailWord_220054).sum := by decide
  have hdescent : baseEnd_220054 < baseStart_220054 := by decide
  rcases family_descends (prefixWord ++ tailWord_220054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220065 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_220065 : Nat := 118140960795 + 220065 * 2 ^ 59
def prefixEnd_220065 : Nat := 4983230072969 + 3 ^ 40 * 220065 * 2
def baseEnd_220065 : Nat := 75332746821191152250297

theorem tailTrace_220065 : CollatzResearch.WordTrace tailWord_220065 prefixEnd_220065 75332746821191152250297 := by
  unfold tailWord_220065
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026429947749563954885649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5350953298499709303257099 8026429947749563954885649)
  ·
    refine ⟨6019822460812172966164237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8026429947749563954885649 6019822460812172966164237)
    ·
      refine ⟨2257433422804564862311589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6019822460812172966164237 2257433422804564862311589)
      ·
        refine ⟨423268766775855911683423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2257433422804564862311589 423268766775855911683423)
        ·
          refine ⟨634903150163783867525135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423268766775855911683423 634903150163783867525135)
          ·
            refine ⟨952354725245675801287703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634903150163783867525135 952354725245675801287703)
            ·
              refine ⟨1428532087868513701931555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952354725245675801287703 1428532087868513701931555)
              ·
                refine ⟨2142798131802770552897333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428532087868513701931555 2142798131802770552897333)
                ·
                  refine ⟨200887324856509739334125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2142798131802770552897333 200887324856509739334125)
                  ·
                    refine ⟨75332746821191152250297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200887324856509739334125 75332746821191152250297)
                    ·
                      rfl

theorem cell22_220065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_220065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220065 prefixEnd_220065 := by exact prefixLift 220065
  have htrace : WordTrace (prefixWord ++ tailWord_220065) baseStart_220065 baseEnd_220065 := by
    simpa [prefixWord, tailWord_220065, baseEnd_220065] using wordTrace_append hprefix tailTrace_220065
  have hstable : (prefixWord ++ tailWord_220065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220065).length < 2 ^ (prefixWord ++ tailWord_220065).sum := by decide
  have hdescent : baseEnd_220065 < baseStart_220065 := by decide
  rcases family_descends (prefixWord ++ tailWord_220065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220091 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_220091 : Nat := 118140960795 + 220091 * 2 ^ 59
def prefixEnd_220091 : Nat := 4983230072969 + 3 ^ 40 * 220091 * 2
def baseEnd_220091 : Nat := 75341647152535751100217

theorem tailTrace_220091 : CollatzResearch.WordTrace tailWord_220091 prefixEnd_220091 75341647152535751100217 := by
  unfold tailWord_220091
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027378245655370395332127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5351585497103580263554751 8027378245655370395332127)
  ·
    refine ⟨12041067368483055592998191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8027378245655370395332127 12041067368483055592998191)
    ·
      refine ⟨18061601052724583389497287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12041067368483055592998191 18061601052724583389497287)
      ·
        refine ⟨27092401579086875084245931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18061601052724583389497287 27092401579086875084245931)
        ·
          refine ⟨40638602368630312626368897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27092401579086875084245931 40638602368630312626368897)
          ·
            refine ⟨30478951776472734469776673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40638602368630312626368897 30478951776472734469776673)
            ·
              refine ⟨22859213832354550852332505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30478951776472734469776673 22859213832354550852332505)
              ·
                refine ⟨17144410374265913139249379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22859213832354550852332505 17144410374265913139249379)
                ·
                  refine ⟨25716615561398869708874069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17144410374265913139249379 25716615561398869708874069)
                  ·
                    refine ⟨75341647152535751100217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 25716615561398869708874069 75341647152535751100217)
                    ·
                      rfl

theorem cell22_220091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_220091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220091 prefixEnd_220091 := by exact prefixLift 220091
  have htrace : WordTrace (prefixWord ++ tailWord_220091) baseStart_220091 baseEnd_220091 := by
    simpa [prefixWord, tailWord_220091, baseEnd_220091] using wordTrace_append hprefix tailTrace_220091
  have hstable : (prefixWord ++ tailWord_220091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220091).length < 2 ^ (prefixWord ++ tailWord_220091).sum := by decide
  have hdescent : baseEnd_220091 < baseStart_220091 := by decide
  rcases family_descends (prefixWord ++ tailWord_220091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220133 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_220133 : Nat := 118140960795 + 220133 * 2 ^ 59
def prefixEnd_220133 : Nat := 4983230072969 + 3 ^ 40 * 220133 * 2
def baseEnd_220133 : Nat := 75356024610861641550089

theorem tailTrace_220133 : CollatzResearch.WordTrace tailWord_220133 prefixEnd_220133 75356024610861641550089 := by
  unfold tailWord_220133
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028910111503211568361053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5352606741002141045574035 8028910111503211568361053)
  ·
    refine ⟨3010841291813704338135395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8028910111503211568361053 3010841291813704338135395)
    ·
      refine ⟨4516261937720556507203093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010841291813704338135395 4516261937720556507203093)
      ·
        refine ⟨211699778330651086275145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4516261937720556507203093 211699778330651086275145)
        ·
          refine ⟨158774833747988314706359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211699778330651086275145 158774833747988314706359)
          ·
            refine ⟨238162250621982472059539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158774833747988314706359 238162250621982472059539)
            ·
              refine ⟨357243375932973708089309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238162250621982472059539 357243375932973708089309)
              ·
                refine ⟨133966265974865140533491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357243375932973708089309 133966265974865140533491)
                ·
                  refine ⟨200949398962297710800237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133966265974865140533491 200949398962297710800237)
                  ·
                    refine ⟨75356024610861641550089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200949398962297710800237 75356024610861641550089)
                    ·
                      rfl

theorem cell22_220133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_220133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220133 prefixEnd_220133 := by exact prefixLift 220133
  have htrace : WordTrace (prefixWord ++ tailWord_220133) baseStart_220133 baseEnd_220133 := by
    simpa [prefixWord, tailWord_220133, baseEnd_220133] using wordTrace_append hprefix tailTrace_220133
  have hstable : (prefixWord ++ tailWord_220133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220133).length < 2 ^ (prefixWord ++ tailWord_220133).sum := by decide
  have hdescent : baseEnd_220133 < baseStart_220133 := by decide
  rcases family_descends (prefixWord ++ tailWord_220133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220155 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 2, 3]
def baseStart_220155 : Nat := 118140960795 + 220155 * 2 ^ 59
def prefixEnd_220155 : Nat := 4983230072969 + 3 ^ 40 * 220155 * 2
def baseEnd_220155 : Nat := 75363555660460917500021

theorem tailTrace_220155 : CollatzResearch.WordTrace tailWord_220155 prefixEnd_220155 75363555660460917500021 := by
  unfold tailWord_220155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8029712517423509325661919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5353141678282339550441279 8029712517423509325661919)
  ·
    refine ⟨12044568776135263988492879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8029712517423509325661919 12044568776135263988492879)
    ·
      refine ⟨18066853164202895982739319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12044568776135263988492879 18066853164202895982739319)
      ·
        refine ⟨27100279746304343974108979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18066853164202895982739319 27100279746304343974108979)
        ·
          refine ⟨40650419619456515961163469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27100279746304343974108979 40650419619456515961163469)
          ·
            refine ⟨15243907357296193485436301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40650419619456515961163469 15243907357296193485436301)
            ·
              refine ⟨5716465258986072557038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15243907357296193485436301 5716465258986072557038613)
              ·
                refine ⟨267959309014972151111185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5716465258986072557038613 267959309014972151111185)
                ·
                  refine ⟨200969481761229113333389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267959309014972151111185 200969481761229113333389)
                  ·
                    refine ⟨75363555660460917500021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200969481761229113333389 75363555660460917500021)
                    ·
                      rfl

theorem cell22_220155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3].length) (baseStart_220155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220155 prefixEnd_220155 := by exact prefixLift 220155
  have htrace : WordTrace (prefixWord ++ tailWord_220155) baseStart_220155 baseEnd_220155 := by
    simpa [prefixWord, tailWord_220155, baseEnd_220155] using wordTrace_append hprefix tailTrace_220155
  have hstable : (prefixWord ++ tailWord_220155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220155).length < 2 ^ (prefixWord ++ tailWord_220155).sum := by decide
  have hdescent : baseEnd_220155 < baseStart_220155 := by decide
  rcases family_descends (prefixWord ++ tailWord_220155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220168 : List Nat := [2, 1, 3, 2, 1, 3, 1, 9]
def baseStart_220168 : Nat := 118140960795 + 220168 * 2 ^ 59
def prefixEnd_220168 : Nat := 4983230072969 + 3 ^ 40 * 220168 * 2
def baseEnd_220168 : Nat := 8374222869570357436109

theorem tailTrace_220168 : CollatzResearch.WordTrace tailWord_220168 prefixEnd_220168 8374222869570357436109 := by
  unfold tailWord_220168
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015093333188206272942579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5353457777584275030590105 4015093333188206272942579)
  ·
    refine ⟨6022639999782309409413869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4015093333188206272942579 6022639999782309409413869)
    ·
      refine ⟨2258489999918366028530201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6022639999782309409413869 2258489999918366028530201)
      ·
        refine ⟨1693867499938774521397651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2258489999918366028530201 1693867499938774521397651)
        ·
          refine ⟨2540801249908161782096477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693867499938774521397651 2540801249908161782096477)
          ·
            refine ⟨952800468715560668286179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540801249908161782096477 952800468715560668286179)
            ·
              refine ⟨1429200703073341002429269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952800468715560668286179 1429200703073341002429269)
              ·
                refine ⟨8374222869570357436109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1429200703073341002429269 8374222869570357436109)
                ·
                  rfl

theorem cell22_220168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_220168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220168 prefixEnd_220168 := by exact prefixLift 220168
  have htrace : WordTrace (prefixWord ++ tailWord_220168) baseStart_220168 baseEnd_220168 := by
    simpa [prefixWord, tailWord_220168, baseEnd_220168] using wordTrace_append hprefix tailTrace_220168
  have hstable : (prefixWord ++ tailWord_220168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220168).length < 2 ^ (prefixWord ++ tailWord_220168).sum := by decide
  have hdescent : baseEnd_220168 < baseStart_220168 := by decide
  rcases family_descends (prefixWord ++ tailWord_220168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220172 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_220172 : Nat := 118140960795 + 220172 * 2 ^ 59
def prefixEnd_220172 : Nat := 4983230072969 + 3 ^ 40 * 220172 * 2
def baseEnd_220172 : Nat := 75369375107878539824969

theorem tailTrace_220172 : CollatzResearch.WordTrace tailWord_220172 prefixEnd_220172 75369375107878539824969 := by
  unfold tailWord_220172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015166279180960614515385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5353555038907947486020513 4015166279180960614515385)
  ·
    refine ⟨3011374709385720460886539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4015166279180960614515385 3011374709385720460886539)
    ·
      refine ⟨4517062064078580691329809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011374709385720460886539 4517062064078580691329809)
      ·
        refine ⟨3387796548058935518497357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517062064078580691329809 3387796548058935518497357)
        ·
          refine ⟨1270423705522100819436509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3387796548058935518497357 1270423705522100819436509)
          ·
            refine ⟨476408889570787807288691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1270423705522100819436509 476408889570787807288691)
            ·
              refine ⟨714613334356181710933037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476408889570787807288691 714613334356181710933037)
              ·
                refine ⟨267980000383568141599889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 714613334356181710933037 267980000383568141599889)
                ·
                  refine ⟨200985000287676106199917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267980000383568141599889 200985000287676106199917)
                  ·
                    refine ⟨75369375107878539824969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200985000287676106199917 75369375107878539824969)
                    ·
                      rfl

theorem cell22_220172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_220172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220172 prefixEnd_220172 := by exact prefixLift 220172
  have htrace : WordTrace (prefixWord ++ tailWord_220172) baseStart_220172 baseEnd_220172 := by
    simpa [prefixWord, tailWord_220172, baseEnd_220172] using wordTrace_append hprefix tailTrace_220172
  have hstable : (prefixWord ++ tailWord_220172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220172).length < 2 ^ (prefixWord ++ tailWord_220172).sum := by decide
  have hdescent : baseEnd_220172 < baseStart_220172 := by decide
  rcases family_descends (prefixWord ++ tailWord_220172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220337 : List Nat := [1, 2, 2, 5, 1, 2, 2, 7]
def baseStart_220337 : Nat := 118140960795 + 220337 * 2 ^ 59
def prefixEnd_220337 : Nat := 4983230072969 + 3 ^ 40 * 220337 * 2
def baseEnd_220337 : Nat := 8380650886652567716607

theorem tailTrace_220337 : CollatzResearch.WordTrace tailWord_220337 prefixEnd_220337 8380650886652567716607 := by
  unfold tailWord_220337
  simp only [CollatzResearch.WordTrace]
  refine ⟨8036350602764154408787265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5357567068509436272524843 8036350602764154408787265)
  ·
    refine ⟨6027262952073115806590449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8036350602764154408787265 6027262952073115806590449)
    ·
      refine ⟨4520447214054836854942837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6027262952073115806590449 4520447214054836854942837)
      ·
        refine ⟨423791926317640955150891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4520447214054836854942837 423791926317640955150891)
        ·
          refine ⟨635687889476461432726337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423791926317640955150891 635687889476461432726337)
          ·
            refine ⟨476765917107346074544753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635687889476461432726337 476765917107346074544753)
            ·
              refine ⟨357574437830509555908565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476765917107346074544753 357574437830509555908565)
              ·
                refine ⟨8380650886652567716607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 357574437830509555908565 8380650886652567716607)
                ·
                  rfl

theorem cell22_220337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 7].length) (baseStart_220337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220337 prefixEnd_220337 := by exact prefixLift 220337
  have htrace : WordTrace (prefixWord ++ tailWord_220337) baseStart_220337 baseEnd_220337 := by
    simpa [prefixWord, tailWord_220337, baseEnd_220337] using wordTrace_append hprefix tailTrace_220337
  have hstable : (prefixWord ++ tailWord_220337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220337).length < 2 ^ (prefixWord ++ tailWord_220337).sum := by decide
  have hdescent : baseEnd_220337 < baseStart_220337 := by decide
  rcases family_descends (prefixWord ++ tailWord_220337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220358 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_220358 : Nat := 118140960795 + 220358 * 2 ^ 59
def prefixEnd_220358 : Nat := 4983230072969 + 3 ^ 40 * 220358 * 2
def baseEnd_220358 : Nat := 75433046709036054674399

theorem tailTrace_220358 : CollatzResearch.WordTrace tailWord_220358 prefixEnd_220358 75433046709036054674399 := by
  unfold tailWord_220358
  simp only [CollatzResearch.WordTrace]
  refine ⟨251159891740252343603179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5358077690458716663534485 251159891740252343603179)
  ·
    refine ⟨376739837610378515404769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251159891740252343603179 376739837610378515404769)
    ·
      refine ⟨282554878207783886553577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376739837610378515404769 282554878207783886553577)
      ·
        refine ⟨211916158655837914915183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282554878207783886553577 211916158655837914915183)
        ·
          refine ⟨317874237983756872372775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211916158655837914915183 317874237983756872372775)
          ·
            refine ⟨476811356975635308559163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317874237983756872372775 476811356975635308559163)
            ·
              refine ⟨715217035463452962838745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476811356975635308559163 715217035463452962838745)
              ·
                refine ⟨536412776597589722129059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715217035463452962838745 536412776597589722129059)
                ·
                  refine ⟨804619164896384583193589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536412776597589722129059 804619164896384583193589)
                  ·
                    refine ⟨75433046709036054674399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 804619164896384583193589 75433046709036054674399)
                    ·
                      rfl

theorem cell22_220358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_220358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220358 prefixEnd_220358 := by exact prefixLift 220358
  have htrace : WordTrace (prefixWord ++ tailWord_220358) baseStart_220358 baseEnd_220358 := by
    simpa [prefixWord, tailWord_220358, baseEnd_220358] using wordTrace_append hprefix tailTrace_220358
  have hstable : (prefixWord ++ tailWord_220358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220358).length < 2 ^ (prefixWord ++ tailWord_220358).sum := by decide
  have hdescent : baseEnd_220358 < baseStart_220358 := by decide
  rcases family_descends (prefixWord ++ tailWord_220358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220369 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 1, 3]
def baseStart_220369 : Nat := 118140960795 + 220369 * 2 ^ 59
def prefixEnd_220369 : Nat := 4983230072969 + 3 ^ 40 * 220369 * 2
def baseEnd_220369 : Nat := 75436812233835692649365

theorem tailTrace_220369 : CollatzResearch.WordTrace tailWord_220369 prefixEnd_220369 75436812233835692649365 := by
  unfold tailWord_220369
  simp only [CollatzResearch.WordTrace]
  refine ⟨8037517738648223873952161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5358345159098815915968107 8037517738648223873952161)
  ·
    refine ⟨6028138303986167905464121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8037517738648223873952161 6028138303986167905464121)
    ·
      refine ⟨4521103727989625929098091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6028138303986167905464121 4521103727989625929098091)
      ·
        refine ⟨6781655591984438893647137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521103727989625929098091 6781655591984438893647137)
        ·
          refine ⟨5086241693988329170235353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6781655591984438893647137 5086241693988329170235353)
          ·
            refine ⟨3814681270491246877676515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5086241693988329170235353 3814681270491246877676515)
            ·
              refine ⟨5722021905736870316514773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814681270491246877676515 5722021905736870316514773)
              ·
                refine ⟨134109888415707898043315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5722021905736870316514773 134109888415707898043315)
                ·
                  refine ⟨201164832623561847064973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134109888415707898043315 201164832623561847064973)
                  ·
                    refine ⟨75436812233835692649365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201164832623561847064973 75436812233835692649365)
                    ·
                      rfl

theorem cell22_220369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_220369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220369 prefixEnd_220369 := by exact prefixLift 220369
  have htrace : WordTrace (prefixWord ++ tailWord_220369) baseStart_220369 baseEnd_220369 := by
    simpa [prefixWord, tailWord_220369, baseEnd_220369] using wordTrace_append hprefix tailTrace_220369
  have hstable : (prefixWord ++ tailWord_220369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220369).length < 2 ^ (prefixWord ++ tailWord_220369).sum := by decide
  have hdescent : baseEnd_220369 < baseStart_220369 := by decide
  rcases family_descends (prefixWord ++ tailWord_220369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220397 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_220397 : Nat := 118140960795 + 220397 * 2 ^ 59
def prefixEnd_220397 : Nat := 4983230072969 + 3 ^ 40 * 220397 * 2
def baseEnd_220397 : Nat := 75446397206052952949279

theorem tailTrace_220397 : CollatzResearch.WordTrace tailWord_220397 prefixEnd_220397 75446397206052952949279 := by
  unfold tailWord_220397
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038538982546784655971445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5359025988364523103980963 8038538982546784655971445)
  ·
    refine ⟨753613029613761061497323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8038538982546784655971445 753613029613761061497323)
    ·
      refine ⟨1130419544420641592245985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753613029613761061497323 1130419544420641592245985)
      ·
        refine ⟨847814658315481194184489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130419544420641592245985 847814658315481194184489)
        ·
          refine ⟨635860993736610895638367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847814658315481194184489 635860993736610895638367)
          ·
            refine ⟨953791490604916343457551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635860993736610895638367 953791490604916343457551)
            ·
              refine ⟨1430687235907374515186327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953791490604916343457551 1430687235907374515186327)
              ·
                refine ⟨2146030853861061772779491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430687235907374515186327 2146030853861061772779491)
                ·
                  refine ⟨3219046280791592659169237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146030853861061772779491 3219046280791592659169237)
                  ·
                    refine ⟨75446397206052952949279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3219046280791592659169237 75446397206052952949279)
                    ·
                      rfl

theorem cell22_220397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_220397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220397 prefixEnd_220397 := by exact prefixLift 220397
  have htrace : WordTrace (prefixWord ++ tailWord_220397) baseStart_220397 baseEnd_220397 := by
    simpa [prefixWord, tailWord_220397, baseEnd_220397] using wordTrace_append hprefix tailTrace_220397
  have hstable : (prefixWord ++ tailWord_220397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220397).length < 2 ^ (prefixWord ++ tailWord_220397).sum := by decide
  have hdescent : baseEnd_220397 < baseStart_220397 := by decide
  rcases family_descends (prefixWord ++ tailWord_220397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220444 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 4]
def baseStart_220444 : Nat := 118140960795 + 220444 * 2 ^ 59
def prefixEnd_220444 : Nat := 4983230072969 + 3 ^ 40 * 220444 * 2
def baseEnd_220444 : Nat := 25154162088853499008045

theorem tailTrace_220444 : CollatzResearch.WordTrace tailWord_220444 prefixEnd_220444 25154162088853499008045 := by
  unfold tailWord_220444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020126606688255841466193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5360168808917674455288257 4020126606688255841466193)
  ·
    refine ⟨3015094955016191881099645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4020126606688255841466193 3015094955016191881099645)
    ·
      refine ⟨1130660608131071955412367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3015094955016191881099645 1130660608131071955412367)
      ·
        refine ⟨1695990912196607933118551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130660608131071955412367 1695990912196607933118551)
        ·
          refine ⟨2543986368294911899677827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695990912196607933118551 2543986368294911899677827)
          ·
            refine ⟨3815979552442367849516741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543986368294911899677827 3815979552442367849516741)
            ·
              refine ⟨715496166082943971784389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3815979552442367849516741 715496166082943971784389)
              ·
                refine ⟨134155531140551994709573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715496166082943971784389 134155531140551994709573)
                ·
                  refine ⟨25154162088853499008045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134155531140551994709573 25154162088853499008045)
                  ·
                    rfl

theorem cell22_220444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_220444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220444 prefixEnd_220444 := by exact prefixLift 220444
  have htrace : WordTrace (prefixWord ++ tailWord_220444) baseStart_220444 baseEnd_220444 := by
    simpa [prefixWord, tailWord_220444, baseEnd_220444] using wordTrace_append hprefix tailTrace_220444
  have hstable : (prefixWord ++ tailWord_220444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220444).length < 2 ^ (prefixWord ++ tailWord_220444).sum := by decide
  have hdescent : baseEnd_220444 < baseStart_220444 := by decide
  rcases family_descends (prefixWord ++ tailWord_220444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220611 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 2, 3]
def baseStart_220611 : Nat := 118140960795 + 220611 * 2 ^ 59
def prefixEnd_220611 : Nat := 4983230072969 + 3 ^ 40 * 220611 * 2
def baseEnd_220611 : Nat := 75519653779427728098623

theorem tailTrace_220611 : CollatzResearch.WordTrace tailWord_220611 prefixEnd_220611 75519653779427728098623 := by
  unfold tailWord_220611
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046344203771499204261687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5364229469180999469507791 8046344203771499204261687)
  ·
    refine ⟨12069516305657248806392531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8046344203771499204261687 12069516305657248806392531)
    ·
      refine ⟨18104274458485873209588797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12069516305657248806392531 18104274458485873209588797)
      ·
        refine ⟨6789102921932202453595799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18104274458485873209588797 6789102921932202453595799)
        ·
          refine ⟨10183654382898303680393699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789102921932202453595799 10183654382898303680393699)
          ·
            refine ⟨15275481574347455520590549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183654382898303680393699 15275481574347455520590549)
            ·
              refine ⟨358019099398768488763841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15275481574347455520590549 358019099398768488763841)
              ·
                refine ⟨268514324549076366572881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358019099398768488763841 268514324549076366572881)
                ·
                  refine ⟨201385743411807274929661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268514324549076366572881 201385743411807274929661)
                  ·
                    refine ⟨75519653779427728098623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201385743411807274929661 75519653779427728098623)
                    ·
                      rfl

theorem cell22_220611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 3].length) (baseStart_220611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220611 prefixEnd_220611 := by exact prefixLift 220611
  have htrace : WordTrace (prefixWord ++ tailWord_220611) baseStart_220611 baseEnd_220611 := by
    simpa [prefixWord, tailWord_220611, baseEnd_220611] using wordTrace_append hprefix tailTrace_220611
  have hstable : (prefixWord ++ tailWord_220611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220611).length < 2 ^ (prefixWord ++ tailWord_220611).sum := by decide
  have hdescent : baseEnd_220611 < baseStart_220611 := by decide
  rcases family_descends (prefixWord ++ tailWord_220611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220628 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_220628 : Nat := 118140960795 + 220628 * 2 ^ 59
def prefixEnd_220628 : Nat := 4983230072969 + 3 ^ 40 * 220628 * 2
def baseEnd_220628 : Nat := 75525473226845350423571

theorem tailTrace_220628 : CollatzResearch.WordTrace tailWord_220628 prefixEnd_220628 75525473226845350423571 := by
  unfold tailWord_220628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023482122354955553815269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5364642829806607405087025 4023482122354955553815269)
  ·
    refine ⟨754402897941554166340363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4023482122354955553815269 754402897941554166340363)
    ·
      refine ⟨1131604346912331249510545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754402897941554166340363 1131604346912331249510545)
      ·
        refine ⟨848703260184248437132909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131604346912331249510545 848703260184248437132909)
        ·
          refine ⟨318263722569093163924841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 848703260184248437132909 318263722569093163924841)
          ·
            refine ⟨238697791926819872943631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318263722569093163924841 238697791926819872943631)
            ·
              refine ⟨358046687890229809415447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238697791926819872943631 358046687890229809415447)
              ·
                refine ⟨537070031835344714123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358046687890229809415447 537070031835344714123171)
                ·
                  refine ⟨805605047753017071184757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537070031835344714123171 805605047753017071184757)
                  ·
                    refine ⟨75525473226845350423571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 805605047753017071184757 75525473226845350423571)
                    ·
                      rfl

theorem cell22_220628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_220628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220628 prefixEnd_220628 := by exact prefixLift 220628
  have htrace : WordTrace (prefixWord ++ tailWord_220628) baseStart_220628 baseEnd_220628 := by
    simpa [prefixWord, tailWord_220628, baseEnd_220628] using wordTrace_append hprefix tailTrace_220628
  have hstable : (prefixWord ++ tailWord_220628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220628).length < 2 ^ (prefixWord ++ tailWord_220628).sum := by decide
  have hdescent : baseEnd_220628 < baseStart_220628 := by decide
  rcases family_descends (prefixWord ++ tailWord_220628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220641 : List Nat := [1, 2, 3, 1, 2, 5, 2, 6]
def baseStart_220641 : Nat := 118140960795 + 220641 * 2 ^ 59
def prefixEnd_220641 : Nat := 4983230072969 + 3 ^ 40 * 220641 * 2
def baseEnd_220641 : Nat := 8392213710279738872059

theorem tailTrace_220641 : CollatzResearch.WordTrace tailWord_220641 prefixEnd_220641 8392213710279738872059 := by
  unfold tailWord_220641
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047438393662814327853777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5364958929108542885235851 8047438393662814327853777)
  ·
    refine ⟨6035578795247110745890333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8047438393662814327853777 6035578795247110745890333)
    ·
      refine ⟨2263342048217666529708875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6035578795247110745890333 2263342048217666529708875)
      ·
        refine ⟨3395013072326499794563313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263342048217666529708875 3395013072326499794563313)
        ·
          refine ⟨2546259804244874845922485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395013072326499794563313 2546259804244874845922485)
          ·
            refine ⟨238711856647957016805233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2546259804244874845922485 238711856647957016805233)
            ·
              refine ⟨179033892485967762603925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238711856647957016805233 179033892485967762603925)
              ·
                refine ⟨8392213710279738872059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179033892485967762603925 8392213710279738872059)
                ·
                  rfl

theorem cell22_220641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 6].length) (baseStart_220641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220641 prefixEnd_220641 := by exact prefixLift 220641
  have htrace : WordTrace (prefixWord ++ tailWord_220641) baseStart_220641 baseEnd_220641 := by
    simpa [prefixWord, tailWord_220641, baseEnd_220641] using wordTrace_append hprefix tailTrace_220641
  have hstable : (prefixWord ++ tailWord_220641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220641).length < 2 ^ (prefixWord ++ tailWord_220641).sum := by decide
  have hdescent : baseEnd_220641 < baseStart_220641 := by decide
  rcases family_descends (prefixWord ++ tailWord_220641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220669 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 7]
def baseStart_220669 : Nat := 118140960795 + 220669 * 2 ^ 59
def prefixEnd_220669 : Nat := 4983230072969 + 3 ^ 40 * 220669 * 2
def baseEnd_220669 : Nat := 25179836121578303382815

theorem tailTrace_220669 : CollatzResearch.WordTrace tailWord_220669 prefixEnd_220669 25179836121578303382815 := by
  unfold tailWord_220669
  simp only [CollatzResearch.WordTrace]
  refine ⟨8048459637561375109873061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5365639758374250073248707 8048459637561375109873061)
  ·
    refine ⟨1509086182042757833101199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8048459637561375109873061 1509086182042757833101199)
    ·
      refine ⟨2263629273064136749651799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1509086182042757833101199 2263629273064136749651799)
      ·
        refine ⟨3395443909596205124477699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263629273064136749651799 3395443909596205124477699)
        ·
          refine ⟨5093165864394307686716549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395443909596205124477699 5093165864394307686716549)
          ·
            refine ⟨954968599573932691259353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5093165864394307686716549 954968599573932691259353)
            ·
              refine ⟨716226449680449518444515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954968599573932691259353 716226449680449518444515)
              ·
                refine ⟨1074339674520674277666773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716226449680449518444515 1074339674520674277666773)
                ·
                  refine ⟨25179836121578303382815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1074339674520674277666773 25179836121578303382815)
                  ·
                    rfl

theorem cell22_220669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_220669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220669 prefixEnd_220669 := by exact prefixLift 220669
  have htrace : WordTrace (prefixWord ++ tailWord_220669) baseStart_220669 baseEnd_220669 := by
    simpa [prefixWord, tailWord_220669, baseEnd_220669] using wordTrace_append hprefix tailTrace_220669
  have hstable : (prefixWord ++ tailWord_220669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220669).length < 2 ^ (prefixWord ++ tailWord_220669).sum := by decide
  have hdescent : baseEnd_220669 < baseStart_220669 := by decide
  rcases family_descends (prefixWord ++ tailWord_220669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220746 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_220746 : Nat := 118140960795 + 220746 * 2 ^ 59
def prefixEnd_220746 : Nat := 4983230072969 + 3 ^ 40 * 220746 * 2
def baseEnd_220746 : Nat := 75565867038332375973209

theorem tailTrace_220746 : CollatzResearch.WordTrace tailWord_220746 prefixEnd_220746 75565867038332375973209 := by
  unfold tailWord_220746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012817014570604315106523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5367512038854944840284061 2012817014570604315106523)
  ·
    refine ⟨3019225521855906472659785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2012817014570604315106523 3019225521855906472659785)
    ·
      refine ⟨2264419141391929854494839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3019225521855906472659785 2264419141391929854494839)
      ·
        refine ⟨3396628712087894781742259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264419141391929854494839 3396628712087894781742259)
        ·
          refine ⟨5094943068131842172613389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396628712087894781742259 5094943068131842172613389)
          ·
            refine ⟨1910603650549440814730021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5094943068131842172613389 1910603650549440814730021)
            ·
              refine ⟨358238184478020152761879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1910603650549440814730021 358238184478020152761879)
              ·
                refine ⟨537357276717030229142819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358238184478020152761879 537357276717030229142819)
                ·
                  refine ⟨806035915075545343714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537357276717030229142819 806035915075545343714229)
                  ·
                    refine ⟨75565867038332375973209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 806035915075545343714229 75565867038332375973209)
                    ·
                      rfl

theorem cell22_220746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_220746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220746 prefixEnd_220746 := by exact prefixLift 220746
  have htrace : WordTrace (prefixWord ++ tailWord_220746) baseStart_220746 baseEnd_220746 := by
    simpa [prefixWord, tailWord_220746, baseEnd_220746] using wordTrace_append hprefix tailTrace_220746
  have hstable : (prefixWord ++ tailWord_220746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220746).length < 2 ^ (prefixWord ++ tailWord_220746).sum := by decide
  have hdescent : baseEnd_220746 < baseStart_220746 := by decide
  rcases family_descends (prefixWord ++ tailWord_220746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220776 : List Nat := [2, 1, 4, 3, 1, 2, 9]
def baseStart_220776 : Nat := 118140960795 + 220776 * 2 ^ 59
def prefixEnd_220776 : Nat := 4983230072969 + 3 ^ 40 * 220776 * 2
def baseEnd_220776 : Nat := 2799116172274899915671

theorem tailTrace_220776 : CollatzResearch.WordTrace tailWord_220776 prefixEnd_220776 2799116172274899915671 := by
  unfold tailWord_220776
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026181124086866192009091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5368241498782488256012121 4026181124086866192009091)
  ·
    refine ⟨6039271686130299288013637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026181124086866192009091 6039271686130299288013637)
    ·
      refine ⟨1132363441149431116502557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6039271686130299288013637 1132363441149431116502557)
      ·
        refine ⟨424636290431036668688459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1132363441149431116502557 424636290431036668688459)
        ·
          refine ⟨636954435646555003032689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424636290431036668688459 636954435646555003032689)
          ·
            refine ⟨477715826734916252274517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636954435646555003032689 477715826734916252274517)
            ·
              refine ⟨2799116172274899915671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 477715826734916252274517 2799116172274899915671)
              ·
                rfl

theorem cell22_220776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 9].length) (baseStart_220776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220776 prefixEnd_220776 := by exact prefixLift 220776
  have htrace : WordTrace (prefixWord ++ tailWord_220776) baseStart_220776 baseEnd_220776 := by
    simpa [prefixWord, tailWord_220776, baseEnd_220776] using wordTrace_append hprefix tailTrace_220776
  have hstable : (prefixWord ++ tailWord_220776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220776).length < 2 ^ (prefixWord ++ tailWord_220776).sum := by decide
  have hdescent : baseEnd_220776 < baseStart_220776 := by decide
  rcases family_descends (prefixWord ++ tailWord_220776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220851 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 3, 4]
def baseStart_220851 : Nat := 118140960795 + 220851 * 2 ^ 59
def prefixEnd_220851 : Nat := 4983230072969 + 3 ^ 40 * 220851 * 2
def baseEnd_220851 : Nat := 75601810684147102097887

theorem tailTrace_220851 : CollatzResearch.WordTrace tailWord_220851 prefixEnd_220851 75601810684147102097887 := by
  unfold tailWord_220851
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055097722902020192998407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5370065148601346795332271 8055097722902020192998407)
  ·
    refine ⟨12082646584353030289497611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055097722902020192998407 12082646584353030289497611)
    ·
      refine ⟨18123969876529545434246417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12082646584353030289497611 18123969876529545434246417)
      ·
        refine ⟨13592977407397159075684813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18123969876529545434246417 13592977407397159075684813)
        ·
          refine ⟨5097366527773934653381805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13592977407397159075684813 5097366527773934653381805)
          ·
            refine ⟨1911512447915225495018177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5097366527773934653381805 1911512447915225495018177)
            ·
              refine ⟨1433634335936419121263633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911512447915225495018177 1433634335936419121263633)
              ·
                refine ⟨1075225751952314340947725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433634335936419121263633 1075225751952314340947725)
                ·
                  refine ⟨403209656982117877855397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075225751952314340947725 403209656982117877855397)
                  ·
                    refine ⟨75601810684147102097887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 403209656982117877855397 75601810684147102097887)
                    ·
                      rfl

theorem cell22_220851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_220851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220851 prefixEnd_220851 := by exact prefixLift 220851
  have htrace : WordTrace (prefixWord ++ tailWord_220851) baseStart_220851 baseEnd_220851 := by
    simpa [prefixWord, tailWord_220851, baseEnd_220851] using wordTrace_append hprefix tailTrace_220851
  have hstable : (prefixWord ++ tailWord_220851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220851).length < 2 ^ (prefixWord ++ tailWord_220851).sum := by decide
  have hdescent : baseEnd_220851 < baseStart_220851 := by decide
  rcases family_descends (prefixWord ++ tailWord_220851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220855 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 5]
def baseStart_220855 : Nat := 118140960795 + 220855 * 2 ^ 59
def prefixEnd_220855 : Nat := 4983230072969 + 3 ^ 40 * 220855 * 2
def baseEnd_220855 : Nat := 25201059988630808332625

theorem tailTrace_220855 : CollatzResearch.WordTrace tailWord_220855 prefixEnd_220855 25201059988630808332625 := by
  unfold tailWord_220855
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055243614887528876144019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5370162409925019250762679 8055243614887528876144019)
  ·
    refine ⟨12082865422331293314216029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055243614887528876144019 12082865422331293314216029)
    ·
      refine ⟨4531074533374234992831011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12082865422331293314216029 4531074533374234992831011)
      ·
        refine ⟨6796611800061352489246517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531074533374234992831011 6796611800061352489246517)
        ·
          refine ⟨637182356255751795866861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6796611800061352489246517 637182356255751795866861)
          ·
            refine ⟨238943383595906923450073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 637182356255751795866861 238943383595906923450073)
            ·
              refine ⟨179207537696930192587555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238943383595906923450073 179207537696930192587555)
              ·
                refine ⟨268811306545395288881333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179207537696930192587555 268811306545395288881333)
                ·
                  refine ⟨25201059988630808332625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268811306545395288881333 25201059988630808332625)
                  ·
                    rfl

theorem cell22_220855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 5].length) (baseStart_220855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220855 prefixEnd_220855 := by exact prefixLift 220855
  have htrace : WordTrace (prefixWord ++ tailWord_220855) baseStart_220855 baseEnd_220855 := by
    simpa [prefixWord, tailWord_220855, baseEnd_220855] using wordTrace_append hprefix tailTrace_220855
  have hstable : (prefixWord ++ tailWord_220855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220855).length < 2 ^ (prefixWord ++ tailWord_220855).sum := by decide
  have hdescent : baseEnd_220855 < baseStart_220855 := by decide
  rcases family_descends (prefixWord ++ tailWord_220855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220868 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_220868 : Nat := 118140960795 + 220868 * 2 ^ 59
def prefixEnd_220868 : Nat := 4983230072969 + 3 ^ 40 * 220868 * 2
def baseEnd_220868 : Nat := 75607630131564724422835

theorem tailTrace_220868 : CollatzResearch.WordTrace tailWord_220868 prefixEnd_220868 75607630131564724422835 := by
  unfold tailWord_220868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027858881920216048183629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5370478509226954730911505 4027858881920216048183629)
  ·
    refine ⟨1510447080720081018068861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4027858881920216048183629 1510447080720081018068861)
    ·
      refine ⟨566417655270030381775823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1510447080720081018068861 566417655270030381775823)
      ·
        refine ⟨849626482905045572663735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566417655270030381775823 849626482905045572663735)
        ·
          refine ⟨1274439724357568358995603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849626482905045572663735 1274439724357568358995603)
          ·
            refine ⟨1911659586536352538493405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274439724357568358995603 1911659586536352538493405)
            ·
              refine ⟨716872344951132201935027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911659586536352538493405 716872344951132201935027)
              ·
                refine ⟨1075308517426698302902541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716872344951132201935027 1075308517426698302902541)
                ·
                  refine ⟨403240694035011863588453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075308517426698302902541 403240694035011863588453)
                  ·
                    refine ⟨75607630131564724422835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 403240694035011863588453 75607630131564724422835)
                    ·
                      rfl

theorem cell22_220868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_220868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220868 prefixEnd_220868 := by exact prefixLift 220868
  have htrace : WordTrace (prefixWord ++ tailWord_220868) baseStart_220868 baseEnd_220868 := by
    simpa [prefixWord, tailWord_220868, baseEnd_220868] using wordTrace_append hprefix tailTrace_220868
  have hstable : (prefixWord ++ tailWord_220868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220868).length < 2 ^ (prefixWord ++ tailWord_220868).sum := by decide
  have hdescent : baseEnd_220868 < baseStart_220868 := by decide
  rcases family_descends (prefixWord ++ tailWord_220868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220881 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_220881 : Nat := 118140960795 + 220881 * 2 ^ 59
def prefixEnd_220881 : Nat := 4983230072969 + 3 ^ 40 * 220881 * 2
def baseEnd_220881 : Nat := 75612080297237023847795

theorem tailTrace_220881 : CollatzResearch.WordTrace tailWord_220881 prefixEnd_220881 75612080297237023847795 := by
  unfold tailWord_220881
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056191912793335316590497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5370794608528890211060331 8056191912793335316590497)
  ·
    refine ⟨6042143934595001487442873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8056191912793335316590497 6042143934595001487442873)
    ·
      refine ⟨4531607950946251115582155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6042143934595001487442873 4531607950946251115582155)
      ·
        refine ⟨6797411926419376673373233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531607950946251115582155 6797411926419376673373233)
        ·
          refine ⟨5098058944814532505029925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797411926419376673373233 5098058944814532505029925)
          ·
            refine ⟨955886052152724844693111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5098058944814532505029925 955886052152724844693111)
            ·
              refine ⟨1433829078229087267039667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955886052152724844693111 1433829078229087267039667)
              ·
                refine ⟨2150743617343630900559501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433829078229087267039667 2150743617343630900559501)
                ·
                  refine ⟨806528856503861587709813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2150743617343630900559501 806528856503861587709813)
                  ·
                    refine ⟨75612080297237023847795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 806528856503861587709813 75612080297237023847795)
                    ·
                      rfl

theorem cell22_220881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_220881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220881 prefixEnd_220881 := by exact prefixLift 220881
  have htrace : WordTrace (prefixWord ++ tailWord_220881) baseStart_220881 baseEnd_220881 := by
    simpa [prefixWord, tailWord_220881, baseEnd_220881] using wordTrace_append hprefix tailTrace_220881
  have hstable : (prefixWord ++ tailWord_220881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220881).length < 2 ^ (prefixWord ++ tailWord_220881).sum := by decide
  have hdescent : baseEnd_220881 < baseStart_220881 := by decide
  rcases family_descends (prefixWord ++ tailWord_220881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220893 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_220893 : Nat := 118140960795 + 220893 * 2 ^ 59
def prefixEnd_220893 : Nat := 4983230072969 + 3 ^ 40 * 220893 * 2
def baseEnd_220893 : Nat := 75616188142472992547759

theorem tailTrace_220893 : CollatzResearch.WordTrace tailWord_220893 prefixEnd_220893 75616188142472992547759 := by
  unfold tailWord_220893
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056629588749861366027333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5371086392499907577351555 8056629588749861366027333)
  ·
    refine ⟨1510618047890599006130125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8056629588749861366027333 1510618047890599006130125)
    ·
      refine ⟨566481767958974627298797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1510618047890599006130125 566481767958974627298797)
      ·
        refine ⟨212430662984615485237049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 566481767958974627298797 212430662984615485237049)
        ·
          refine ⟨159322997238461613927787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212430662984615485237049 159322997238461613927787)
          ·
            refine ⟨238984495857692420891681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159322997238461613927787 238984495857692420891681)
            ·
              refine ⟨179238371893269315668761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238984495857692420891681 179238371893269315668761)
              ·
                refine ⟨134428778919951986751571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179238371893269315668761 134428778919951986751571)
                ·
                  refine ⟨201643168379927980127357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134428778919951986751571 201643168379927980127357)
                  ·
                    refine ⟨75616188142472992547759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201643168379927980127357 75616188142472992547759)
                    ·
                      rfl

theorem cell22_220893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_220893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220893 prefixEnd_220893 := by exact prefixLift 220893
  have htrace : WordTrace (prefixWord ++ tailWord_220893) baseStart_220893 baseEnd_220893 := by
    simpa [prefixWord, tailWord_220893, baseEnd_220893] using wordTrace_append hprefix tailTrace_220893
  have hstable : (prefixWord ++ tailWord_220893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220893).length < 2 ^ (prefixWord ++ tailWord_220893).sum := by decide
  have hdescent : baseEnd_220893 < baseStart_220893 := by decide
  rcases family_descends (prefixWord ++ tailWord_220893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220960 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_220960 : Nat := 118140960795 + 220960 * 2 ^ 59
def prefixEnd_220960 : Nat := 4983230072969 + 3 ^ 40 * 220960 * 2
def baseEnd_220960 : Nat := 75639123611707151122553

theorem tailTrace_220960 : CollatzResearch.WordTrace tailWord_220960 prefixEnd_220960 75639123611707151122553 := by
  unfold tailWord_220960
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029536639753565904358167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5372715519671421205810889 4029536639753565904358167)
  ·
    refine ⟨6044304959630348856537251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4029536639753565904358167 6044304959630348856537251)
    ·
      refine ⟨9066457439445523284805877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6044304959630348856537251 9066457439445523284805877)
      ·
        refine ⟨849980384948017807950551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9066457439445523284805877 849980384948017807950551)
        ·
          refine ⟨1274970577422026711925827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849980384948017807950551 1274970577422026711925827)
          ·
            refine ⟨1912455866133040067888741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274970577422026711925827 1912455866133040067888741)
            ·
              refine ⟨358585474899945012729139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1912455866133040067888741 358585474899945012729139)
              ·
                refine ⟨537878212349917519093709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358585474899945012729139 537878212349917519093709)
                ·
                  refine ⟨201704329631219069660141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537878212349917519093709 201704329631219069660141)
                  ·
                    refine ⟨75639123611707151122553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201704329631219069660141 75639123611707151122553)
                    ·
                      rfl

theorem cell22_220960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_220960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220960 prefixEnd_220960 := by exact prefixLift 220960
  have htrace : WordTrace (prefixWord ++ tailWord_220960) baseStart_220960 baseEnd_220960 := by
    simpa [prefixWord, tailWord_220960, baseEnd_220960] using wordTrace_append hprefix tailTrace_220960
  have hstable : (prefixWord ++ tailWord_220960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220960).length < 2 ^ (prefixWord ++ tailWord_220960).sum := by decide
  have hdescent : baseEnd_220960 < baseStart_220960 := by decide
  rcases family_descends (prefixWord ++ tailWord_220960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220971 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_220971 : Nat := 118140960795 + 220971 * 2 ^ 59
def prefixEnd_220971 : Nat := 4983230072969 + 3 ^ 40 * 220971 * 2
def baseEnd_220971 : Nat := 75642889136506789097519

theorem tailTrace_220971 : CollatzResearch.WordTrace tailWord_220971 prefixEnd_220971 75642889136506789097519 := by
  unfold tailWord_220971
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059474482467280687366767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5372982988311520458244511 8059474482467280687366767)
  ·
    refine ⟨12089211723700921031050151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8059474482467280687366767 12089211723700921031050151)
    ·
      refine ⟨18133817585551381546575227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12089211723700921031050151 18133817585551381546575227)
      ·
        refine ⟨27200726378327072319862841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133817585551381546575227 27200726378327072319862841)
        ·
          refine ⟨20400544783745304239897131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27200726378327072319862841 20400544783745304239897131)
          ·
            refine ⟨30600817175617956359845697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20400544783745304239897131 30600817175617956359845697)
            ·
              refine ⟨22950612881713467269884273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30600817175617956359845697 22950612881713467269884273)
              ·
                refine ⟨17212959661285100452413205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22950612881713467269884273 17212959661285100452413205)
                ·
                  refine ⟨806857484122739083706869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17212959661285100452413205 806857484122739083706869)
                  ·
                    refine ⟨75642889136506789097519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 806857484122739083706869 75642889136506789097519)
                    ·
                      rfl

theorem cell22_220971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_220971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_220971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_220971 prefixEnd_220971 := by exact prefixLift 220971
  have htrace : WordTrace (prefixWord ++ tailWord_220971) baseStart_220971 baseEnd_220971 := by
    simpa [prefixWord, tailWord_220971, baseEnd_220971] using wordTrace_append hprefix tailTrace_220971
  have hstable : (prefixWord ++ tailWord_220971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220971).length < 2 ^ (prefixWord ++ tailWord_220971).sum := by decide
  have hdescent : baseEnd_220971 < baseStart_220971 := by decide
  rcases family_descends (prefixWord ++ tailWord_220971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221063 : List Nat := [1, 1, 4, 2, 4, 10]
def baseStart_221063 : Nat := 118140960795 + 221063 * 2 ^ 59
def prefixEnd_221063 : Nat := 4983230072969 + 3 ^ 40 * 221063 * 2
def baseEnd_221063 : Nat := 934251637242582911077

theorem tailTrace_221063 : CollatzResearch.WordTrace tailWord_221063 prefixEnd_221063 934251637242582911077 := by
  unfold tailWord_221063
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062829998133980399715843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5375219998755986933143895 8062829998133980399715843)
  ·
    refine ⟨12094244997200970599573765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062829998133980399715843 12094244997200970599573765)
    ·
      refine ⟨2267670936975181987420081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12094244997200970599573765 2267670936975181987420081)
      ·
        refine ⟨1700753202731386490565061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267670936975181987420081 1700753202731386490565061)
        ·
          refine ⟨318891225512134966980949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1700753202731386490565061 318891225512134966980949)
          ·
            refine ⟨934251637242582911077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 318891225512134966980949 934251637242582911077)
            ·
              rfl

theorem cell22_221063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 10].length) (baseStart_221063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221063 prefixEnd_221063 := by exact prefixLift 221063
  have htrace : WordTrace (prefixWord ++ tailWord_221063) baseStart_221063 baseEnd_221063 := by
    simpa [prefixWord, tailWord_221063, baseEnd_221063] using wordTrace_append hprefix tailTrace_221063
  have hstable : (prefixWord ++ tailWord_221063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221063).length < 2 ^ (prefixWord ++ tailWord_221063).sum := by decide
  have hdescent : baseEnd_221063 < baseStart_221063 := by decide
  rcases family_descends (prefixWord ++ tailWord_221063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221140 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_221140 : Nat := 118140960795 + 221140 * 2 ^ 59
def prefixEnd_221140 : Nat := 4983230072969 + 3 ^ 40 * 221140 * 2
def baseEnd_221140 : Nat := 75700741290246681622001

theorem tailTrace_221140 : CollatzResearch.WordTrace tailWord_221140 prefixEnd_221140 75700741290246681622001 := by
  unfold tailWord_221140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032819209427511275134437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5377092279236681700179249 4032819209427511275134437)
  ·
    refine ⟨756153601767658364087707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4032819209427511275134437 756153601767658364087707)
    ·
      refine ⟨1134230402651487546131561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756153601767658364087707 1134230402651487546131561)
      ·
        refine ⟨850672801988615659598671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1134230402651487546131561 850672801988615659598671)
        ·
          refine ⟨1276009202982923489398007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850672801988615659598671 1276009202982923489398007)
          ·
            refine ⟨1914013804474385234097011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276009202982923489398007 1914013804474385234097011)
            ·
              refine ⟨2871020706711577851145517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914013804474385234097011 2871020706711577851145517)
              ·
                refine ⟨1076632765016841694179569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2871020706711577851145517 1076632765016841694179569)
                ·
                  refine ⟨807474573762631270634677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1076632765016841694179569 807474573762631270634677)
                  ·
                    refine ⟨75700741290246681622001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 807474573762631270634677 75700741290246681622001)
                    ·
                      rfl

theorem cell22_221140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_221140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221140 prefixEnd_221140 := by exact prefixLift 221140
  have htrace : WordTrace (prefixWord ++ tailWord_221140) baseStart_221140 baseEnd_221140 := by
    simpa [prefixWord, tailWord_221140, baseEnd_221140] using wordTrace_append hprefix tailTrace_221140
  have hstable : (prefixWord ++ tailWord_221140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221140).length < 2 ^ (prefixWord ++ tailWord_221140).sum := by decide
  have hdescent : baseEnd_221140 < baseStart_221140 := by decide
  rcases family_descends (prefixWord ++ tailWord_221140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221148 : List Nat := [2, 2, 6, 1, 2, 1, 2, 6]
def baseStart_221148 : Nat := 118140960795 + 221148 * 2 ^ 59
def prefixEnd_221148 : Nat := 4983230072969 + 3 ^ 40 * 221148 * 2
def baseEnd_221148 : Nat := 8411497761526369713553

theorem tailTrace_221148 : CollatzResearch.WordTrace tailWord_221148 prefixEnd_221148 8411497761526369713553 := by
  unfold tailWord_221148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032965101413019958280049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5377286801884026611040065 4032965101413019958280049)
  ·
    refine ⟨3024723826059764968710037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4032965101413019958280049 3024723826059764968710037)
    ·
      refine ⟨141783929346551482908283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3024723826059764968710037 141783929346551482908283)
      ·
        refine ⟨212675894019827224362425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141783929346551482908283 212675894019827224362425)
        ·
          refine ⟨159506920514870418271819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212675894019827224362425 159506920514870418271819)
          ·
            refine ⟨239260380772305627407729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159506920514870418271819 239260380772305627407729)
            ·
              refine ⟨179445285579229220555797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239260380772305627407729 179445285579229220555797)
              ·
                refine ⟨8411497761526369713553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179445285579229220555797 8411497761526369713553)
                ·
                  rfl

theorem cell22_221148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 6].length) (baseStart_221148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221148 prefixEnd_221148 := by exact prefixLift 221148
  have htrace : WordTrace (prefixWord ++ tailWord_221148) baseStart_221148 baseEnd_221148 := by
    simpa [prefixWord, tailWord_221148, baseEnd_221148] using wordTrace_append hprefix tailTrace_221148
  have hstable : (prefixWord ++ tailWord_221148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221148).length < 2 ^ (prefixWord ++ tailWord_221148).sum := by decide
  have hdescent : baseEnd_221148 < baseStart_221148 := by decide
  rcases family_descends (prefixWord ++ tailWord_221148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221245 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_221245 : Nat := 118140960795 + 221245 * 2 ^ 59
def prefixEnd_221245 : Nat := 4983230072969 + 3 ^ 40 * 221245 * 2
def baseEnd_221245 : Nat := 75736684936061407746679

theorem tailTrace_221245 : CollatzResearch.WordTrace tailWord_221245 prefixEnd_221245 75736684936061407746679 := by
  unfold tailWord_221245
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069468083474625482841189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5379645388983083655227459 8069468083474625482841189)
  ·
    refine ⟨1513025265651492278032723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8069468083474625482841189 1513025265651492278032723)
    ·
      refine ⟨2269537898477238417049085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1513025265651492278032723 2269537898477238417049085)
      ·
        refine ⟨851076711928964406393407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2269537898477238417049085 851076711928964406393407)
        ·
          refine ⟨1276615067893446609590111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851076711928964406393407 1276615067893446609590111)
          ·
            refine ⟨1914922601840169914385167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276615067893446609590111 1914922601840169914385167)
            ·
              refine ⟨2872383902760254871577751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914922601840169914385167 2872383902760254871577751)
              ·
                refine ⟨4308575854140382307366627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872383902760254871577751 4308575854140382307366627)
                ·
                  refine ⟨6462863781210573461049941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308575854140382307366627 6462863781210573461049941)
                  ·
                    refine ⟨75736684936061407746679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6462863781210573461049941 75736684936061407746679)
                    ·
                      rfl

theorem cell22_221245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_221245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221245 prefixEnd_221245 := by exact prefixLift 221245
  have htrace : WordTrace (prefixWord ++ tailWord_221245) baseStart_221245 baseEnd_221245 := by
    simpa [prefixWord, tailWord_221245, baseEnd_221245] using wordTrace_append hprefix tailTrace_221245
  have hstable : (prefixWord ++ tailWord_221245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221245).length < 2 ^ (prefixWord ++ tailWord_221245).sum := by decide
  have hdescent : baseEnd_221245 < baseStart_221245 := by decide
  rcases family_descends (prefixWord ++ tailWord_221245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221322 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_221322 : Nat := 118140960795 + 221322 * 2 ^ 59
def prefixEnd_221322 : Nat := 4983230072969 + 3 ^ 40 * 221322 * 2
def baseEnd_221322 : Nat := 25254347869886291190481

theorem tailTrace_221322 : CollatzResearch.WordTrace tailWord_221322 prefixEnd_221322 25254347869886291190481 := by
  unfold tailWord_221322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018069126048916908348555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5381517669463778422262813 2018069126048916908348555)
  ·
    refine ⟨3027103689073375362522833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018069126048916908348555 3027103689073375362522833)
    ·
      refine ⟨2270327766805031521892125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3027103689073375362522833 2270327766805031521892125)
      ·
        refine ⟨851372912551886820709547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2270327766805031521892125 851372912551886820709547)
        ·
          refine ⟨1277059368827830231064321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851372912551886820709547 1277059368827830231064321)
          ·
            refine ⟨957794526620872673298241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1277059368827830231064321 957794526620872673298241)
            ·
              refine ⟨718345894965654504973681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957794526620872673298241 718345894965654504973681)
              ·
                refine ⟨538759421224240878730261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718345894965654504973681 538759421224240878730261)
                ·
                  refine ⟨25254347869886291190481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 538759421224240878730261 25254347869886291190481)
                  ·
                    rfl

theorem cell22_221322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_221322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221322 prefixEnd_221322 := by exact prefixLift 221322
  have htrace : WordTrace (prefixWord ++ tailWord_221322) baseStart_221322 baseEnd_221322 := by
    simpa [prefixWord, tailWord_221322, baseEnd_221322] using wordTrace_append hprefix tailTrace_221322
  have hstable : (prefixWord ++ tailWord_221322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221322).length < 2 ^ (prefixWord ++ tailWord_221322).sum := by decide
  have hdescent : baseEnd_221322 < baseStart_221322 := by decide
  rcases family_descends (prefixWord ++ tailWord_221322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221332 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_221332 : Nat := 118140960795 + 221332 * 2 ^ 59
def prefixEnd_221332 : Nat := 4983230072969 + 3 ^ 40 * 221332 * 2
def baseEnd_221332 : Nat := 75766466814022180821413

theorem tailTrace_221332 : CollatzResearch.WordTrace tailWord_221332 prefixEnd_221332 75766466814022180821413 := by
  unfold tailWord_221332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036320617079719670629125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5381760822772959560838833 4036320617079719670629125)
  ·
    refine ⟨756810115702447438242961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4036320617079719670629125 756810115702447438242961)
    ·
      refine ⟨567607586776835578682221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 756810115702447438242961 567607586776835578682221)
      ·
        refine ⟨212852845041313342005833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567607586776835578682221 212852845041313342005833)
        ·
          refine ⟨159639633780985006504375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212852845041313342005833 159639633780985006504375)
          ·
            refine ⟨239459450671477509756563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159639633780985006504375 239459450671477509756563)
            ·
              refine ⟨359189176007216264634845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239459450671477509756563 359189176007216264634845)
              ·
                refine ⟨134695941002706099238067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359189176007216264634845 134695941002706099238067)
                ·
                  refine ⟨202043911504059148857101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134695941002706099238067 202043911504059148857101)
                  ·
                    refine ⟨75766466814022180821413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202043911504059148857101 75766466814022180821413)
                    ·
                      rfl

theorem cell22_221332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_221332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221332 prefixEnd_221332 := by exact prefixLift 221332
  have htrace : WordTrace (prefixWord ++ tailWord_221332) baseStart_221332 baseEnd_221332 := by
    simpa [prefixWord, tailWord_221332, baseEnd_221332] using wordTrace_append hprefix tailTrace_221332
  have hstable : (prefixWord ++ tailWord_221332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221332).length < 2 ^ (prefixWord ++ tailWord_221332).sum := by decide
  have hdescent : baseEnd_221332 < baseStart_221332 := by decide
  rcases family_descends (prefixWord ++ tailWord_221332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221367 : List Nat := [1, 1, 3, 1, 4, 3, 2, 7]
def baseStart_221367 : Nat := 118140960795 + 221367 * 2 ^ 59
def prefixEnd_221367 : Nat := 4983230072969 + 3 ^ 40 * 221367 * 2
def baseEnd_221367 : Nat := 8419827558810417355145

theorem tailTrace_221367 : CollatzResearch.WordTrace tailWord_221367 prefixEnd_221367 8419827558810417355145 := by
  unfold tailWord_221367
  simp only [CollatzResearch.WordTrace]
  refine ⟨8073917789032640318782355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5382611859355093545854903 8073917789032640318782355)
  ·
    refine ⟨12110876683548960478173533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8073917789032640318782355 12110876683548960478173533)
    ·
      refine ⟨4541578756330860179315075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12110876683548960478173533 4541578756330860179315075)
      ·
        refine ⟨6812368134496290268972613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541578756330860179315075 6812368134496290268972613)
        ·
          refine ⟨1277319025218054425432365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6812368134496290268972613 1277319025218054425432365)
          ·
            refine ⟨478994634456770409537137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1277319025218054425432365 478994634456770409537137)
            ·
              refine ⟨359245975842577807152853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478994634456770409537137 359245975842577807152853)
              ·
                refine ⟨8419827558810417355145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 359245975842577807152853 8419827558810417355145)
                ·
                  rfl

theorem cell22_221367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 7].length) (baseStart_221367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221367 prefixEnd_221367 := by exact prefixLift 221367
  have htrace : WordTrace (prefixWord ++ tailWord_221367) baseStart_221367 baseEnd_221367 := by
    simpa [prefixWord, tailWord_221367, baseEnd_221367] using wordTrace_append hprefix tailTrace_221367
  have hstable : (prefixWord ++ tailWord_221367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221367).length < 2 ^ (prefixWord ++ tailWord_221367).sum := by decide
  have hdescent : baseEnd_221367 < baseStart_221367 := by decide
  rcases family_descends (prefixWord ++ tailWord_221367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221427 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 2, 5]
def baseStart_221427 : Nat := 118140960795 + 221427 * 2 ^ 59
def prefixEnd_221427 : Nat := 4983230072969 + 3 ^ 40 * 221427 * 2
def baseEnd_221427 : Nat := 75798987255473599696121

theorem tailTrace_221427 : CollatzResearch.WordTrace tailWord_221427 prefixEnd_221427 75798987255473599696121 := by
  unfold tailWord_221427
  simp only [CollatzResearch.WordTrace]
  refine ⟨8076106168815270565966535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5384070779210180377311023 8076106168815270565966535)
  ·
    refine ⟨12114159253222905848949803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8076106168815270565966535 12114159253222905848949803)
    ·
      refine ⟨18171238879834358773424705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12114159253222905848949803 18171238879834358773424705)
      ·
        refine ⟨13628429159875769080068529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18171238879834358773424705 13628429159875769080068529)
        ·
          refine ⟨10221321869906826810051397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13628429159875769080068529 10221321869906826810051397)
          ·
            refine ⟨1916497850607530026884637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10221321869906826810051397 1916497850607530026884637)
            ·
              refine ⟨718686693977823760081739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1916497850607530026884637 718686693977823760081739)
              ·
                refine ⟨1078030040966735640122609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718686693977823760081739 1078030040966735640122609)
                ·
                  refine ⟨808522530725051730091957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1078030040966735640122609 808522530725051730091957)
                  ·
                    refine ⟨75798987255473599696121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 808522530725051730091957 75798987255473599696121)
                    ·
                      rfl

theorem cell22_221427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_221427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221427 prefixEnd_221427 := by exact prefixLift 221427
  have htrace : WordTrace (prefixWord ++ tailWord_221427) baseStart_221427 baseEnd_221427 := by
    simpa [prefixWord, tailWord_221427, baseEnd_221427] using wordTrace_append hprefix tailTrace_221427
  have hstable : (prefixWord ++ tailWord_221427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221427).length < 2 ^ (prefixWord ++ tailWord_221427).sum := by decide
  have hdescent : baseEnd_221427 < baseStart_221427 := by decide
  rcases family_descends (prefixWord ++ tailWord_221427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221474 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_221474 : Nat := 118140960795 + 221474 * 2 ^ 59
def prefixEnd_221474 : Nat := 4983230072969 + 3 ^ 40 * 221474 * 2
def baseEnd_221474 : Nat := 25271692105327047923659

theorem tailTrace_221474 : CollatzResearch.WordTrace tailWord_221474 prefixEnd_221474 25271692105327047923659 := by
  unfold tailWord_221474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019455099911249398231869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5385213599763331728618317 2019455099911249398231869)
  ·
    refine ⟨757295662466718524336951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2019455099911249398231869 757295662466718524336951)
    ·
      refine ⟨1135943493700077786505427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757295662466718524336951 1135943493700077786505427)
      ·
        refine ⟨1703915240550116679758141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135943493700077786505427 1703915240550116679758141)
        ·
          refine ⟨638968215206293754909303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1703915240550116679758141 638968215206293754909303)
          ·
            refine ⟨958452322809440632363955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638968215206293754909303 958452322809440632363955)
            ·
              refine ⟨1437678484214160948545933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958452322809440632363955 1437678484214160948545933)
              ·
                refine ⟨539129431580310355704725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1437678484214160948545933 539129431580310355704725)
                ·
                  refine ⟨25271692105327047923659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 539129431580310355704725 25271692105327047923659)
                  ·
                    rfl

theorem cell22_221474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_221474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221474 prefixEnd_221474 := by exact prefixLift 221474
  have htrace : WordTrace (prefixWord ++ tailWord_221474) baseStart_221474 baseEnd_221474 := by
    simpa [prefixWord, tailWord_221474, baseEnd_221474] using wordTrace_append hprefix tailTrace_221474
  have hstable : (prefixWord ++ tailWord_221474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221474).length < 2 ^ (prefixWord ++ tailWord_221474).sum := by decide
  have hdescent : baseEnd_221474 < baseStart_221474 := by decide
  rcases family_descends (prefixWord ++ tailWord_221474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221487 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_221487 : Nat := 118140960795 + 221487 * 2 ^ 59
def prefixEnd_221487 : Nat := 4983230072969 + 3 ^ 40 * 221487 * 2
def baseEnd_221487 : Nat := 75819526481653443195937

theorem tailTrace_221487 : CollatzResearch.WordTrace tailWord_221487 prefixEnd_221487 75819526481653443195937 := by
  unfold tailWord_221487
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078294548597900813150715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5385529699065267208767143 8078294548597900813150715)
  ·
    refine ⟨12117441822896851219726073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8078294548597900813150715 12117441822896851219726073)
    ·
      refine ⟨9088081367172638414794555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12117441822896851219726073 9088081367172638414794555)
      ·
        refine ⟨13632122050758957622191833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088081367172638414794555 13632122050758957622191833)
        ·
          refine ⟨10224091538069218216643875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13632122050758957622191833 10224091538069218216643875)
          ·
            refine ⟨15336137307103827324965813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224091538069218216643875 15336137307103827324965813)
            ·
              refine ⟨1437762872540983811715545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15336137307103827324965813 1437762872540983811715545)
              ·
                refine ⟨1078322154405737858786659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437762872540983811715545 1078322154405737858786659)
                ·
                  refine ⟨1617483231608606788179989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078322154405737858786659 1617483231608606788179989)
                  ·
                    refine ⟨75819526481653443195937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1617483231608606788179989 75819526481653443195937)
                    ·
                      rfl

theorem cell22_221487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_221487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221487 prefixEnd_221487 := by exact prefixLift 221487
  have htrace : WordTrace (prefixWord ++ tailWord_221487) baseStart_221487 baseEnd_221487 := by
    simpa [prefixWord, tailWord_221487, baseEnd_221487] using wordTrace_append hprefix tailTrace_221487
  have hstable : (prefixWord ++ tailWord_221487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221487).length < 2 ^ (prefixWord ++ tailWord_221487).sum := by decide
  have hdescent : baseEnd_221487 < baseStart_221487 := by decide
  rcases family_descends (prefixWord ++ tailWord_221487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221598 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_221598 : Nat := 118140960795 + 221598 * 2 ^ 59
def prefixEnd_221598 : Nat := 4983230072969 + 3 ^ 40 * 221598 * 2
def baseEnd_221598 : Nat := 25285841350028717890199

theorem tailTrace_221598 : CollatzResearch.WordTrace tailWord_221598 prefixEnd_221598 25285841350028717890199 := by
  unfold tailWord_221598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010292881399470846305181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5388228700797177846960965 1010292881399470846305181)
  ·
    refine ⟨378859830524801567364443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1010292881399470846305181 378859830524801567364443)
    ·
      refine ⟨568289745787202351046665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378859830524801567364443 568289745787202351046665)
      ·
        refine ⟨426217309340401763284999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568289745787202351046665 426217309340401763284999)
        ·
          refine ⟨639325964010602644927499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426217309340401763284999 639325964010602644927499)
          ·
            refine ⟨958988946015903967391249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639325964010602644927499 958988946015903967391249)
            ·
              refine ⟨719241709511927975543437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958988946015903967391249 719241709511927975543437)
              ·
                refine ⟨269715641066972990828789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719241709511927975543437 269715641066972990828789)
                ·
                  refine ⟨25285841350028717890199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269715641066972990828789 25285841350028717890199)
                  ·
                    rfl

theorem cell22_221598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_221598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221598 prefixEnd_221598 := by exact prefixLift 221598
  have htrace : WordTrace (prefixWord ++ tailWord_221598) baseStart_221598 baseEnd_221598 := by
    simpa [prefixWord, tailWord_221598, baseEnd_221598] using wordTrace_append hprefix tailTrace_221598
  have hstable : (prefixWord ++ tailWord_221598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221598).length < 2 ^ (prefixWord ++ tailWord_221598).sum := by decide
  have hdescent : baseEnd_221598 < baseStart_221598 := by decide
  rcases family_descends (prefixWord ++ tailWord_221598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221628 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_221628 : Nat := 118140960795 + 221628 * 2 ^ 59
def prefixEnd_221628 : Nat := 4983230072969 + 3 ^ 40 * 221628 * 2
def baseEnd_221628 : Nat := 75867793663176075420505

theorem tailTrace_221628 : CollatzResearch.WordTrace tailWord_221628 prefixEnd_221628 75867793663176075420505 := by
  unfold tailWord_221628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041718620543540947016769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5388958160724721262689025 4041718620543540947016769)
  ·
    refine ⟨3031288965407655710262577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4041718620543540947016769 3031288965407655710262577)
    ·
      refine ⟨2273466724055741782696933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3031288965407655710262577 2273466724055741782696933)
      ·
        refine ⟨426275010760451584255675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2273466724055741782696933 426275010760451584255675)
        ·
          refine ⟨639412516140677376383513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426275010760451584255675 639412516140677376383513)
          ·
            refine ⟨479559387105508032287635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639412516140677376383513 479559387105508032287635)
            ·
              refine ⟨719339080658262048431453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479559387105508032287635 719339080658262048431453)
              ·
                refine ⟨269752155246848268161795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719339080658262048431453 269752155246848268161795)
                ·
                  refine ⟨404628232870272402242693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269752155246848268161795 404628232870272402242693)
                  ·
                    refine ⟨75867793663176075420505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404628232870272402242693 75867793663176075420505)
                    ·
                      rfl

theorem cell22_221628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_221628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221628 prefixEnd_221628 := by exact prefixLift 221628
  have htrace : WordTrace (prefixWord ++ tailWord_221628) baseStart_221628 baseEnd_221628 := by
    simpa [prefixWord, tailWord_221628, baseEnd_221628] using wordTrace_append hprefix tailTrace_221628
  have hstable : (prefixWord ++ tailWord_221628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221628).length < 2 ^ (prefixWord ++ tailWord_221628).sum := by decide
  have hdescent : baseEnd_221628 < baseStart_221628 := by decide
  rcases family_descends (prefixWord ++ tailWord_221628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221699 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 7]
def baseStart_221699 : Nat := 118140960795 + 221699 * 2 ^ 59
def prefixEnd_221699 : Nat := 4983230072969 + 3 ^ 40 * 221699 * 2
def baseEnd_221699 : Nat := 25297366138051852298429

theorem tailTrace_221699 : CollatzResearch.WordTrace tailWord_221699 prefixEnd_221699 25297366138051852298429 := by
  unfold tailWord_221699
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086026823829861019868151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5390684549219907346578767 8086026823829861019868151)
  ·
    refine ⟨12129040235744791529802227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8086026823829861019868151 12129040235744791529802227)
    ·
      refine ⟨18193560353617187294703341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12129040235744791529802227 18193560353617187294703341)
      ·
        refine ⟨6822585132606445235513753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18193560353617187294703341 6822585132606445235513753)
        ·
          refine ⟨5116938849454833926635315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6822585132606445235513753 5116938849454833926635315)
          ·
            refine ⟨7675408274182250889952973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116938849454833926635315 7675408274182250889952973)
            ·
              refine ⟨2878278102818344083732365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7675408274182250889952973 2878278102818344083732365)
              ·
                refine ⟨1079354288556879031399637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2878278102818344083732365 1079354288556879031399637)
                ·
                  refine ⟨25297366138051852298429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1079354288556879031399637 25297366138051852298429)
                  ·
                    rfl

theorem cell22_221699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_221699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221699 prefixEnd_221699 := by exact prefixLift 221699
  have htrace : WordTrace (prefixWord ++ tailWord_221699) baseStart_221699 baseEnd_221699 := by
    simpa [prefixWord, tailWord_221699, baseEnd_221699] using wordTrace_append hprefix tailTrace_221699
  have hstable : (prefixWord ++ tailWord_221699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221699).length < 2 ^ (prefixWord ++ tailWord_221699).sum := by decide
  have hdescent : baseEnd_221699 < baseStart_221699 := by decide
  rcases family_descends (prefixWord ++ tailWord_221699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221709 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_221709 : Nat := 118140960795 + 221709 * 2 ^ 59
def prefixEnd_221709 : Nat := 4983230072969 + 3 ^ 40 * 221709 * 2
def baseEnd_221709 : Nat := 75895521618518864145257

theorem tailTrace_221709 : CollatzResearch.WordTrace tailWord_221709 prefixEnd_221709 75895521618518864145257 := by
  unfold tailWord_221709
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086391553793632727732181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5390927702529088485154787 8086391553793632727732181)
  ·
    refine ⟨189524802042038267056223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8086391553793632727732181 189524802042038267056223)
    ·
      refine ⟨284287203063057400584335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189524802042038267056223 284287203063057400584335)
      ·
        refine ⟨426430804594586100876503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284287203063057400584335 426430804594586100876503)
        ·
          refine ⟨639646206891879151314755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426430804594586100876503 639646206891879151314755)
          ·
            refine ⟨959469310337818726972133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639646206891879151314755 959469310337818726972133)
            ·
              refine ⟨179900495688341011307275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 959469310337818726972133 179900495688341011307275)
              ·
                refine ⟨269850743532511516960913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179900495688341011307275 269850743532511516960913)
                ·
                  refine ⟨202388057649383637720685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269850743532511516960913 202388057649383637720685)
                  ·
                    refine ⟨75895521618518864145257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202388057649383637720685 75895521618518864145257)
                    ·
                      rfl

theorem cell22_221709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_221709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221709 prefixEnd_221709 := by exact prefixLift 221709
  have htrace : WordTrace (prefixWord ++ tailWord_221709) baseStart_221709 baseEnd_221709 := by
    simpa [prefixWord, tailWord_221709, baseEnd_221709] using wordTrace_append hprefix tailTrace_221709
  have hstable : (prefixWord ++ tailWord_221709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221709).length < 2 ^ (prefixWord ++ tailWord_221709).sum := by decide
  have hdescent : baseEnd_221709 < baseStart_221709 := by decide
  rcases family_descends (prefixWord ++ tailWord_221709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221750 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_221750 : Nat := 118140960795 + 221750 * 2 ^ 59
def prefixEnd_221750 : Nat := 4983230072969 + 3 ^ 40 * 221750 * 2
def baseEnd_221750 : Nat := 25303185585469474623377

theorem tailTrace_221750 : CollatzResearch.WordTrace tailWord_221750 prefixEnd_221750 25303185585469474623377 := by
  unfold tailWord_221750
  simp only [CollatzResearch.WordTrace]
  refine ⟨505492934165318545623419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5391924631096731153316469 505492934165318545623419)
  ·
    refine ⟨758239401247977818435129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 505492934165318545623419 758239401247977818435129)
    ·
      refine ⟨568679550935983363826347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 758239401247977818435129 568679550935983363826347)
      ·
        refine ⟨853019326403975045739521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568679550935983363826347 853019326403975045739521)
        ·
          refine ⟨639764494802981284304641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853019326403975045739521 639764494802981284304641)
          ·
            refine ⟨479823371102235963228481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639764494802981284304641 479823371102235963228481)
            ·
              refine ⟨359867528326676972421361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479823371102235963228481 359867528326676972421361)
              ·
                refine ⟨269900646245007729316021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359867528326676972421361 269900646245007729316021)
                ·
                  refine ⟨25303185585469474623377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269900646245007729316021 25303185585469474623377)
                  ·
                    rfl

theorem cell22_221750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_221750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221750 prefixEnd_221750 := by exact prefixLift 221750
  have htrace : WordTrace (prefixWord ++ tailWord_221750) baseStart_221750 baseEnd_221750 := by
    simpa [prefixWord, tailWord_221750, baseEnd_221750] using wordTrace_append hprefix tailTrace_221750
  have hstable : (prefixWord ++ tailWord_221750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221750).length < 2 ^ (prefixWord ++ tailWord_221750).sum := by decide
  have hdescent : baseEnd_221750 < baseStart_221750 := by decide
  rcases family_descends (prefixWord ++ tailWord_221750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221797 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_221797 : Nat := 118140960795 + 221797 * 2 ^ 59
def prefixEnd_221797 : Nat := 4983230072969 + 3 ^ 40 * 221797 * 2
def baseEnd_221797 : Nat := 75925645816915967944987

theorem tailTrace_221797 : CollatzResearch.WordTrace tailWord_221797 prefixEnd_221797 75925645816915967944987 := by
  unfold tailWord_221797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089601177474823756935645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5393067451649882504623763 8089601177474823756935645)
  ·
    refine ⟨3033600441553058908850867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8089601177474823756935645 3033600441553058908850867)
    ·
      refine ⟨4550400662329588363276301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3033600441553058908850867 4550400662329588363276301)
      ·
        refine ⟨1706400248373595636228613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4550400662329588363276301 1706400248373595636228613)
        ·
          refine ⟨319950046570049181792865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1706400248373595636228613 319950046570049181792865)
          ·
            refine ⟨239962534927536886344649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319950046570049181792865 239962534927536886344649)
            ·
              refine ⟨179971901195652664758487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239962534927536886344649 179971901195652664758487)
              ·
                refine ⟨269957851793478997137731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179971901195652664758487 269957851793478997137731)
                ·
                  refine ⟨404936777690218495706597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269957851793478997137731 404936777690218495706597)
                  ·
                    refine ⟨75925645816915967944987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404936777690218495706597 75925645816915967944987)
                    ·
                      rfl

theorem cell22_221797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_221797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221797 prefixEnd_221797 := by exact prefixLift 221797
  have htrace : WordTrace (prefixWord ++ tailWord_221797) baseStart_221797 baseEnd_221797 := by
    simpa [prefixWord, tailWord_221797, baseEnd_221797] using wordTrace_append hprefix tailTrace_221797
  have hstable : (prefixWord ++ tailWord_221797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221797).length < 2 ^ (prefixWord ++ tailWord_221797).sum := by decide
  have hdescent : baseEnd_221797 < baseStart_221797 := by decide
  rcases family_descends (prefixWord ++ tailWord_221797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221810 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_221810 : Nat := 118140960795 + 221810 * 2 ^ 59
def prefixEnd_221810 : Nat := 4983230072969 + 3 ^ 40 * 221810 * 2
def baseEnd_221810 : Nat := 75930095982588267369947

theorem tailTrace_221810 : CollatzResearch.WordTrace tailWord_221810 prefixEnd_221810 75930095982588267369947 := by
  unfold tailWord_221810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022518831606931744289721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5393383550951817984772589 2022518831606931744289721)
  ·
    refine ⟨1516889123705198808217291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2022518831606931744289721 1516889123705198808217291)
    ·
      refine ⟨2275333685557798212325937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516889123705198808217291 2275333685557798212325937)
      ·
        refine ⟨1706500264168348659244453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2275333685557798212325937 1706500264168348659244453)
        ·
          refine ⟨319968799531565373608335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1706500264168348659244453 319968799531565373608335)
          ·
            refine ⟨479953199297348060412503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319968799531565373608335 479953199297348060412503)
            ·
              refine ⟨719929798946022090618755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479953199297348060412503 719929798946022090618755)
              ·
                refine ⟨1079894698419033135928133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719929798946022090618755 1079894698419033135928133)
                ·
                  refine ⟨202480255953568712986525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079894698419033135928133 202480255953568712986525)
                  ·
                    refine ⟨75930095982588267369947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202480255953568712986525 75930095982588267369947)
                    ·
                      rfl

theorem cell22_221810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_221810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221810 prefixEnd_221810 := by exact prefixLift 221810
  have htrace : WordTrace (prefixWord ++ tailWord_221810) baseStart_221810 baseEnd_221810 := by
    simpa [prefixWord, tailWord_221810, baseEnd_221810] using wordTrace_append hprefix tailTrace_221810
  have hstable : (prefixWord ++ tailWord_221810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221810).length < 2 ^ (prefixWord ++ tailWord_221810).sum := by decide
  have hdescent : baseEnd_221810 < baseStart_221810 := by decide
  rcases family_descends (prefixWord ++ tailWord_221810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221878 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_221878 : Nat := 118140960795 + 221878 * 2 ^ 59
def prefixEnd_221878 : Nat := 4983230072969 + 3 ^ 40 * 221878 * 2
def baseEnd_221878 : Nat := 75953373772258756669739

theorem tailTrace_221878 : CollatzResearch.WordTrace tailWord_221878 prefixEnd_221878 75953373772258756669739 := by
  unfold tailWord_221878
  simp only [CollatzResearch.WordTrace]
  refine ⟨505784718136335911914643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5395036993454249727089525 505784718136335911914643)
  ·
    refine ⟨758677077204503867871965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 505784718136335911914643 758677077204503867871965)
    ·
      refine ⟨284503903951688950451987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 758677077204503867871965 284503903951688950451987)
      ·
        refine ⟨426755855927533425677981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284503903951688950451987 426755855927533425677981)
        ·
          refine ⟨160033445972825034629243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426755855927533425677981 160033445972825034629243)
          ·
            refine ⟨240050168959237551943865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160033445972825034629243 240050168959237551943865)
            ·
              refine ⟨180037626719428163957899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240050168959237551943865 180037626719428163957899)
              ·
                refine ⟨270056440079142245936849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180037626719428163957899 270056440079142245936849)
                ·
                  refine ⟨202542330059356684452637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270056440079142245936849 202542330059356684452637)
                  ·
                    refine ⟨75953373772258756669739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202542330059356684452637 75953373772258756669739)
                    ·
                      rfl

theorem cell22_221878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_221878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221878 prefixEnd_221878 := by exact prefixLift 221878
  have htrace : WordTrace (prefixWord ++ tailWord_221878) baseStart_221878 baseEnd_221878 := by
    simpa [prefixWord, tailWord_221878, baseEnd_221878] using wordTrace_append hprefix tailTrace_221878
  have hstable : (prefixWord ++ tailWord_221878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221878).length < 2 ^ (prefixWord ++ tailWord_221878).sum := by decide
  have hdescent : baseEnd_221878 < baseStart_221878 := by decide
  rcases family_descends (prefixWord ++ tailWord_221878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221881 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_221881 : Nat := 118140960795 + 221881 * 2 ^ 59
def prefixEnd_221881 : Nat := 4983230072969 + 3 ^ 40 * 221881 * 2
def baseEnd_221881 : Nat := 75954400733567748844729

theorem tailTrace_221881 : CollatzResearch.WordTrace tailWord_221881 prefixEnd_221881 75954400733567748844729 := by
  unfold tailWord_221881
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092664909170506102993497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5395109939447004068662331 8092664909170506102993497)
  ·
    refine ⟨6069498681877879577245123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8092664909170506102993497 6069498681877879577245123)
    ·
      refine ⟨9104248022816819365867685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6069498681877879577245123 9104248022816819365867685)
      ·
        refine ⟨1707046504278153631100191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9104248022816819365867685 1707046504278153631100191)
        ·
          refine ⟨2560569756417230446650287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707046504278153631100191 2560569756417230446650287)
          ·
            refine ⟨3840854634625845669975431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560569756417230446650287 3840854634625845669975431)
            ·
              refine ⟨5761281951938768504963147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840854634625845669975431 5761281951938768504963147)
              ·
                refine ⟨8641922927908152757444721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761281951938768504963147 8641922927908152757444721)
                ·
                  refine ⟨6481442195931114568083541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8641922927908152757444721 6481442195931114568083541)
                  ·
                    refine ⟨75954400733567748844729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6481442195931114568083541 75954400733567748844729)
                    ·
                      rfl

theorem cell22_221881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_221881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221881 prefixEnd_221881 := by exact prefixLift 221881
  have htrace : WordTrace (prefixWord ++ tailWord_221881) baseStart_221881 baseEnd_221881 := by
    simpa [prefixWord, tailWord_221881, baseEnd_221881] using wordTrace_append hprefix tailTrace_221881
  have hstable : (prefixWord ++ tailWord_221881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221881).length < 2 ^ (prefixWord ++ tailWord_221881).sum := by decide
  have hdescent : baseEnd_221881 < baseStart_221881 := by decide
  rcases family_descends (prefixWord ++ tailWord_221881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221885 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 5]
def baseStart_221885 : Nat := 118140960795 + 221885 * 2 ^ 59
def prefixEnd_221885 : Nat := 4983230072969 + 3 ^ 40 * 221885 * 2
def baseEnd_221885 : Nat := 25318590005104357248239

theorem tailTrace_221885 : CollatzResearch.WordTrace tailWord_221885 prefixEnd_221885 25318590005104357248239 := by
  unfold tailWord_221885
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092810801156014786139109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5395207200770676524092739 8092810801156014786139109)
  ·
    refine ⟨1517402025216752772401083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8092810801156014786139109 1517402025216752772401083)
    ·
      refine ⟨2276103037825129158601625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517402025216752772401083 2276103037825129158601625)
      ·
        refine ⟨1707077278368846868951219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2276103037825129158601625 1707077278368846868951219)
        ·
          refine ⟨2560615917553270303426829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707077278368846868951219 2560615917553270303426829)
          ·
            refine ⟨960230969082476363785061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2560615917553270303426829 960230969082476363785061)
            ·
              refine ⟨180043306702964318209699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 960230969082476363785061 180043306702964318209699)
              ·
                refine ⟨270064960054446477314549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180043306702964318209699 270064960054446477314549)
                ·
                  refine ⟨25318590005104357248239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270064960054446477314549 25318590005104357248239)
                  ·
                    rfl

theorem cell22_221885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_221885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221885 prefixEnd_221885 := by exact prefixLift 221885
  have htrace : WordTrace (prefixWord ++ tailWord_221885) baseStart_221885 baseEnd_221885 := by
    simpa [prefixWord, tailWord_221885, baseEnd_221885] using wordTrace_append hprefix tailTrace_221885
  have hstable : (prefixWord ++ tailWord_221885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221885).length < 2 ^ (prefixWord ++ tailWord_221885).sum := by decide
  have hdescent : baseEnd_221885 < baseStart_221885 := by decide
  rcases family_descends (prefixWord ++ tailWord_221885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221960 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_221960 : Nat := 118140960795 + 221960 * 2 ^ 59
def prefixEnd_221960 : Nat := 4983230072969 + 3 ^ 40 * 221960 * 2
def baseEnd_221960 : Nat := 75981444048037876119487

theorem tailTrace_221960 : CollatzResearch.WordTrace tailWord_221960 prefixEnd_221960 75981444048037876119487 := by
  unfold tailWord_221960
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047773137942151297559667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5397030850589535063412889 4047773137942151297559667)
  ·
    refine ⟨6071659706913226946339501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4047773137942151297559667 6071659706913226946339501)
    ·
      refine ⟨2276872390092460104877313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6071659706913226946339501 2276872390092460104877313)
      ·
        refine ⟨1707654292569345078657985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2276872390092460104877313 1707654292569345078657985)
        ·
          refine ⟨1280740719427008808993489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707654292569345078657985 1280740719427008808993489)
          ·
            refine ⟨960555539570256606745117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280740719427008808993489 960555539570256606745117)
            ·
              refine ⟨360208327338846227529419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960555539570256606745117 360208327338846227529419)
              ·
                refine ⟨540312491008269341294129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360208327338846227529419 540312491008269341294129)
                ·
                  refine ⟨405234368256202005970597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540312491008269341294129 405234368256202005970597)
                  ·
                    refine ⟨75981444048037876119487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405234368256202005970597 75981444048037876119487)
                    ·
                      rfl

theorem cell22_221960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_221960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_221960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_221960 prefixEnd_221960 := by exact prefixLift 221960
  have htrace : WordTrace (prefixWord ++ tailWord_221960) baseStart_221960 baseEnd_221960 := by
    simpa [prefixWord, tailWord_221960, baseEnd_221960] using wordTrace_append hprefix tailTrace_221960
  have hstable : (prefixWord ++ tailWord_221960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221960).length < 2 ^ (prefixWord ++ tailWord_221960).sum := by decide
  have hdescent : baseEnd_221960 < baseStart_221960 := by decide
  rcases family_descends (prefixWord ++ tailWord_221960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222063 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_222063 : Nat := 118140960795 + 222063 * 2 ^ 59
def prefixEnd_222063 : Nat := 4983230072969 + 3 ^ 40 * 222063 * 2
def baseEnd_222063 : Nat := 76016703052979940794171

theorem tailTrace_222063 : CollatzResearch.WordTrace tailWord_222063 prefixEnd_222063 76016703052979940794171 := by
  unfold tailWord_222063
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099302994511151186118843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5399535329674100790745895 8099302994511151186118843)
  ·
    refine ⟨12148954491766726779178265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8099302994511151186118843 12148954491766726779178265)
    ·
      refine ⟨9111715868825045084383699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12148954491766726779178265 9111715868825045084383699)
      ·
        refine ⟨13667573803237567626575549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9111715868825045084383699 13667573803237567626575549)
        ·
          refine ⟨5125340176214087859965831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13667573803237567626575549 5125340176214087859965831)
          ·
            refine ⟨7688010264321131789948747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125340176214087859965831 7688010264321131789948747)
            ·
              refine ⟨11532015396481697684923121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688010264321131789948747 11532015396481697684923121)
              ·
                refine ⟨8649011547361273263692341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11532015396481697684923121 8649011547361273263692341)
                ·
                  refine ⟨810844832565119368471157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8649011547361273263692341 810844832565119368471157)
                  ·
                    refine ⟨76016703052979940794171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 810844832565119368471157 76016703052979940794171)
                    ·
                      rfl

theorem cell22_222063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_222063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222063 prefixEnd_222063 := by exact prefixLift 222063
  have htrace : WordTrace (prefixWord ++ tailWord_222063) baseStart_222063 baseEnd_222063 := by
    simpa [prefixWord, tailWord_222063, baseEnd_222063] using wordTrace_append hprefix tailTrace_222063
  have hstable : (prefixWord ++ tailWord_222063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222063).length < 2 ^ (prefixWord ++ tailWord_222063).sum := by decide
  have hdescent : baseEnd_222063 < baseStart_222063 := by decide
  rcases family_descends (prefixWord ++ tailWord_222063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222080 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_222080 : Nat := 118140960795 + 222080 * 2 ^ 59
def prefixEnd_222080 : Nat := 4983230072969 + 3 ^ 40 * 222080 * 2
def baseEnd_222080 : Nat := 76022522500397563119119

theorem tailTrace_222080 : CollatzResearch.WordTrace tailWord_222080 prefixEnd_222080 76022522500397563119119 := by
  unfold tailWord_222080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049961517724781544743847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5399948690299708726325129 4049961517724781544743847)
  ·
    refine ⟨6074942276587172317115771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4049961517724781544743847 6074942276587172317115771)
    ·
      refine ⟨9112413414880758475673657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6074942276587172317115771 9112413414880758475673657)
      ·
        refine ⟨6834310061160568856755243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9112413414880758475673657 6834310061160568856755243)
        ·
          refine ⟨10251465091740853285132865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6834310061160568856755243 10251465091740853285132865)
          ·
            refine ⟨7688598818805639963849649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10251465091740853285132865 7688598818805639963849649)
            ·
              refine ⟨5766449114104229972887237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7688598818805639963849649 5766449114104229972887237)
              ·
                refine ⟨1081209208894543119916357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5766449114104229972887237 1081209208894543119916357)
                ·
                  refine ⟨202726726667726834984317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081209208894543119916357 202726726667726834984317)
                  ·
                    refine ⟨76022522500397563119119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202726726667726834984317 76022522500397563119119)
                    ·
                      rfl

theorem cell22_222080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_222080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222080 prefixEnd_222080 := by exact prefixLift 222080
  have htrace : WordTrace (prefixWord ++ tailWord_222080) baseStart_222080 baseEnd_222080 := by
    simpa [prefixWord, tailWord_222080, baseEnd_222080] using wordTrace_append hprefix tailTrace_222080
  have hstable : (prefixWord ++ tailWord_222080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222080).length < 2 ^ (prefixWord ++ tailWord_222080).sum := by decide
  have hdescent : baseEnd_222080 < baseStart_222080 := by decide
  rcases family_descends (prefixWord ++ tailWord_222080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222114 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_222114 : Nat := 118140960795 + 222114 * 2 ^ 59
def prefixEnd_222114 : Nat := 4983230072969 + 3 ^ 40 * 222114 * 2
def baseEnd_222114 : Nat := 76034161395232807769015

theorem tailTrace_222114 : CollatzResearch.WordTrace tailWord_222114 prefixEnd_222114 76034161395232807769015 := by
  unfold tailWord_222114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025290779331596724056349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5400775411550924597483597 2025290779331596724056349)
  ·
    refine ⟨759484042249348771521131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2025290779331596724056349 759484042249348771521131)
    ·
      refine ⟨1139226063374023157281697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759484042249348771521131 1139226063374023157281697)
      ·
        refine ⟨854419547530517367961273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139226063374023157281697 854419547530517367961273)
        ·
          refine ⟨640814660647888025970955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854419547530517367961273 640814660647888025970955)
          ·
            refine ⟨961221990971832038956433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640814660647888025970955 961221990971832038956433)
            ·
              refine ⟨720916493228874029217325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961221990971832038956433 720916493228874029217325)
              ·
                refine ⟨270343684960827760956497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 720916493228874029217325 270343684960827760956497)
                ·
                  refine ⟨202757763720620820717373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270343684960827760956497 202757763720620820717373)
                  ·
                    refine ⟨76034161395232807769015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202757763720620820717373 76034161395232807769015)
                    ·
                      rfl

theorem cell22_222114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_222114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222114 prefixEnd_222114 := by exact prefixLift 222114
  have htrace : WordTrace (prefixWord ++ tailWord_222114) baseStart_222114 baseEnd_222114 := by
    simpa [prefixWord, tailWord_222114, baseEnd_222114] using wordTrace_append hprefix tailTrace_222114
  have hstable : (prefixWord ++ tailWord_222114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222114).length < 2 ^ (prefixWord ++ tailWord_222114).sum := by decide
  have hdescent : baseEnd_222114 < baseStart_222114 := by decide
  rcases family_descends (prefixWord ++ tailWord_222114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222129 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_222129 : Nat := 118140960795 + 222129 * 2 ^ 59
def prefixEnd_222129 : Nat := 4983230072969 + 3 ^ 40 * 222129 * 2
def baseEnd_222129 : Nat := 76039296201777768643969

theorem tailTrace_222129 : CollatzResearch.WordTrace tailWord_222129 prefixEnd_222129 76039296201777768643969 := by
  unfold tailWord_222129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8101710212272044458021441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5401140141514696305347627 8101710212272044458021441)
  ·
    refine ⟨6076282659204033343516081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8101710212272044458021441 6076282659204033343516081)
    ·
      refine ⟨4557211994403025007637061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6076282659204033343516081 4557211994403025007637061)
      ·
        refine ⟨854477248950567188931949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4557211994403025007637061 854477248950567188931949)
        ·
          refine ⟨320428968356462695849481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 854477248950567188931949 320428968356462695849481)
          ·
            refine ⟨240321726267347021887111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320428968356462695849481 240321726267347021887111)
            ·
              refine ⟨360482589401020532830667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240321726267347021887111 360482589401020532830667)
              ·
                refine ⟨540723884101530799246001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360482589401020532830667 540723884101530799246001)
                ·
                  refine ⟨405542913076148099434501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540723884101530799246001 405542913076148099434501)
                  ·
                    refine ⟨76039296201777768643969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405542913076148099434501 76039296201777768643969)
                    ·
                      rfl

theorem cell22_222129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_222129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222129 prefixEnd_222129 := by exact prefixLift 222129
  have htrace : WordTrace (prefixWord ++ tailWord_222129) baseStart_222129 baseEnd_222129 := by
    simpa [prefixWord, tailWord_222129, baseEnd_222129] using wordTrace_append hprefix tailTrace_222129
  have hstable : (prefixWord ++ tailWord_222129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222129).length < 2 ^ (prefixWord ++ tailWord_222129).sum := by decide
  have hdescent : baseEnd_222129 < baseStart_222129 := by decide
  rcases family_descends (prefixWord ++ tailWord_222129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222142 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_222142 : Nat := 118140960795 + 222142 * 2 ^ 59
def prefixEnd_222142 : Nat := 4983230072969 + 3 ^ 40 * 222142 * 2
def baseEnd_222142 : Nat := 76043746367450068068929

theorem tailTrace_222142 : CollatzResearch.WordTrace tailWord_222142 prefixEnd_222142 76043746367450068068929 := by
  unfold tailWord_222142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012773045153118459780585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5401456240816631785496453 1012773045153118459780585)
  ·
    refine ⟨759579783864838844835439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1012773045153118459780585 759579783864838844835439)
    ·
      refine ⟨1139369675797258267253159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759579783864838844835439 1139369675797258267253159)
      ·
        refine ⟨1709054513695887400879739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139369675797258267253159 1709054513695887400879739)
        ·
          refine ⟨2563581770543831101319609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709054513695887400879739 2563581770543831101319609)
          ·
            refine ⟨1922686327907873325989707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2563581770543831101319609 1922686327907873325989707)
            ·
              refine ⟨2884029491861809988984561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922686327907873325989707 2884029491861809988984561)
              ·
                refine ⟨2163022118896357491738421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884029491861809988984561 2163022118896357491738421)
                ·
                  refine ⟨202783323646533514850477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2163022118896357491738421 202783323646533514850477)
                  ·
                    refine ⟨76043746367450068068929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202783323646533514850477 76043746367450068068929)
                    ·
                      rfl

theorem cell22_222142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_222142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222142 prefixEnd_222142 := by exact prefixLift 222142
  have htrace : WordTrace (prefixWord ++ tailWord_222142) baseStart_222142 baseEnd_222142 := by
    simpa [prefixWord, tailWord_222142, baseEnd_222142] using wordTrace_append hprefix tailTrace_222142
  have hstable : (prefixWord ++ tailWord_222142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222142).length < 2 ^ (prefixWord ++ tailWord_222142).sum := by decide
  have hdescent : baseEnd_222142 < baseStart_222142 := by decide
  rcases family_descends (prefixWord ++ tailWord_222142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222148 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_222148 : Nat := 118140960795 + 222148 * 2 ^ 59
def prefixEnd_222148 : Nat := 4983230072969 + 3 ^ 40 * 222148 * 2
def baseEnd_222148 : Nat := 76045800290068052418911

theorem tailTrace_222148 : CollatzResearch.WordTrace tailWord_222148 prefixEnd_222148 76045800290068052418911 := by
  unfold tailWord_222148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051201599601605351481549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5401602132802140468642065 4051201599601605351481549)
  ·
    refine ⟨1519200599850602006805581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4051201599601605351481549 1519200599850602006805581)
    ·
      refine ⟨569700224943975752552093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1519200599850602006805581 569700224943975752552093)
      ·
        refine ⟨213637584353990907207035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569700224943975752552093 213637584353990907207035)
        ·
          refine ⟨320456376530986360810553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213637584353990907207035 320456376530986360810553)
          ·
            refine ⟨240342282398239770607915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320456376530986360810553 240342282398239770607915)
            ·
              refine ⟨360513423597359655911873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240342282398239770607915 360513423597359655911873)
              ·
                refine ⟨270385067698019741933905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360513423597359655911873 270385067698019741933905)
                ·
                  refine ⟨202788800773514806450429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270385067698019741933905 202788800773514806450429)
                  ·
                    refine ⟨76045800290068052418911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202788800773514806450429 76045800290068052418911)
                    ·
                      rfl

theorem cell22_222148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_222148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222148 prefixEnd_222148 := by exact prefixLift 222148
  have htrace : WordTrace (prefixWord ++ tailWord_222148) baseStart_222148 baseEnd_222148 := by
    simpa [prefixWord, tailWord_222148, baseEnd_222148] using wordTrace_append hprefix tailTrace_222148
  have hstable : (prefixWord ++ tailWord_222148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222148).length < 2 ^ (prefixWord ++ tailWord_222148).sum := by decide
  have hdescent : baseEnd_222148 < baseStart_222148 := by decide
  rcases family_descends (prefixWord ++ tailWord_222148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222155 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 7]
def baseStart_222155 : Nat := 118140960795 + 222155 * 2 ^ 59
def prefixEnd_222155 : Nat := 4983230072969 + 3 ^ 40 * 222155 * 2
def baseEnd_222155 : Nat := 25349398844374122497963

theorem tailTrace_222155 : CollatzResearch.WordTrace tailWord_222155 prefixEnd_222155 25349398844374122497963 := by
  unfold tailWord_222155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8102658510177850898467919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5401772340118567265645279 8102658510177850898467919)
  ·
    refine ⟨12153987765266776347701879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8102658510177850898467919 12153987765266776347701879)
    ·
      refine ⟨18230981647900164521552819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12153987765266776347701879 18230981647900164521552819)
      ·
        refine ⟨27346472471850246782329229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18230981647900164521552819 27346472471850246782329229)
        ·
          refine ⟨10254927176943842543373461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27346472471850246782329229 10254927176943842543373461)
          ·
            refine ⟨480699711419242619220631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10254927176943842543373461 480699711419242619220631)
            ·
              refine ⟨721049567128863928830947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480699711419242619220631 721049567128863928830947)
              ·
                refine ⟨1081574350693295893246421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721049567128863928830947 1081574350693295893246421)
                ·
                  refine ⟨25349398844374122497963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1081574350693295893246421 25349398844374122497963)
                  ·
                    rfl

theorem cell22_222155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_222155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222155 prefixEnd_222155 := by exact prefixLift 222155
  have htrace : WordTrace (prefixWord ++ tailWord_222155) baseStart_222155 baseEnd_222155 := by
    simpa [prefixWord, tailWord_222155, baseEnd_222155] using wordTrace_append hprefix tailTrace_222155
  have hstable : (prefixWord ++ tailWord_222155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222155).length < 2 ^ (prefixWord ++ tailWord_222155).sum := by decide
  have hdescent : baseEnd_222155 < baseStart_222155 := by decide
  rcases family_descends (prefixWord ++ tailWord_222155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222159 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 1, 3]
def baseStart_222159 : Nat := 118140960795 + 222159 * 2 ^ 59
def prefixEnd_222159 : Nat := 4983230072969 + 3 ^ 40 * 222159 * 2
def baseEnd_222159 : Nat := 76049565814867690393877

theorem tailTrace_222159 : CollatzResearch.WordTrace tailWord_222159 prefixEnd_222159 76049565814867690393877 := by
  unfold tailWord_222159
  simp only [CollatzResearch.WordTrace]
  refine ⟨8102804402163359581613531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5401869601442239721075687 8102804402163359581613531)
  ·
    refine ⟨12154206603245039372420297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8102804402163359581613531 12154206603245039372420297)
    ·
      refine ⟨9115654952433779529315223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12154206603245039372420297 9115654952433779529315223)
      ·
        refine ⟨13673482428650669293972835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115654952433779529315223 13673482428650669293972835)
        ·
          refine ⟨20510223642976003940959253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13673482428650669293972835 20510223642976003940959253)
          ·
            refine ⟨961416733264500184732465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20510223642976003940959253 961416733264500184732465)
            ·
              refine ⟨721062549948375138549349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961416733264500184732465 721062549948375138549349)
              ·
                refine ⟨135199228115320338478003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 721062549948375138549349 135199228115320338478003)
                ·
                  refine ⟨202798842172980507717005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135199228115320338478003 202798842172980507717005)
                  ·
                    refine ⟨76049565814867690393877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202798842172980507717005 76049565814867690393877)
                    ·
                      rfl

theorem cell22_222159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_222159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222159 prefixEnd_222159 := by exact prefixLift 222159
  have htrace : WordTrace (prefixWord ++ tailWord_222159) baseStart_222159 baseEnd_222159 := by
    simpa [prefixWord, tailWord_222159, baseEnd_222159] using wordTrace_append hprefix tailTrace_222159
  have hstable : (prefixWord ++ tailWord_222159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222159).length < 2 ^ (prefixWord ++ tailWord_222159).sum := by decide
  have hdescent : baseEnd_222159 < baseStart_222159 := by decide
  rcases family_descends (prefixWord ++ tailWord_222159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222210 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_222210 : Nat := 118140960795 + 222210 * 2 ^ 59
def prefixEnd_222210 : Nat := 4983230072969 + 3 ^ 40 * 222210 * 2
def baseEnd_222210 : Nat := 76067024157120557368721

theorem tailTrace_222210 : CollatzResearch.WordTrace tailWord_222210 prefixEnd_222210 76067024157120557368721 := by
  unfold tailWord_222210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026166131244648822930021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5403109683319063527813389 2026166131244648822930021)
  ·
    refine ⟨379906149608371654299379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2026166131244648822930021 379906149608371654299379)
    ·
      refine ⟨569859224412557481449069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379906149608371654299379 569859224412557481449069)
      ·
        refine ⟨213697209154709055543401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569859224412557481449069 213697209154709055543401)
        ·
          refine ⟨160272906866031791657551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213697209154709055543401 160272906866031791657551)
          ·
            refine ⟨240409360299047687486327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160272906866031791657551 240409360299047687486327)
            ·
              refine ⟨360614040448571531229491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240409360299047687486327 360614040448571531229491)
              ·
                refine ⟨540921060672857296844237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360614040448571531229491 540921060672857296844237)
                ·
                  refine ⟨202845397752321486316589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540921060672857296844237 202845397752321486316589)
                  ·
                    refine ⟨76067024157120557368721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202845397752321486316589 76067024157120557368721)
                    ·
                      rfl

theorem cell22_222210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_222210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222210 prefixEnd_222210 := by exact prefixLift 222210
  have htrace : WordTrace (prefixWord ++ tailWord_222210) baseStart_222210 baseEnd_222210 := by
    simpa [prefixWord, tailWord_222210, baseEnd_222210] using wordTrace_append hprefix tailTrace_222210
  have hstable : (prefixWord ++ tailWord_222210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222210).length < 2 ^ (prefixWord ++ tailWord_222210).sum := by decide
  have hdescent : baseEnd_222210 < baseStart_222210 := by decide
  rcases family_descends (prefixWord ++ tailWord_222210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222217 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 4]
def baseStart_222217 : Nat := 118140960795 + 222217 * 2 ^ 59
def prefixEnd_222217 : Nat := 4983230072969 + 3 ^ 40 * 222217 * 2
def baseEnd_222217 : Nat := 25356473466724957481233

theorem tailTrace_222217 : CollatzResearch.WordTrace tailWord_222217 prefixEnd_222217 25356473466724957481233 := by
  unfold tailWord_222217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104919835953235487224905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5403279890635490324816603 8104919835953235487224905)
  ·
    refine ⟨6078689876964926615418679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8104919835953235487224905 6078689876964926615418679)
    ·
      refine ⟨9118034815447389923128019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6078689876964926615418679 9118034815447389923128019)
      ·
        refine ⟨13677052223171084884692029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118034815447389923128019 13677052223171084884692029)
        ·
          refine ⟨5128894583689156831759511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13677052223171084884692029 5128894583689156831759511)
          ·
            refine ⟨7693341875533735247639267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128894583689156831759511 7693341875533735247639267)
            ·
              refine ⟨11540012813300602871458901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693341875533735247639267 11540012813300602871458901)
              ·
                refine ⟨135234525155866439899909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11540012813300602871458901 135234525155866439899909)
                ·
                  refine ⟨25356473466724957481233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135234525155866439899909 25356473466724957481233)
                  ·
                    rfl

theorem cell22_222217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_222217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222217 prefixEnd_222217 := by exact prefixLift 222217
  have htrace : WordTrace (prefixWord ++ tailWord_222217) baseStart_222217 baseEnd_222217 := by
    simpa [prefixWord, tailWord_222217, baseEnd_222217] using wordTrace_append hprefix tailTrace_222217
  have hstable : (prefixWord ++ tailWord_222217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222217).length < 2 ^ (prefixWord ++ tailWord_222217).sum := by decide
  have hdescent : baseEnd_222217 < baseStart_222217 := by decide
  rcases family_descends (prefixWord ++ tailWord_222217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
