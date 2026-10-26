import V185TrunkScan23Chunk0003

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_22757 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 2, 2, 2]
def baseStart_22757 : Nat := 118140960795 + 22757 * 2 ^ 59
def prefixEnd_22757 : Nat := 4983230072969 + 3 ^ 40 * 22757 * 2
def baseEnd_22757 : Nat := 11685279254472696832849

theorem tailTrace_22757 : CollatzResearch.WordTrace tailWord_22757 prefixEnd_22757 11685279254472696832849 := by
  unfold tailWord_22757
  simp only [CollatzResearch.WordTrace]
  refine ⟨830015978562750431282525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 553343985708500287521683 830015978562750431282525)
  ·
    refine ⟨311255991961031411730947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 830015978562750431282525 311255991961031411730947)
    ·
      refine ⟨466883987941547117596421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311255991961031411730947 466883987941547117596421)
      ·
        refine ⟨87540747739040084549329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 466883987941547117596421 87540747739040084549329)
        ·
          refine ⟨65655560804280063411997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87540747739040084549329 65655560804280063411997)
          ·
            refine ⟨24620835301605023779499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65655560804280063411997 24620835301605023779499)
            ·
              refine ⟨36931252952407535669249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24620835301605023779499 36931252952407535669249)
              ·
                refine ⟨27698439714305651751937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36931252952407535669249 27698439714305651751937)
                ·
                  refine ⟨20773829785729238813953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27698439714305651751937 20773829785729238813953)
                  ·
                    refine ⟨15580372339296929110465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20773829785729238813953 15580372339296929110465)
                    ·
                      refine ⟨11685279254472696832849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15580372339296929110465 11685279254472696832849)
                      ·
                        rfl

theorem cell23_22757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_22757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22757 prefixEnd_22757 := by exact prefixLift 22757
  have htrace : WordTrace (prefixWord ++ tailWord_22757) baseStart_22757 baseEnd_22757 := by
    simpa [prefixWord, tailWord_22757, baseEnd_22757] using wordTrace_append hprefix tailTrace_22757
  have hstable : (prefixWord ++ tailWord_22757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22757).length < 2 ^ (prefixWord ++ tailWord_22757).sum := by decide
  have hdescent : baseEnd_22757 < baseStart_22757 := by decide
  rcases family_descends (prefixWord ++ tailWord_22757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22769 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_22769 : Nat := 118140960795 + 22769 * 2 ^ 59
def prefixEnd_22769 : Nat := 4983230072969 + 3 ^ 40 * 22769 * 2
def baseEnd_22769 : Nat := 11691441022326649882793

theorem tailTrace_22769 : CollatzResearch.WordTrace tailWord_22769 prefixEnd_22769 11691441022326649882793 := by
  unfold tailWord_22769
  simp only [CollatzResearch.WordTrace]
  refine ⟨830453654519276480719361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 553635769679517653812907 830453654519276480719361)
  ·
    refine ⟨622840240889457360539521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 830453654519276480719361 622840240889457360539521)
    ·
      refine ⟨467130180667093020404641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622840240889457360539521 467130180667093020404641)
      ·
        refine ⟨350347635500319765303481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467130180667093020404641 350347635500319765303481)
        ·
          refine ⟨262760726625239823977611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350347635500319765303481 262760726625239823977611)
          ·
            refine ⟨394141089937859735966417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262760726625239823977611 394141089937859735966417)
            ·
              refine ⟨295605817453394801974813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394141089937859735966417 295605817453394801974813)
              ·
                refine ⟨110852181545023050740555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295605817453394801974813 110852181545023050740555)
                ·
                  refine ⟨166278272317534576110833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110852181545023050740555 166278272317534576110833)
                  ·
                    refine ⟨124708704238150932083125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166278272317534576110833 124708704238150932083125)
                    ·
                      refine ⟨11691441022326649882793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 124708704238150932083125 11691441022326649882793)
                      ·
                        rfl

theorem cell23_22769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_22769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22769 prefixEnd_22769 := by exact prefixLift 22769
  have htrace : WordTrace (prefixWord ++ tailWord_22769) baseStart_22769 baseEnd_22769 := by
    simpa [prefixWord, tailWord_22769, baseEnd_22769] using wordTrace_append hprefix tailTrace_22769
  have hstable : (prefixWord ++ tailWord_22769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22769).length < 2 ^ (prefixWord ++ tailWord_22769).sum := by decide
  have hdescent : baseEnd_22769 < baseStart_22769 := by decide
  rcases family_descends (prefixWord ++ tailWord_22769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22796 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_22796 : Nat := 118140960795 + 22796 * 2 ^ 59
def prefixEnd_22796 : Nat := 4983230072969 + 3 ^ 40 * 22796 * 2
def baseEnd_22796 : Nat := 11705304999998044245169

theorem tailTrace_22796 : CollatzResearch.WordTrace tailWord_22796 prefixEnd_22796 11705304999998044245169 := by
  unfold tailWord_22796
  simp only [CollatzResearch.WordTrace]
  refine ⟨415719212710730045976121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 554292283614306727968161 415719212710730045976121)
  ·
    refine ⟨311789409533047534482091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 415719212710730045976121 311789409533047534482091)
    ·
      refine ⟨467684114299571301723137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311789409533047534482091 467684114299571301723137)
      ·
        refine ⟨350763085724678476292353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467684114299571301723137 350763085724678476292353)
        ·
          refine ⟨263072314293508857219265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350763085724678476292353 263072314293508857219265)
          ·
            refine ⟨197304235720131642914449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263072314293508857219265 197304235720131642914449)
            ·
              refine ⟨147978176790098732185837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197304235720131642914449 147978176790098732185837)
              ·
                refine ⟨55491816296287024569689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147978176790098732185837 55491816296287024569689)
                ·
                  refine ⟨41618862222215268427267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55491816296287024569689 41618862222215268427267)
                  ·
                    refine ⟨62428293333322902640901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41618862222215268427267 62428293333322902640901)
                    ·
                      refine ⟨11705304999998044245169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 62428293333322902640901 11705304999998044245169)
                      ·
                        rfl

theorem cell23_22796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_22796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22796 prefixEnd_22796 := by exact prefixLift 22796
  have htrace : WordTrace (prefixWord ++ tailWord_22796) baseStart_22796 baseEnd_22796 := by
    simpa [prefixWord, tailWord_22796, baseEnd_22796] using wordTrace_append hprefix tailTrace_22796
  have hstable : (prefixWord ++ tailWord_22796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22796).length < 2 ^ (prefixWord ++ tailWord_22796).sum := by decide
  have hdescent : baseEnd_22796 < baseStart_22796 := by decide
  rcases family_descends (prefixWord ++ tailWord_22796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22819 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 8]
def baseStart_22819 : Nat := 118140960795 + 22819 * 2 ^ 59
def prefixEnd_22819 : Nat := 4983230072969 + 3 ^ 40 * 22819 * 2
def baseEnd_22819 : Nat := 1301901672783494917507

theorem tailTrace_22819 : CollatzResearch.WordTrace tailWord_22819 prefixEnd_22819 1301901672783494917507 := by
  unfold tailWord_22819
  simp only [CollatzResearch.WordTrace]
  refine ⟨832277304338135020039511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 554851536225423346693007 832277304338135020039511)
  ·
    refine ⟨1248415956507202530059267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832277304338135020039511 1248415956507202530059267)
    ·
      refine ⟨1872623934760803795088901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1248415956507202530059267 1872623934760803795088901)
      ·
        refine ⟨351116987767650711579169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1872623934760803795088901 351116987767650711579169)
        ·
          refine ⟨263337740825738033684377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351116987767650711579169 263337740825738033684377)
          ·
            refine ⟨197503305619303525263283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263337740825738033684377 197503305619303525263283)
            ·
              refine ⟨296254958428955287894925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197503305619303525263283 296254958428955287894925)
              ·
                refine ⟨111095609410858232960597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296254958428955287894925 111095609410858232960597)
                ·
                  refine ⟨1301901672783494917507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 111095609410858232960597 1301901672783494917507)
                  ·
                    rfl

theorem cell23_22819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 8].length) (baseStart_22819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22819 prefixEnd_22819 := by exact prefixLift 22819
  have htrace : WordTrace (prefixWord ++ tailWord_22819) baseStart_22819 baseEnd_22819 := by
    simpa [prefixWord, tailWord_22819, baseEnd_22819] using wordTrace_append hprefix tailTrace_22819
  have hstable : (prefixWord ++ tailWord_22819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22819).length < 2 ^ (prefixWord ++ tailWord_22819).sum := by decide
  have hdescent : baseEnd_22819 < baseStart_22819 := by decide
  rcases family_descends (prefixWord ++ tailWord_22819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22839 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_22839 : Nat := 118140960795 + 22839 * 2 ^ 59
def prefixEnd_22839 : Nat := 4983230072969 + 3 ^ 40 * 22839 * 2
def baseEnd_22839 : Nat := 11727384668141376007471

theorem tailTrace_22839 : CollatzResearch.WordTrace tailWord_22839 prefixEnd_22839 11727384668141376007471 := by
  unfold tailWord_22839
  simp only [CollatzResearch.WordTrace]
  refine ⟨833006764265678435767571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 555337842843785623845047 833006764265678435767571)
  ·
    refine ⟨1249510146398517653651357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833006764265678435767571 1249510146398517653651357)
    ·
      refine ⟨468566304899444120119259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1249510146398517653651357 468566304899444120119259)
      ·
        refine ⟨702849457349166180178889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468566304899444120119259 702849457349166180178889)
        ·
          refine ⟨527137093011874635134167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702849457349166180178889 527137093011874635134167)
          ·
            refine ⟨790705639517811952701251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527137093011874635134167 790705639517811952701251)
            ·
              refine ⟨1186058459276717929051877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790705639517811952701251 1186058459276717929051877)
              ·
                refine ⟨222385961114384611697227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1186058459276717929051877 222385961114384611697227)
                ·
                  refine ⟨333578941671576917545841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222385961114384611697227 333578941671576917545841)
                  ·
                    refine ⟨250184206253682688159381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333578941671576917545841 250184206253682688159381)
                    ·
                      refine ⟨11727384668141376007471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 250184206253682688159381 11727384668141376007471)
                      ·
                        rfl

theorem cell23_22839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_22839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22839 prefixEnd_22839 := by exact prefixLift 22839
  have htrace : WordTrace (prefixWord ++ tailWord_22839) baseStart_22839 baseEnd_22839 := by
    simpa [prefixWord, tailWord_22839, baseEnd_22839] using wordTrace_append hprefix tailTrace_22839
  have hstable : (prefixWord ++ tailWord_22839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22839).length < 2 ^ (prefixWord ++ tailWord_22839).sum := by decide
  have hdescent : baseEnd_22839 < baseStart_22839 := by decide
  rcases family_descends (prefixWord ++ tailWord_22839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22859 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_22859 : Nat := 118140960795 + 22859 * 2 ^ 59
def prefixEnd_22859 : Nat := 4983230072969 + 3 ^ 40 * 22859 * 2
def baseEnd_22859 : Nat := 11737654281231297757379

theorem tailTrace_22859 : CollatzResearch.WordTrace tailWord_22859 prefixEnd_22859 11737654281231297757379 := by
  unfold tailWord_22859
  simp only [CollatzResearch.WordTrace]
  refine ⟨833736224193221851495631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 555824149462147900997087 833736224193221851495631)
  ·
    refine ⟨1250604336289832777243447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833736224193221851495631 1250604336289832777243447)
    ·
      refine ⟨1875906504434749165865171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250604336289832777243447 1875906504434749165865171)
      ·
        refine ⟨2813859756652123748797757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875906504434749165865171 2813859756652123748797757)
        ·
          refine ⟨1055197408744546405799159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2813859756652123748797757 1055197408744546405799159)
          ·
            refine ⟨1582796113116819608698739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055197408744546405799159 1582796113116819608698739)
            ·
              refine ⟨2374194169675229413048109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582796113116819608698739 2374194169675229413048109)
              ·
                refine ⟨890322813628211029893041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2374194169675229413048109 890322813628211029893041)
                ·
                  refine ⟨667742110221158272419781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890322813628211029893041 667742110221158272419781)
                  ·
                    refine ⟨125201645666467176078709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667742110221158272419781 125201645666467176078709)
                    ·
                      refine ⟨11737654281231297757379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 125201645666467176078709 11737654281231297757379)
                      ·
                        rfl

theorem cell23_22859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_22859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22859 prefixEnd_22859 := by exact prefixLift 22859
  have htrace : WordTrace (prefixWord ++ tailWord_22859) baseStart_22859 baseEnd_22859 := by
    simpa [prefixWord, tailWord_22859, baseEnd_22859] using wordTrace_append hprefix tailTrace_22859
  have hstable : (prefixWord ++ tailWord_22859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22859).length < 2 ^ (prefixWord ++ tailWord_22859).sum := by decide
  have hdescent : baseEnd_22859 < baseStart_22859 := by decide
  rcases family_descends (prefixWord ++ tailWord_22859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22896 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_22896 : Nat := 118140960795 + 22896 * 2 ^ 59
def prefixEnd_22896 : Nat := 4983230072969 + 3 ^ 40 * 22896 * 2
def baseEnd_22896 : Nat := 3918884355149217664903

theorem tailTrace_22896 : CollatzResearch.WordTrace tailWord_22896 prefixEnd_22896 3918884355149217664903 := by
  unfold tailWord_22896
  simp only [CollatzResearch.WordTrace]
  refine ⟨417542862529588585296271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 556723816706118113728361 417542862529588585296271)
  ·
    refine ⟨626314293794382877944407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417542862529588585296271 626314293794382877944407)
    ·
      refine ⟨939471440691574316916611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626314293794382877944407 939471440691574316916611)
      ·
        refine ⟨1409207161037361475374917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939471440691574316916611 1409207161037361475374917)
        ·
          refine ⟨264226342694505276632797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1409207161037361475374917 264226342694505276632797)
          ·
            refine ⟨99084878510439478737299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264226342694505276632797 99084878510439478737299)
            ·
              refine ⟨148627317765659218105949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99084878510439478737299 148627317765659218105949)
              ·
                refine ⟨55735244162122206789731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148627317765659218105949 55735244162122206789731)
                ·
                  refine ⟨83602866243183310184597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55735244162122206789731 83602866243183310184597)
                  ·
                    refine ⟨3918884355149217664903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83602866243183310184597 3918884355149217664903)
                    ·
                      rfl

theorem cell23_22896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_22896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22896 prefixEnd_22896 := by exact prefixLift 22896
  have htrace : WordTrace (prefixWord ++ tailWord_22896) baseStart_22896 baseEnd_22896 := by
    simpa [prefixWord, tailWord_22896, baseEnd_22896] using wordTrace_append hprefix tailTrace_22896
  have hstable : (prefixWord ++ tailWord_22896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22896).length < 2 ^ (prefixWord ++ tailWord_22896).sum := by decide
  have hdescent : baseEnd_22896 < baseStart_22896 := by decide
  rcases family_descends (prefixWord ++ tailWord_22896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22913 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_22913 : Nat := 118140960795 + 22913 * 2 ^ 59
def prefixEnd_22913 : Nat := 4983230072969 + 3 ^ 40 * 22913 * 2
def baseEnd_22913 : Nat := 3921794078858028827377

theorem tailTrace_22913 : CollatzResearch.WordTrace tailWord_22913 prefixEnd_22913 3921794078858028827377 := by
  unfold tailWord_22913
  simp only [CollatzResearch.WordTrace]
  refine ⟨835705765997589073961393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 557137177331726049307595 835705765997589073961393)
  ·
    refine ⟨626779324498191805471045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 835705765997589073961393 626779324498191805471045)
    ·
      refine ⟨117521123343410963525821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 626779324498191805471045 117521123343410963525821)
      ·
        refine ⟨44070421253779111322183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117521123343410963525821 44070421253779111322183)
        ·
          refine ⟨66105631880668666983275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44070421253779111322183 66105631880668666983275)
          ·
            refine ⟨99158447821003000474913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66105631880668666983275 99158447821003000474913)
            ·
              refine ⟨74368835865752250356185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99158447821003000474913 74368835865752250356185)
              ·
                refine ⟨55776626899314187767139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74368835865752250356185 55776626899314187767139)
                ·
                  refine ⟨83664940348971281650709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55776626899314187767139 83664940348971281650709)
                  ·
                    refine ⟨3921794078858028827377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83664940348971281650709 3921794078858028827377)
                    ·
                      rfl

theorem cell23_22913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_22913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22913 prefixEnd_22913 := by exact prefixLift 22913
  have htrace : WordTrace (prefixWord ++ tailWord_22913) baseStart_22913 baseEnd_22913 := by
    simpa [prefixWord, tailWord_22913, baseEnd_22913] using wordTrace_append hprefix tailTrace_22913
  have hstable : (prefixWord ++ tailWord_22913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22913).length < 2 ^ (prefixWord ++ tailWord_22913).sum := by decide
  have hdescent : baseEnd_22913 < baseStart_22913 := by decide
  rcases family_descends (prefixWord ++ tailWord_22913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22920 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_22920 : Nat := 118140960795 + 22920 * 2 ^ 59
def prefixEnd_22920 : Nat := 4983230072969 + 3 ^ 40 * 22920 * 2
def baseEnd_22920 : Nat := 11768976601155559094599

theorem tailTrace_22920 : CollatzResearch.WordTrace tailWord_22920 prefixEnd_22920 11768976601155559094599 := by
  unfold tailWord_22920
  simp only [CollatzResearch.WordTrace]
  refine ⟨417980538486114634733107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 557307384648152846310809 417980538486114634733107)
  ·
    refine ⟨626970807729171952099661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417980538486114634733107 626970807729171952099661)
    ·
      refine ⟨235114052898439482037373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 626970807729171952099661 235114052898439482037373)
      ·
        refine ⟨88167769836914805764015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235114052898439482037373 88167769836914805764015)
        ·
          refine ⟨132251654755372208646023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88167769836914805764015 132251654755372208646023)
          ·
            refine ⟨198377482133058312969035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132251654755372208646023 198377482133058312969035)
            ·
              refine ⟨297566223199587469453553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198377482133058312969035 297566223199587469453553)
              ·
                refine ⟨223174667399690602090165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297566223199587469453553 223174667399690602090165)
                ·
                  refine ⟨20922625068720993945953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223174667399690602090165 20922625068720993945953)
                  ·
                    refine ⟨15691968801540745459465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20922625068720993945953 15691968801540745459465)
                    ·
                      refine ⟨11768976601155559094599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15691968801540745459465 11768976601155559094599)
                      ·
                        rfl

theorem cell23_22920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_22920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22920 prefixEnd_22920 := by exact prefixLift 22920
  have htrace : WordTrace (prefixWord ++ tailWord_22920) baseStart_22920 baseEnd_22920 := by
    simpa [prefixWord, tailWord_22920, baseEnd_22920] using wordTrace_append hprefix tailTrace_22920
  have hstable : (prefixWord ++ tailWord_22920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22920).length < 2 ^ (prefixWord ++ tailWord_22920).sum := by decide
  have hdescent : baseEnd_22920 < baseStart_22920 := by decide
  rcases family_descends (prefixWord ++ tailWord_22920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22937 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 1, 2, 2]
def baseStart_22937 : Nat := 118140960795 + 22937 * 2 ^ 59
def prefixEnd_22937 : Nat := 4983230072969 + 3 ^ 40 * 22937 * 2
def baseEnd_22937 : Nat := 11777705772281992582021

theorem tailTrace_22937 : CollatzResearch.WordTrace tailWord_22937 prefixEnd_22937 11777705772281992582021 := by
  unfold tailWord_22937
  simp only [CollatzResearch.WordTrace]
  refine ⟨836581117910641172835065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 557720745273760781890043 836581117910641172835065)
  ·
    refine ⟨627435838432980879626299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 836581117910641172835065 627435838432980879626299)
    ·
      refine ⟨941153757649471319439449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627435838432980879626299 941153757649471319439449)
      ·
        refine ⟨705865318237103489579587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 941153757649471319439449 705865318237103489579587)
        ·
          refine ⟨1058797977355655234369381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705865318237103489579587 1058797977355655234369381)
          ·
            refine ⟨198524620754185356444259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1058797977355655234369381 198524620754185356444259)
            ·
              refine ⟨297786931131278034666389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198524620754185356444259 297786931131278034666389)
              ·
                refine ⟨13958762396778657874987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 297786931131278034666389 13958762396778657874987)
                ·
                  refine ⟨20938143595167986812481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13958762396778657874987 20938143595167986812481)
                  ·
                    refine ⟨15703607696375990109361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20938143595167986812481 15703607696375990109361)
                    ·
                      refine ⟨11777705772281992582021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15703607696375990109361 11777705772281992582021)
                      ·
                        rfl

theorem cell23_22937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_22937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22937 prefixEnd_22937 := by exact prefixLift 22937
  have htrace : WordTrace (prefixWord ++ tailWord_22937) baseStart_22937 baseEnd_22937 := by
    simpa [prefixWord, tailWord_22937, baseEnd_22937] using wordTrace_append hprefix tailTrace_22937
  have hstable : (prefixWord ++ tailWord_22937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22937).length < 2 ^ (prefixWord ++ tailWord_22937).sum := by decide
  have hdescent : baseEnd_22937 < baseStart_22937 := by decide
  rcases family_descends (prefixWord ++ tailWord_22937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22976 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_22976 : Nat := 118140960795 + 22976 * 2 ^ 59
def prefixEnd_22976 : Nat := 4983230072969 + 3 ^ 40 * 22976 * 2
def baseEnd_22976 : Nat := 11797731517807339994341

theorem tailTrace_22976 : CollatzResearch.WordTrace tailWord_22976 prefixEnd_22976 11797731517807339994341 := by
  unfold tailWord_22976
  simp only [CollatzResearch.WordTrace]
  refine ⟨419001782384675416752391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 558669043179567222336521 419001782384675416752391)
  ·
    refine ⟨628502673577013125128587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419001782384675416752391 628502673577013125128587)
    ·
      refine ⟨942754010365519687692881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628502673577013125128587 942754010365519687692881)
      ·
        refine ⟨707065507774139765769661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942754010365519687692881 707065507774139765769661)
        ·
          refine ⟨265149565415302412163623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 707065507774139765769661 265149565415302412163623)
          ·
            refine ⟨397724348122953618245435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265149565415302412163623 397724348122953618245435)
            ·
              refine ⟨596586522184430427368153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397724348122953618245435 596586522184430427368153)
              ·
                refine ⟨447439891638322820526115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596586522184430427368153 447439891638322820526115)
                ·
                  refine ⟨671159837457484230789173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447439891638322820526115 671159837457484230789173)
                  ·
                    refine ⟨62921234761639146636485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671159837457484230789173 62921234761639146636485)
                    ·
                      refine ⟨11797731517807339994341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 62921234761639146636485 11797731517807339994341)
                      ·
                        rfl

theorem cell23_22976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_22976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22976 prefixEnd_22976 := by exact prefixLift 22976
  have htrace : WordTrace (prefixWord ++ tailWord_22976) baseStart_22976 baseEnd_22976 := by
    simpa [prefixWord, tailWord_22976, baseEnd_22976] using wordTrace_append hprefix tailTrace_22976
  have hstable : (prefixWord ++ tailWord_22976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22976).length < 2 ^ (prefixWord ++ tailWord_22976).sum := by decide
  have hdescent : baseEnd_22976 < baseStart_22976 := by decide
  rcases family_descends (prefixWord ++ tailWord_22976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22977 : List Nat := [1, 2, 7, 1, 1, 2, 9]
def baseStart_22977 : Nat := 118140960795 + 22977 * 2 ^ 59
def prefixEnd_22977 : Nat := 4983230072969 + 3 ^ 40 * 22977 * 2
def baseEnd_22977 : Nat := 145657345660022667677

theorem tailTrace_22977 : CollatzResearch.WordTrace tailWord_22977 prefixEnd_22977 145657345660022667677 := by
  unfold tailWord_22977
  simp only [CollatzResearch.WordTrace]
  refine ⟨838040037765728004291185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 558693358510485336194123 838040037765728004291185)
  ·
    refine ⟨628530028324296003218389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 838040037765728004291185 628530028324296003218389)
    ·
      refine ⟨14731172538850687575431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 628530028324296003218389 14731172538850687575431)
      ·
        refine ⟨22096758808276031363147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14731172538850687575431 22096758808276031363147)
        ·
          refine ⟨33145138212414047044721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22096758808276031363147 33145138212414047044721)
          ·
            refine ⟨24858853659310535283541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33145138212414047044721 24858853659310535283541)
            ·
              refine ⟨145657345660022667677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 24858853659310535283541 145657345660022667677)
              ·
                rfl

theorem cell23_22977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 9].length) (baseStart_22977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22977 prefixEnd_22977 := by exact prefixLift 22977
  have htrace : WordTrace (prefixWord ++ tailWord_22977) baseStart_22977 baseEnd_22977 := by
    simpa [prefixWord, tailWord_22977, baseEnd_22977] using wordTrace_append hprefix tailTrace_22977
  have hstable : (prefixWord ++ tailWord_22977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22977).length < 2 ^ (prefixWord ++ tailWord_22977).sum := by decide
  have hdescent : baseEnd_22977 < baseStart_22977 := by decide
  rcases family_descends (prefixWord ++ tailWord_22977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23043 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 3]
def baseStart_23043 : Nat := 118140960795 + 23043 * 2 ^ 59
def prefixEnd_23043 : Nat := 4983230072969 + 3 ^ 40 * 23043 * 2
def baseEnd_23043 : Nat := 11832134721658577856533

theorem tailTrace_23043 : CollatzResearch.WordTrace tailWord_23043 prefixEnd_23043 11832134721658577856533 := by
  unfold tailWord_23043
  simp only [CollatzResearch.WordTrace]
  refine ⟨840447255526621276193783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 560298170351080850795855 840447255526621276193783)
  ·
    refine ⟨1260670883289931914290675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840447255526621276193783 1260670883289931914290675)
    ·
      refine ⟨1891006324934897871436013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260670883289931914290675 1891006324934897871436013)
      ·
        refine ⟨709127371850586701788505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1891006324934897871436013 709127371850586701788505)
        ·
          refine ⟨531845528887940026341379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709127371850586701788505 531845528887940026341379)
          ·
            refine ⟨797768293331910039512069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531845528887940026341379 797768293331910039512069)
            ·
              refine ⟨149581554999733132408513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 797768293331910039512069 149581554999733132408513)
              ·
                refine ⟨112186166249799849306385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149581554999733132408513 112186166249799849306385)
                ·
                  refine ⟨84139624687349886979789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112186166249799849306385 84139624687349886979789)
                  ·
                    refine ⟨31552359257756207617421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84139624687349886979789 31552359257756207617421)
                    ·
                      refine ⟨11832134721658577856533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 31552359257756207617421 11832134721658577856533)
                      ·
                        rfl

theorem cell23_23043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_23043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23043 prefixEnd_23043 := by exact prefixLift 23043
  have htrace : WordTrace (prefixWord ++ tailWord_23043) baseStart_23043 baseEnd_23043 := by
    simpa [prefixWord, tailWord_23043, baseEnd_23043] using wordTrace_append hprefix tailTrace_23043
  have hstable : (prefixWord ++ tailWord_23043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23043).length < 2 ^ (prefixWord ++ tailWord_23043).sum := by decide
  have hdescent : baseEnd_23043 < baseStart_23043 := by decide
  rcases family_descends (prefixWord ++ tailWord_23043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23044 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_23044 : Nat := 118140960795 + 23044 * 2 ^ 59
def prefixEnd_23044 : Nat := 4983230072969 + 3 ^ 40 * 23044 * 2
def baseEnd_23044 : Nat := 11832648202313073944029

theorem tailTrace_23044 : CollatzResearch.WordTrace tailWord_23044 prefixEnd_23044 11832648202313073944029 := by
  unfold tailWord_23044
  simp only [CollatzResearch.WordTrace]
  refine ⟨420241864261499223490093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 560322485681998964653457 420241864261499223490093)
  ·
    refine ⟨157590699098062208808785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 420241864261499223490093 157590699098062208808785)
    ·
      refine ⟨118193024323546656606589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157590699098062208808785 118193024323546656606589)
      ·
        refine ⟨44322384121329996227471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118193024323546656606589 44322384121329996227471)
        ·
          refine ⟨66483576181994994341207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44322384121329996227471 66483576181994994341207)
          ·
            refine ⟨99725364272992491511811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66483576181994994341207 99725364272992491511811)
            ·
              refine ⟨149588046409488737267717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99725364272992491511811 149588046409488737267717)
              ·
                refine ⟨28047758701779138237697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149588046409488737267717 28047758701779138237697)
                ·
                  refine ⟨21035819026334353678273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28047758701779138237697 21035819026334353678273)
                  ·
                    refine ⟨15776864269750765258705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21035819026334353678273 15776864269750765258705)
                    ·
                      refine ⟨11832648202313073944029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15776864269750765258705 11832648202313073944029)
                      ·
                        rfl

theorem cell23_23044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_23044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23044 prefixEnd_23044 := by exact prefixLift 23044
  have htrace : WordTrace (prefixWord ++ tailWord_23044) baseStart_23044 baseEnd_23044 := by
    simpa [prefixWord, tailWord_23044, baseEnd_23044] using wordTrace_append hprefix tailTrace_23044
  have hstable : (prefixWord ++ tailWord_23044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23044).length < 2 ^ (prefixWord ++ tailWord_23044).sum := by decide
  have hdescent : baseEnd_23044 < baseStart_23044 := by decide
  rcases family_descends (prefixWord ++ tailWord_23044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23050 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_23050 : Nat := 118140960795 + 23050 * 2 ^ 59
def prefixEnd_23050 : Nat := 4983230072969 + 3 ^ 40 * 23050 * 2
def baseEnd_23050 : Nat := 1315081009582227829889

theorem tailTrace_23050 : CollatzResearch.WordTrace tailWord_23050 prefixEnd_23050 1315081009582227829889 := by
  unfold tailWord_23050
  simp only [CollatzResearch.WordTrace]
  refine ⟨210175641625315367924651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 560468377667507647799069 210175641625315367924651)
  ·
    refine ⟨315263462437973051886977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210175641625315367924651 315263462437973051886977)
    ·
      refine ⟨236447596828479788915233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315263462437973051886977 236447596828479788915233)
      ·
        refine ⟨177335697621359841686425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236447596828479788915233 177335697621359841686425)
        ·
          refine ⟨133001773216019881264819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177335697621359841686425 133001773216019881264819)
          ·
            refine ⟨199502659824029821897229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133001773216019881264819 199502659824029821897229)
            ·
              refine ⟨74813497434011183211461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199502659824029821897229 74813497434011183211461)
              ·
                refine ⟨14027530768877096852149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74813497434011183211461 14027530768877096852149)
                ·
                  refine ⟨1315081009582227829889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14027530768877096852149 1315081009582227829889)
                  ·
                    rfl

theorem cell23_23050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_23050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23050 prefixEnd_23050 := by exact prefixLift 23050
  have htrace : WordTrace (prefixWord ++ tailWord_23050) baseStart_23050 baseEnd_23050 := by
    simpa [prefixWord, tailWord_23050, baseEnd_23050] using wordTrace_append hprefix tailTrace_23050
  have hstable : (prefixWord ++ tailWord_23050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23050).length < 2 ^ (prefixWord ++ tailWord_23050).sum := by decide
  have hdescent : baseEnd_23050 < baseStart_23050 := by decide
  rcases family_descends (prefixWord ++ tailWord_23050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23056 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_23056 : Nat := 118140960795 + 23056 * 2 ^ 59
def prefixEnd_23056 : Nat := 4983230072969 + 3 ^ 40 * 23056 * 2
def baseEnd_23056 : Nat := 11838809970167026993973

theorem tailTrace_23056 : CollatzResearch.WordTrace tailWord_23056 prefixEnd_23056 11838809970167026993973 := by
  unfold tailWord_23056
  simp only [CollatzResearch.WordTrace]
  refine ⟨420460702239762248208511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 560614269653016330944681 420460702239762248208511)
  ·
    refine ⟨630691053359643372312767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 420460702239762248208511 630691053359643372312767)
    ·
      refine ⟨946036580039465058469151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630691053359643372312767 946036580039465058469151)
      ·
        refine ⟨1419054870059197587703727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946036580039465058469151 1419054870059197587703727)
        ·
          refine ⟨2128582305088796381555591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419054870059197587703727 2128582305088796381555591)
          ·
            refine ⟨3192873457633194572333387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128582305088796381555591 3192873457633194572333387)
            ·
              refine ⟨4789310186449791858500081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192873457633194572333387 4789310186449791858500081)
              ·
                refine ⟨3591982639837343893875061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789310186449791858500081 3591982639837343893875061)
                ·
                  refine ⟨336748372484750990050787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3591982639837343893875061 336748372484750990050787)
                  ·
                    refine ⟨505122558727126485076181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336748372484750990050787 505122558727126485076181)
                    ·
                      refine ⟨11838809970167026993973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 505122558727126485076181 11838809970167026993973)
                      ·
                        rfl

theorem cell23_23056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_23056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23056 prefixEnd_23056 := by exact prefixLift 23056
  have htrace : WordTrace (prefixWord ++ tailWord_23056) baseStart_23056 baseEnd_23056 := by
    simpa [prefixWord, tailWord_23056, baseEnd_23056] using wordTrace_append hprefix tailTrace_23056
  have hstable : (prefixWord ++ tailWord_23056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23056).length < 2 ^ (prefixWord ++ tailWord_23056).sum := by decide
  have hdescent : baseEnd_23056 < baseStart_23056 := by decide
  rcases family_descends (prefixWord ++ tailWord_23056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23080 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_23080 : Nat := 118140960795 + 23080 * 2 ^ 59
def prefixEnd_23080 : Nat := 4983230072969 + 3 ^ 40 * 23080 * 2
def baseEnd_23080 : Nat := 3950377835291644364621

theorem tailTrace_23080 : CollatzResearch.WordTrace tailWord_23080 prefixEnd_23080 3950377835291644364621 := by
  unfold tailWord_23080
  simp only [CollatzResearch.WordTrace]
  refine ⟨420898378196288297645347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 561197837595051063527129 420898378196288297645347)
  ·
    refine ⟨631347567294432446468021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 420898378196288297645347 631347567294432446468021)
    ·
      refine ⟨59188834433853041856377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 631347567294432446468021 59188834433853041856377)
      ·
        refine ⟨44391625825389781392283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59188834433853041856377 44391625825389781392283)
        ·
          refine ⟨66587438738084672088425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44391625825389781392283 66587438738084672088425)
          ·
            refine ⟨49940579053563504066319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66587438738084672088425 49940579053563504066319)
            ·
              refine ⟨74910868580345256099479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49940579053563504066319 74910868580345256099479)
              ·
                refine ⟨112366302870517884149219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74910868580345256099479 112366302870517884149219)
                ·
                  refine ⟨168549454305776826223829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112366302870517884149219 168549454305776826223829)
                  ·
                    refine ⟨3950377835291644364621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168549454305776826223829 3950377835291644364621)
                    ·
                      rfl

theorem cell23_23080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_23080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23080 prefixEnd_23080 := by exact prefixLift 23080
  have htrace : WordTrace (prefixWord ++ tailWord_23080) baseStart_23080 baseEnd_23080 := by
    simpa [prefixWord, tailWord_23080, baseEnd_23080] using wordTrace_append hprefix tailTrace_23080
  have hstable : (prefixWord ++ tailWord_23080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23080).length < 2 ^ (prefixWord ++ tailWord_23080).sum := by decide
  have hdescent : baseEnd_23080 < baseStart_23080 := by decide
  rcases family_descends (prefixWord ++ tailWord_23080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23153 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_23153 : Nat := 118140960795 + 23153 * 2 ^ 59
def prefixEnd_23153 : Nat := 4983230072969 + 3 ^ 40 * 23153 * 2
def baseEnd_23153 : Nat := 3962872531217715827009

theorem tailTrace_23153 : CollatzResearch.WordTrace tailWord_23153 prefixEnd_23153 3962872531217715827009 := by
  unfold tailWord_23153
  simp only [CollatzResearch.WordTrace]
  refine ⟨844459285128110062698113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 562972856752073375132075 844459285128110062698113)
  ·
    refine ⟨633344463846082547023585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 844459285128110062698113 633344463846082547023585)
    ·
      refine ⟨475008347884561910267689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 633344463846082547023585 475008347884561910267689)
      ·
        refine ⟨356256260913421432700767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475008347884561910267689 356256260913421432700767)
        ·
          refine ⟨534384391370132149051151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356256260913421432700767 534384391370132149051151)
          ·
            refine ⟨801576587055198223576727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534384391370132149051151 801576587055198223576727)
            ·
              refine ⟨1202364880582797335365091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801576587055198223576727 1202364880582797335365091)
              ·
                refine ⟨1803547320874196003047637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202364880582797335365091 1803547320874196003047637)
                ·
                  refine ⟨42270640332988968821429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1803547320874196003047637 42270640332988968821429)
                  ·
                    refine ⟨3962872531217715827009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42270640332988968821429 3962872531217715827009)
                    ·
                      rfl

theorem cell23_23153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_23153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23153 prefixEnd_23153 := by exact prefixLift 23153
  have htrace : WordTrace (prefixWord ++ tailWord_23153) baseStart_23153 baseEnd_23153 := by
    simpa [prefixWord, tailWord_23153, baseEnd_23153] using wordTrace_append hprefix tailTrace_23153
  have hstable : (prefixWord ++ tailWord_23153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23153).length < 2 ^ (prefixWord ++ tailWord_23153).sum := by decide
  have hdescent : baseEnd_23153 < baseStart_23153 := by decide
  rcases family_descends (prefixWord ++ tailWord_23153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23203 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_23203 : Nat := 118140960795 + 23203 * 2 ^ 59
def prefixEnd_23203 : Nat := 4983230072969 + 3 ^ 40 * 23203 * 2
def baseEnd_23203 : Nat := 11914291626377951855797

theorem tailTrace_23203 : CollatzResearch.WordTrace tailWord_23203 prefixEnd_23203 11914291626377951855797 := by
  unfold tailWord_23203
  simp only [CollatzResearch.WordTrace]
  refine ⟨846282934946968602018263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 564188623297979068012175 846282934946968602018263)
  ·
    refine ⟨1269424402420452903027395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 846282934946968602018263 1269424402420452903027395)
    ·
      refine ⟨1904136603630679354541093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269424402420452903027395 1904136603630679354541093)
      ·
        refine ⟨357025613180752378976455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1904136603630679354541093 357025613180752378976455)
        ·
          refine ⟨535538419771128568464683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357025613180752378976455 535538419771128568464683)
          ·
            refine ⟨803307629656692852697025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535538419771128568464683 803307629656692852697025)
            ·
              refine ⟨602480722242519639522769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803307629656692852697025 602480722242519639522769)
              ·
                refine ⟨451860541681889729642077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602480722242519639522769 451860541681889729642077)
                ·
                  refine ⟨169447703130708648615779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451860541681889729642077 169447703130708648615779)
                  ·
                    refine ⟨254171554696062972923669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169447703130708648615779 254171554696062972923669)
                    ·
                      refine ⟨11914291626377951855797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 254171554696062972923669 11914291626377951855797)
                      ·
                        rfl

theorem cell23_23203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_23203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23203 prefixEnd_23203 := by exact prefixLift 23203
  have htrace : WordTrace (prefixWord ++ tailWord_23203) baseStart_23203 baseEnd_23203 := by
    simpa [prefixWord, tailWord_23203, baseEnd_23203] using wordTrace_append hprefix tailTrace_23203
  have hstable : (prefixWord ++ tailWord_23203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23203).length < 2 ^ (prefixWord ++ tailWord_23203).sum := by decide
  have hdescent : baseEnd_23203 < baseStart_23203 := by decide
  rcases family_descends (prefixWord ++ tailWord_23203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23245 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_23245 : Nat := 118140960795 + 23245 * 2 ^ 59
def prefixEnd_23245 : Nat := 4983230072969 + 3 ^ 40 * 23245 * 2
def baseEnd_23245 : Nat := 11935857813866787530605

theorem tailTrace_23245 : CollatzResearch.WordTrace tailWord_23245 prefixEnd_23245 11935857813866787530605 := by
  unfold tailWord_23245
  simp only [CollatzResearch.WordTrace]
  refine ⟨847814800794809775047189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 565209867196539850031459 847814800794809775047189)
  ·
    refine ⟨39741318787256708205337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 847814800794809775047189 39741318787256708205337)
    ·
      refine ⟨29805989090442531154003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39741318787256708205337 29805989090442531154003)
      ·
        refine ⟨44708983635663796731005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29805989090442531154003 44708983635663796731005)
        ·
          refine ⟨16765868863373923774127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44708983635663796731005 16765868863373923774127)
          ·
            refine ⟨25148803295060885661191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16765868863373923774127 25148803295060885661191)
            ·
              refine ⟨37723204942591328491787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25148803295060885661191 37723204942591328491787)
              ·
                refine ⟨56584807413886992737681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37723204942591328491787 56584807413886992737681)
                ·
                  refine ⟨42438605560415244553261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56584807413886992737681 42438605560415244553261)
                  ·
                    refine ⟨15914477085155716707473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42438605560415244553261 15914477085155716707473)
                    ·
                      refine ⟨11935857813866787530605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15914477085155716707473 11935857813866787530605)
                      ·
                        rfl

theorem cell23_23245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_23245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23245 prefixEnd_23245 := by exact prefixLift 23245
  have htrace : WordTrace (prefixWord ++ tailWord_23245) baseStart_23245 baseEnd_23245 := by
    simpa [prefixWord, tailWord_23245, baseEnd_23245] using wordTrace_append hprefix tailTrace_23245
  have hstable : (prefixWord ++ tailWord_23245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23245).length < 2 ^ (prefixWord ++ tailWord_23245).sum := by decide
  have hdescent : baseEnd_23245 < baseStart_23245 := by decide
  rcases family_descends (prefixWord ++ tailWord_23245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23257 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 3]
def baseStart_23257 : Nat := 118140960795 + 23257 * 2 ^ 59
def prefixEnd_23257 : Nat := 4983230072969 + 3 ^ 40 * 23257 * 2
def baseEnd_23257 : Nat := 11942019581720740580549

theorem tailTrace_23257 : CollatzResearch.WordTrace tailWord_23257 prefixEnd_23257 11942019581720740580549 := by
  unfold tailWord_23257
  simp only [CollatzResearch.WordTrace]
  refine ⟨848252476751335824484025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 565501651167557216322683 848252476751335824484025)
  ·
    refine ⟨636189357563501868363019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 848252476751335824484025 636189357563501868363019)
    ·
      refine ⟨954284036345252802544529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636189357563501868363019 954284036345252802544529)
      ·
        refine ⟨715713027258939601908397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954284036345252802544529 715713027258939601908397)
        ·
          refine ⟨268392385222102350715649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 715713027258939601908397 268392385222102350715649)
          ·
            refine ⟨201294288916576763036737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268392385222102350715649 201294288916576763036737)
            ·
              refine ⟨150970716687432572277553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201294288916576763036737 150970716687432572277553)
              ·
                refine ⟨113228037515574429208165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150970716687432572277553 113228037515574429208165)
                ·
                  refine ⟨21230257034170205476531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113228037515574429208165 21230257034170205476531)
                  ·
                    refine ⟨31845385551255308214797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21230257034170205476531 31845385551255308214797)
                    ·
                      refine ⟨11942019581720740580549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 31845385551255308214797 11942019581720740580549)
                      ·
                        rfl

theorem cell23_23257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_23257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23257 prefixEnd_23257 := by exact prefixLift 23257
  have htrace : WordTrace (prefixWord ++ tailWord_23257) baseStart_23257 baseEnd_23257 := by
    simpa [prefixWord, tailWord_23257, baseEnd_23257] using wordTrace_append hprefix tailTrace_23257
  have hstable : (prefixWord ++ tailWord_23257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23257).length < 2 ^ (prefixWord ++ tailWord_23257).sum := by decide
  have hdescent : baseEnd_23257 < baseStart_23257 := by decide
  rcases family_descends (prefixWord ++ tailWord_23257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23285 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_23285 : Nat := 118140960795 + 23285 * 2 ^ 59
def prefixEnd_23285 : Nat := 4983230072969 + 3 ^ 40 * 23285 * 2
def baseEnd_23285 : Nat := 3985465680015543676807

theorem tailTrace_23285 : CollatzResearch.WordTrace tailWord_23285 prefixEnd_23285 3985465680015543676807 := by
  unfold tailWord_23285
  simp only [CollatzResearch.WordTrace]
  refine ⟨849273720649896606503309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 566182480433264404335539 849273720649896606503309)
  ·
    refine ⟨318477645243711227438741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 849273720649896606503309 318477645243711227438741)
    ·
      refine ⟨14928639620798963786191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 318477645243711227438741 14928639620798963786191)
      ·
        refine ⟨22392959431198445679287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14928639620798963786191 22392959431198445679287)
        ·
          refine ⟨33589439146797668518931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22392959431198445679287 33589439146797668518931)
          ·
            refine ⟨50384158720196502778397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33589439146797668518931 50384158720196502778397)
            ·
              refine ⟨18894059520073688541899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50384158720196502778397 18894059520073688541899)
              ·
                refine ⟨28341089280110532812849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18894059520073688541899 28341089280110532812849)
                ·
                  refine ⟨21255816960082899609637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28341089280110532812849 21255816960082899609637)
                  ·
                    refine ⟨3985465680015543676807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21255816960082899609637 3985465680015543676807)
                    ·
                      rfl

theorem cell23_23285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_23285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23285 prefixEnd_23285 := by exact prefixLift 23285
  have htrace : WordTrace (prefixWord ++ tailWord_23285) baseStart_23285 baseEnd_23285 := by
    simpa [prefixWord, tailWord_23285, baseEnd_23285] using wordTrace_append hprefix tailTrace_23285
  have hstable : (prefixWord ++ tailWord_23285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23285).length < 2 ^ (prefixWord ++ tailWord_23285).sum := by decide
  have hdescent : baseEnd_23285 < baseStart_23285 := by decide
  rcases family_descends (prefixWord ++ tailWord_23285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23290 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_23290 : Nat := 118140960795 + 23290 * 2 ^ 59
def prefixEnd_23290 : Nat := 4983230072969 + 3 ^ 40 * 23290 * 2
def baseEnd_23290 : Nat := 3986321481106370489299

theorem tailTrace_23290 : CollatzResearch.WordTrace tailWord_23290 prefixEnd_23290 3986321481106370489299 := by
  unfold tailWord_23290
  simp only [CollatzResearch.WordTrace]
  refine ⟨212364021407945615108831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 566304057087854973623549 212364021407945615108831)
  ·
    refine ⟨318546032111918422663247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212364021407945615108831 318546032111918422663247)
    ·
      refine ⟨477819048167877633994871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318546032111918422663247 477819048167877633994871)
      ·
        refine ⟨716728572251816450992307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477819048167877633994871 716728572251816450992307)
        ·
          refine ⟨1075092858377724676488461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716728572251816450992307 1075092858377724676488461)
          ·
            refine ⟨403159821891646753683173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1075092858377724676488461 403159821891646753683173)
            ·
              refine ⟨75592466604683766315595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 403159821891646753683173 75592466604683766315595)
              ·
                refine ⟨113388699907025649473393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75592466604683766315595 113388699907025649473393)
                ·
                  refine ⟨85041524930269237105045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113388699907025649473393 85041524930269237105045)
                  ·
                    refine ⟨3986321481106370489299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85041524930269237105045 3986321481106370489299)
                    ·
                      rfl

theorem cell23_23290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_23290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23290 prefixEnd_23290 := by exact prefixLift 23290
  have htrace : WordTrace (prefixWord ++ tailWord_23290) baseStart_23290 baseEnd_23290 := by
    simpa [prefixWord, tailWord_23290, baseEnd_23290] using wordTrace_append hprefix tailTrace_23290
  have hstable : (prefixWord ++ tailWord_23290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23290).length < 2 ^ (prefixWord ++ tailWord_23290).sum := by decide
  have hdescent : baseEnd_23290 < baseStart_23290 := by decide
  rcases family_descends (prefixWord ++ tailWord_23290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23388 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 5]
def baseStart_23388 : Nat := 118140960795 + 23388 * 2 ^ 59
def prefixEnd_23388 : Nat := 4983230072969 + 3 ^ 40 * 23388 * 2
def baseEnd_23388 : Nat := 1334365060828858671383

theorem tailTrace_23388 : CollatzResearch.WordTrace tailWord_23388 prefixEnd_23388 1334365060828858671383 := by
  unfold tailWord_23388
  simp only [CollatzResearch.WordTrace]
  refine ⟨426515219638372598751409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 568686959517830131668545 426515219638372598751409)
  ·
    refine ⟨319886414728779449063557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 426515219638372598751409 319886414728779449063557)
    ·
      refine ⟨59978702761646146699417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319886414728779449063557 59978702761646146699417)
      ·
        refine ⟨44984027071234610024563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59978702761646146699417 44984027071234610024563)
        ·
          refine ⟨67476040606851915036845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44984027071234610024563 67476040606851915036845)
          ·
            refine ⟨25303515227569468138817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67476040606851915036845 25303515227569468138817)
            ·
              refine ⟨18977636420677101104113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25303515227569468138817 18977636420677101104113)
              ·
                refine ⟨14233227315507825828085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18977636420677101104113 14233227315507825828085)
                ·
                  refine ⟨1334365060828858671383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14233227315507825828085 1334365060828858671383)
                  ·
                    rfl

theorem cell23_23388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_23388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23388 prefixEnd_23388 := by exact prefixLift 23388
  have htrace : WordTrace (prefixWord ++ tailWord_23388) baseStart_23388 baseEnd_23388 := by
    simpa [prefixWord, tailWord_23388, baseEnd_23388] using wordTrace_append hprefix tailTrace_23388
  have hstable : (prefixWord ++ tailWord_23388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23388).length < 2 ^ (prefixWord ++ tailWord_23388).sum := by decide
  have hdescent : baseEnd_23388 < baseStart_23388 := by decide
  rcases family_descends (prefixWord ++ tailWord_23388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23404 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 2, 4, 2]
def baseStart_23404 : Nat := 118140960795 + 23404 * 2 ^ 59
def prefixEnd_23404 : Nat := 4983230072969 + 3 ^ 40 * 23404 * 2
def baseEnd_23404 : Nat := 12017501237931665442373

theorem tailTrace_23404 : CollatzResearch.WordTrace tailWord_23404 prefixEnd_23404 12017501237931665442373 := by
  unfold tailWord_23404
  simp only [CollatzResearch.WordTrace]
  refine ⟨426807003609389965042633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 569076004812519953390177 426807003609389965042633)
  ·
    refine ⟨320105252707042473781975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 426807003609389965042633 320105252707042473781975)
    ·
      refine ⟨480157879060563710672963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320105252707042473781975 480157879060563710672963)
      ·
        refine ⟨720236818590845566009445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480157879060563710672963 720236818590845566009445)
        ·
          refine ⟨135044403485783543626771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 720236818590845566009445 135044403485783543626771)
          ·
            refine ⟨202566605228675315440157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135044403485783543626771 202566605228675315440157)
            ·
              refine ⟨75962476960753243290059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202566605228675315440157 75962476960753243290059)
              ·
                refine ⟨113943715441129864935089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75962476960753243290059 113943715441129864935089)
                ·
                  refine ⟨85457786580847398701317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113943715441129864935089 85457786580847398701317)
                  ·
                    refine ⟨16023334983908887256497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85457786580847398701317 16023334983908887256497)
                    ·
                      refine ⟨12017501237931665442373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16023334983908887256497 12017501237931665442373)
                      ·
                        rfl

theorem cell23_23404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_23404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23404 prefixEnd_23404 := by exact prefixLift 23404
  have htrace : WordTrace (prefixWord ++ tailWord_23404) baseStart_23404 baseEnd_23404 := by
    simpa [prefixWord, tailWord_23404, baseEnd_23404] using wordTrace_append hprefix tailTrace_23404
  have hstable : (prefixWord ++ tailWord_23404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23404).length < 2 ^ (prefixWord ++ tailWord_23404).sum := by decide
  have hdescent : baseEnd_23404 < baseStart_23404 := by decide
  rcases family_descends (prefixWord ++ tailWord_23404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23407 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_23407 : Nat := 118140960795 + 23407 * 2 ^ 59
def prefixEnd_23407 : Nat := 4983230072969 + 3 ^ 40 * 23407 * 2
def baseEnd_23407 : Nat := 12019041679895153704859

theorem tailTrace_23407 : CollatzResearch.WordTrace tailWord_23407 prefixEnd_23407 12019041679895153704859 := by
  unfold tailWord_23407
  simp only [CollatzResearch.WordTrace]
  refine ⟨853723426207911442444475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 569148950805274294962983 853723426207911442444475)
  ·
    refine ⟨1280585139311867163666713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853723426207911442444475 1280585139311867163666713)
    ·
      refine ⟨960438854483900372750035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1280585139311867163666713 960438854483900372750035)
      ·
        refine ⟨1440658281725850559125053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960438854483900372750035 1440658281725850559125053)
        ·
          refine ⟨540246855647193959671895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1440658281725850559125053 540246855647193959671895)
          ·
            refine ⟨810370283470790939507843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540246855647193959671895 810370283470790939507843)
            ·
              refine ⟨1215555425206186409261765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810370283470790939507843 1215555425206186409261765)
              ·
                refine ⟨227916642226159951736581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1215555425206186409261765 227916642226159951736581)
                ·
                  refine ⟨42734370417404990950609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227916642226159951736581 42734370417404990950609)
                  ·
                    refine ⟨32050777813053743212957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42734370417404990950609 32050777813053743212957)
                    ·
                      refine ⟨12019041679895153704859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 32050777813053743212957 12019041679895153704859)
                      ·
                        rfl

theorem cell23_23407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_23407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23407 prefixEnd_23407 := by exact prefixLift 23407
  have htrace : WordTrace (prefixWord ++ tailWord_23407) baseStart_23407 baseEnd_23407 := by
    simpa [prefixWord, tailWord_23407, baseEnd_23407] using wordTrace_append hprefix tailTrace_23407
  have hstable : (prefixWord ++ tailWord_23407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23407).length < 2 ^ (prefixWord ++ tailWord_23407).sum := by decide
  have hdescent : baseEnd_23407 < baseStart_23407 := by decide
  rcases family_descends (prefixWord ++ tailWord_23407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23431 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 1, 4]
def baseStart_23431 : Nat := 118140960795 + 23431 * 2 ^ 59
def prefixEnd_23431 : Nat := 4983230072969 + 3 ^ 40 * 23431 * 2
def baseEnd_23431 : Nat := 4010455071867686601583

theorem tailTrace_23431 : CollatzResearch.WordTrace tailWord_23431 prefixEnd_23431 4010455071867686601583 := by
  unfold tailWord_23431
  simp only [CollatzResearch.WordTrace]
  refine ⟨854598778120963541318147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 569732518747309027545431 854598778120963541318147)
  ·
    refine ⟨1281898167181445311977221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 854598778120963541318147 1281898167181445311977221)
    ·
      refine ⟨240355906346520995995729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1281898167181445311977221 240355906346520995995729)
      ·
        refine ⟨180266929759890746996797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240355906346520995995729 180266929759890746996797)
        ·
          refine ⟨67600098659959030123799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180266929759890746996797 67600098659959030123799)
          ·
            refine ⟨101400147989938545185699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67600098659959030123799 101400147989938545185699)
            ·
              refine ⟨152100221984907817778549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101400147989938545185699 152100221984907817778549)
              ·
                refine ⟨14259395811085107916739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152100221984907817778549 14259395811085107916739)
                ·
                  refine ⟨21389093716627661875109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14259395811085107916739 21389093716627661875109)
                  ·
                    refine ⟨4010455071867686601583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21389093716627661875109 4010455071867686601583)
                    ·
                      rfl

theorem cell23_23431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_23431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23431 prefixEnd_23431 := by exact prefixLift 23431
  have htrace : WordTrace (prefixWord ++ tailWord_23431) baseStart_23431 baseEnd_23431 := by
    simpa [prefixWord, tailWord_23431, baseEnd_23431] using wordTrace_append hprefix tailTrace_23431
  have hstable : (prefixWord ++ tailWord_23431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23431).length < 2 ^ (prefixWord ++ tailWord_23431).sum := by decide
  have hdescent : baseEnd_23431 < baseStart_23431 := by decide
  rcases family_descends (prefixWord ++ tailWord_23431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23440 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_23440 : Nat := 118140960795 + 23440 * 2 ^ 59
def prefixEnd_23440 : Nat := 4983230072969 + 3 ^ 40 * 23440 * 2
def baseEnd_23440 : Nat := 4011995513831174864069

theorem tailTrace_23440 : CollatzResearch.WordTrace tailWord_23440 prefixEnd_23440 4011995513831174864069 := by
  unfold tailWord_23440
  simp only [CollatzResearch.WordTrace]
  refine ⟨427463517544179039197887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 569951356725572052263849 427463517544179039197887)
  ·
    refine ⟨641195276316268558796831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 427463517544179039197887 641195276316268558796831)
    ·
      refine ⟨961792914474402838195247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641195276316268558796831 961792914474402838195247)
      ·
        refine ⟨1442689371711604257292871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961792914474402838195247 1442689371711604257292871)
        ·
          refine ⟨2164034057567406385939307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442689371711604257292871 2164034057567406385939307)
          ·
            refine ⟨3246051086351109578908961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164034057567406385939307 3246051086351109578908961)
            ·
              refine ⟨2434538314763332184181721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246051086351109578908961 2434538314763332184181721)
              ·
                refine ⟨1825903736072499138136291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434538314763332184181721 1825903736072499138136291)
                ·
                  refine ⟨2738855604108748707204437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825903736072499138136291 2738855604108748707204437)
                  ·
                    refine ⟨4011995513831174864069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 2738855604108748707204437 4011995513831174864069)
                    ·
                      rfl

theorem cell23_23440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_23440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23440 prefixEnd_23440 := by exact prefixLift 23440
  have htrace : WordTrace (prefixWord ++ tailWord_23440) baseStart_23440 baseEnd_23440 := by
    simpa [prefixWord, tailWord_23440, baseEnd_23440] using wordTrace_append hprefix tailTrace_23440
  have hstable : (prefixWord ++ tailWord_23440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23440).length < 2 ^ (prefixWord ++ tailWord_23440).sum := by decide
  have hdescent : baseEnd_23440 < baseStart_23440 := by decide
  rcases family_descends (prefixWord ++ tailWord_23440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23488 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 1, 1, 3]
def baseStart_23488 : Nat := 118140960795 + 23488 * 2 ^ 59
def prefixEnd_23488 : Nat := 4983230072969 + 3 ^ 40 * 23488 * 2
def baseEnd_23488 : Nat := 12060633612909336791987

theorem tailTrace_23488 : CollatzResearch.WordTrace tailWord_23488 prefixEnd_23488 12060633612909336791987 := by
  unfold tailWord_23488
  simp only [CollatzResearch.WordTrace]
  refine ⟨428338869457231138071559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 571118492609641517428745 428338869457231138071559)
  ·
    refine ⟨642508304185846707107339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428338869457231138071559 642508304185846707107339)
    ·
      refine ⟨963762456278770060661009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642508304185846707107339 963762456278770060661009)
      ·
        refine ⟨722821842209077545495757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 963762456278770060661009 722821842209077545495757)
        ·
          refine ⟨271058190828404079560909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722821842209077545495757 271058190828404079560909)
          ·
            refine ⟨101646821560651529835341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271058190828404079560909 101646821560651529835341)
            ·
              refine ⟨38117558085244323688253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101646821560651529835341 38117558085244323688253)
              ·
                refine ⟨14294084281966621383095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38117558085244323688253 14294084281966621383095)
                ·
                  refine ⟨21441126422949932074643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14294084281966621383095 21441126422949932074643)
                  ·
                    refine ⟨32161689634424898111965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21441126422949932074643 32161689634424898111965)
                    ·
                      refine ⟨12060633612909336791987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 32161689634424898111965 12060633612909336791987)
                      ·
                        rfl

theorem cell23_23488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_23488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23488 prefixEnd_23488 := by exact prefixLift 23488
  have htrace : WordTrace (prefixWord ++ tailWord_23488) baseStart_23488 baseEnd_23488 := by
    simpa [prefixWord, tailWord_23488, baseEnd_23488] using wordTrace_append hprefix tailTrace_23488
  have hstable : (prefixWord ++ tailWord_23488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23488).length < 2 ^ (prefixWord ++ tailWord_23488).sum := by decide
  have hdescent : baseEnd_23488 < baseStart_23488 := by decide
  rcases family_descends (prefixWord ++ tailWord_23488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23504 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 2, 4]
def baseStart_23504 : Nat := 118140960795 + 23504 * 2 ^ 59
def prefixEnd_23504 : Nat := 4983230072969 + 3 ^ 40 * 23504 * 2
def baseEnd_23504 : Nat := 4022949767793758063971

theorem tailTrace_23504 : CollatzResearch.WordTrace tailWord_23504 prefixEnd_23504 4022949767793758063971 := by
  unfold tailWord_23504
  simp only [CollatzResearch.WordTrace]
  refine ⟨428630653428248504362783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 571507537904331339150377 428630653428248504362783)
  ·
    refine ⟨642945980142372756544175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428630653428248504362783 642945980142372756544175)
    ·
      refine ⟨964418970213559134816263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642945980142372756544175 964418970213559134816263)
      ·
        refine ⟨1446628455320338702224395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964418970213559134816263 1446628455320338702224395)
        ·
          refine ⟨2169942682980508053336593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446628455320338702224395 2169942682980508053336593)
          ·
            refine ⟨1627457012235381040002445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2169942682980508053336593 1627457012235381040002445)
            ·
              refine ⟨610296379588267890000917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1627457012235381040002445 610296379588267890000917)
              ·
                refine ⟨28607642793200057343793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 610296379588267890000917 28607642793200057343793)
                ·
                  refine ⟨21455732094900043007845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28607642793200057343793 21455732094900043007845)
                  ·
                    refine ⟨4022949767793758063971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21455732094900043007845 4022949767793758063971)
                    ·
                      rfl

theorem cell23_23504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_23504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23504 prefixEnd_23504 := by exact prefixLift 23504
  have htrace : WordTrace (prefixWord ++ tailWord_23504) baseStart_23504 baseEnd_23504 := by
    simpa [prefixWord, tailWord_23504, baseEnd_23504] using wordTrace_append hprefix tailTrace_23504
  have hstable : (prefixWord ++ tailWord_23504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23504).length < 2 ^ (prefixWord ++ tailWord_23504).sum := by decide
  have hdescent : baseEnd_23504 < baseStart_23504 := by decide
  rcases family_descends (prefixWord ++ tailWord_23504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23511 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 3, 2, 2]
def baseStart_23511 : Nat := 118140960795 + 23511 * 2 ^ 59
def prefixEnd_23511 : Nat := 4983230072969 + 3 ^ 40 * 23511 * 2
def baseEnd_23511 : Nat := 12072443667962746804381

theorem tailTrace_23511 : CollatzResearch.WordTrace tailWord_23511 prefixEnd_23511 12072443667962746804381 := by
  unfold tailWord_23511
  simp only [CollatzResearch.WordTrace]
  refine ⟨857516617831137204230387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 571677745220758136153591 857516617831137204230387)
  ·
    refine ⟨1286274926746705806345581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 857516617831137204230387 1286274926746705806345581)
    ·
      refine ⟨482353097530014677379593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1286274926746705806345581 482353097530014677379593)
      ·
        refine ⟨361764823147511008034695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482353097530014677379593 361764823147511008034695)
        ·
          refine ⟨542647234721266512052043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361764823147511008034695 542647234721266512052043)
          ·
            refine ⟨813970852081899768078065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542647234721266512052043 813970852081899768078065)
            ·
              refine ⟨610478139061424826058549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813970852081899768078065 610478139061424826058549)
              ·
                refine ⟨57232325537008577442989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610478139061424826058549 57232325537008577442989)
                ·
                  refine ⟨21462122076378216541121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57232325537008577442989 21462122076378216541121)
                  ·
                    refine ⟨16096591557283662405841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21462122076378216541121 16096591557283662405841)
                    ·
                      refine ⟨12072443667962746804381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16096591557283662405841 12072443667962746804381)
                      ·
                        rfl

theorem cell23_23511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_23511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23511 prefixEnd_23511 := by exact prefixLift 23511
  have htrace : WordTrace (prefixWord ++ tailWord_23511) baseStart_23511 baseEnd_23511 := by
    simpa [prefixWord, tailWord_23511, baseEnd_23511] using wordTrace_append hprefix tailTrace_23511
  have hstable : (prefixWord ++ tailWord_23511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23511).length < 2 ^ (prefixWord ++ tailWord_23511).sum := by decide
  have hdescent : baseEnd_23511 < baseStart_23511 := by decide
  rcases family_descends (prefixWord ++ tailWord_23511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23514 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_23514 : Nat := 118140960795 + 23514 * 2 ^ 59
def prefixEnd_23514 : Nat := 4983230072969 + 3 ^ 40 * 23514 * 2
def baseEnd_23514 : Nat := 12073984109926235066867

theorem tailTrace_23514 : CollatzResearch.WordTrace tailWord_23514 prefixEnd_23514 12073984109926235066867 := by
  unfold tailWord_23514
  simp only [CollatzResearch.WordTrace]
  refine ⟨214406509205067179147399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 571750691213512477726397 214406509205067179147399)
  ·
    refine ⟨321609763807600768721099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214406509205067179147399 321609763807600768721099)
    ·
      refine ⟨482414645711401153081649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321609763807600768721099 482414645711401153081649)
      ·
        refine ⟨361810984283550864811237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482414645711401153081649 361810984283550864811237)
        ·
          refine ⟨67839559553165787152107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 361810984283550864811237 67839559553165787152107)
          ·
            refine ⟨101759339329748680728161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67839559553165787152107 101759339329748680728161)
            ·
              refine ⟨76319504497311510546121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101759339329748680728161 76319504497311510546121)
              ·
                refine ⟨57239628372983632909591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76319504497311510546121 57239628372983632909591)
                ·
                  refine ⟨85859442559475449364387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57239628372983632909591 85859442559475449364387)
                  ·
                    refine ⟨128789163839213174046581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85859442559475449364387 128789163839213174046581)
                    ·
                      refine ⟨12073984109926235066867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 128789163839213174046581 12073984109926235066867)
                      ·
                        rfl

theorem cell23_23514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_23514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23514 prefixEnd_23514 := by exact prefixLift 23514
  have htrace : WordTrace (prefixWord ++ tailWord_23514) baseStart_23514 baseEnd_23514 := by
    simpa [prefixWord, tailWord_23514, baseEnd_23514] using wordTrace_append hprefix tailTrace_23514
  have hstable : (prefixWord ++ tailWord_23514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23514).length < 2 ^ (prefixWord ++ tailWord_23514).sum := by decide
  have hdescent : baseEnd_23514 < baseStart_23514 := by decide
  rcases family_descends (prefixWord ++ tailWord_23514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23525 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_23525 : Nat := 118140960795 + 23525 * 2 ^ 59
def prefixEnd_23525 : Nat := 4983230072969 + 3 ^ 40 * 23525 * 2
def baseEnd_23525 : Nat := 4026544132375230676439

theorem tailTrace_23525 : CollatzResearch.WordTrace tailWord_23525 prefixEnd_23525 4026544132375230676439 := by
  unfold tailWord_23525
  simp only [CollatzResearch.WordTrace]
  refine ⟨858027239780417595240029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 572018159853611730160019 858027239780417595240029)
  ·
    refine ⟨321760214917656598215011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 858027239780417595240029 321760214917656598215011)
    ·
      refine ⟨482640322376484897322517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321760214917656598215011 482640322376484897322517)
      ·
        refine ⟨22623765111397729561993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 482640322376484897322517 22623765111397729561993)
        ·
          refine ⟨16967823833548297171495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22623765111397729561993 16967823833548297171495)
          ·
            refine ⟨25451735750322445757243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16967823833548297171495 25451735750322445757243)
            ·
              refine ⟨38177603625483668635865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25451735750322445757243 38177603625483668635865)
              ·
                refine ⟨28633202719112751476899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38177603625483668635865 28633202719112751476899)
                ·
                  refine ⟨42949804078669127215349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28633202719112751476899 42949804078669127215349)
                  ·
                    refine ⟨4026544132375230676439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42949804078669127215349 4026544132375230676439)
                    ·
                      rfl

theorem cell23_23525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_23525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23525 prefixEnd_23525 := by exact prefixLift 23525
  have htrace : WordTrace (prefixWord ++ tailWord_23525) baseStart_23525 baseEnd_23525 := by
    simpa [prefixWord, tailWord_23525, baseEnd_23525] using wordTrace_append hprefix tailTrace_23525
  have hstable : (prefixWord ++ tailWord_23525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23525).length < 2 ^ (prefixWord ++ tailWord_23525).sum := by decide
  have hdescent : baseEnd_23525 < baseStart_23525 := by decide
  rcases family_descends (prefixWord ++ tailWord_23525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23548 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_23548 : Nat := 118140960795 + 23548 * 2 ^ 59
def prefixEnd_23548 : Nat := 4983230072969 + 3 ^ 40 * 23548 * 2
def baseEnd_23548 : Nat := 12091442452179102041711

theorem tailTrace_23548 : CollatzResearch.WordTrace tailWord_23548 prefixEnd_23548 12091442452179102041711 := by
  unfold tailWord_23548
  simp only [CollatzResearch.WordTrace]
  refine ⟨429433059348546261663649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 572577412464728348884865 429433059348546261663649)
  ·
    refine ⟨322074794511409696247737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 429433059348546261663649 322074794511409696247737)
    ·
      refine ⟨241556095883557272185803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322074794511409696247737 241556095883557272185803)
      ·
        refine ⟨362334143825335908278705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241556095883557272185803 362334143825335908278705)
        ·
          refine ⟨271750607869001931209029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362334143825335908278705 271750607869001931209029)
          ·
            refine ⟨50953238975437862101693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271750607869001931209029 50953238975437862101693)
            ·
              refine ⟨19107464615789198288135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50953238975437862101693 19107464615789198288135)
              ·
                refine ⟨28661196923683797432203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19107464615789198288135 28661196923683797432203)
                ·
                  refine ⟨42991795385525696148305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28661196923683797432203 42991795385525696148305)
                  ·
                    refine ⟨32243846539144272111229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42991795385525696148305 32243846539144272111229)
                    ·
                      refine ⟨12091442452179102041711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 32243846539144272111229 12091442452179102041711)
                      ·
                        rfl

theorem cell23_23548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_23548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23548 prefixEnd_23548 := by exact prefixLift 23548
  have htrace : WordTrace (prefixWord ++ tailWord_23548) baseStart_23548 baseEnd_23548 := by
    simpa [prefixWord, tailWord_23548, baseEnd_23548] using wordTrace_append hprefix tailTrace_23548
  have hstable : (prefixWord ++ tailWord_23548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23548).length < 2 ^ (prefixWord ++ tailWord_23548).sum := by decide
  have hdescent : baseEnd_23548 < baseStart_23548 := by decide
  rcases family_descends (prefixWord ++ tailWord_23548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23562 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_23562 : Nat := 118140960795 + 23562 * 2 ^ 59
def prefixEnd_23562 : Nat := 4983230072969 + 3 ^ 40 * 23562 * 2
def baseEnd_23562 : Nat := 12098631181342047266647

theorem tailTrace_23562 : CollatzResearch.WordTrace tailWord_23562 prefixEnd_23562 12098631181342047266647 := by
  unfold tailWord_23562
  simp only [CollatzResearch.WordTrace]
  refine ⟨214844185161593228584235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 572917827097581942891293 214844185161593228584235)
  ·
    refine ⟨322266277742389842876353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214844185161593228584235 322266277742389842876353)
    ·
      refine ⟨241699708306792382157265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322266277742389842876353 241699708306792382157265)
      ·
        refine ⟨181274781230094286617949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241699708306792382157265 181274781230094286617949)
        ·
          refine ⟨67978042961285357481731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181274781230094286617949 67978042961285357481731)
          ·
            refine ⟨101967064441928036222597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67978042961285357481731 101967064441928036222597)
            ·
              refine ⟨19118824582861506791737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101967064441928036222597 19118824582861506791737)
              ·
                refine ⟨14339118437146130093803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19118824582861506791737 14339118437146130093803)
                ·
                  refine ⟨21508677655719195140705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14339118437146130093803 21508677655719195140705)
                  ·
                    refine ⟨16131508241789396355529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21508677655719195140705 16131508241789396355529)
                    ·
                      refine ⟨12098631181342047266647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16131508241789396355529 12098631181342047266647)
                      ·
                        rfl

theorem cell23_23562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_23562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23562 prefixEnd_23562 := by exact prefixLift 23562
  have htrace : WordTrace (prefixWord ++ tailWord_23562) baseStart_23562 baseEnd_23562 := by
    simpa [prefixWord, tailWord_23562, baseEnd_23562] using wordTrace_append hprefix tailTrace_23562
  have hstable : (prefixWord ++ tailWord_23562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23562).length < 2 ^ (prefixWord ++ tailWord_23562).sum := by decide
  have hdescent : baseEnd_23562 < baseStart_23562 := by decide
  rcases family_descends (prefixWord ++ tailWord_23562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23577 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_23577 : Nat := 118140960795 + 23577 * 2 ^ 59
def prefixEnd_23577 : Nat := 4983230072969 + 3 ^ 40 * 23577 * 2
def baseEnd_23577 : Nat := 4035444463719829526359

theorem tailTrace_23577 : CollatzResearch.WordTrace tailWord_23577 prefixEnd_23577 4035444463719829526359 := by
  unfold tailWord_23577
  simp only [CollatzResearch.WordTrace]
  refine ⟨859923835592030476132985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 573282557061353650755323 859923835592030476132985)
  ·
    refine ⟨644942876694022857099739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 859923835592030476132985 644942876694022857099739)
    ·
      refine ⟨967414315041034285649609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644942876694022857099739 967414315041034285649609)
      ·
        refine ⟨725560736280775714237207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967414315041034285649609 725560736280775714237207)
        ·
          refine ⟨1088341104421163571355811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725560736280775714237207 1088341104421163571355811)
          ·
            refine ⟨1632511656631745357033717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088341104421163571355811 1632511656631745357033717)
            ·
              refine ⟨153047967809226127221911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1632511656631745357033717 153047967809226127221911)
              ·
                refine ⟨229571951713839190832867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153047967809226127221911 229571951713839190832867)
                ·
                  refine ⟨344357927570758786249301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229571951713839190832867 344357927570758786249301)
                  ·
                    refine ⟨4035444463719829526359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 344357927570758786249301 4035444463719829526359)
                    ·
                      rfl

theorem cell23_23577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_23577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23577 prefixEnd_23577 := by exact prefixLift 23577
  have htrace : WordTrace (prefixWord ++ tailWord_23577) baseStart_23577 baseEnd_23577 := by
    simpa [prefixWord, tailWord_23577, baseEnd_23577] using wordTrace_append hprefix tailTrace_23577
  have hstable : (prefixWord ++ tailWord_23577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23577).length < 2 ^ (prefixWord ++ tailWord_23577).sum := by decide
  have hdescent : baseEnd_23577 < baseStart_23577 := by decide
  rcases family_descends (prefixWord ++ tailWord_23577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23588 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_23588 : Nat := 118140960795 + 23588 * 2 ^ 59
def prefixEnd_23588 : Nat := 4983230072969 + 3 ^ 40 * 23588 * 2
def baseEnd_23588 : Nat := 12111981678358945541527

theorem tailTrace_23588 : CollatzResearch.WordTrace tailWord_23588 prefixEnd_23588 12111981678358945541527 := by
  unfold tailWord_23588
  simp only [CollatzResearch.WordTrace]
  refine ⟨430162519276089677391709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 573550025701452903188945 430162519276089677391709)
  ·
    refine ⟨161310944728533629021891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 430162519276089677391709 161310944728533629021891)
    ·
      refine ⟨241966417092800443532837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161310944728533629021891 241966417092800443532837)
      ·
        refine ⟨45368703204900083162407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241966417092800443532837 45368703204900083162407)
        ·
          refine ⟨68053054807350124743611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45368703204900083162407 68053054807350124743611)
          ·
            refine ⟨102079582211025187115417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68053054807350124743611 102079582211025187115417)
            ·
              refine ⟨76559686658268890336563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102079582211025187115417 76559686658268890336563)
              ·
                refine ⟨114839529987403335504845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76559686658268890336563 114839529987403335504845)
                ·
                  refine ⟨43064823745276250814317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114839529987403335504845 43064823745276250814317)
                  ·
                    refine ⟨16149308904478594055369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43064823745276250814317 16149308904478594055369)
                    ·
                      refine ⟨12111981678358945541527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16149308904478594055369 12111981678358945541527)
                      ·
                        rfl

theorem cell23_23588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_23588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23588 prefixEnd_23588 := by exact prefixLift 23588
  have htrace : WordTrace (prefixWord ++ tailWord_23588) baseStart_23588 baseEnd_23588 := by
    simpa [prefixWord, tailWord_23588, baseEnd_23588] using wordTrace_append hprefix tailTrace_23588
  have hstable : (prefixWord ++ tailWord_23588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23588).length < 2 ^ (prefixWord ++ tailWord_23588).sum := by decide
  have hdescent : baseEnd_23588 < baseStart_23588 := by decide
  rcases family_descends (prefixWord ++ tailWord_23588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23601 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 1, 4, 2]
def baseStart_23601 : Nat := 118140960795 + 23601 * 2 ^ 59
def prefixEnd_23601 : Nat := 4983230072969 + 3 ^ 40 * 23601 * 2
def baseEnd_23601 : Nat := 12118656926867394678967

theorem tailTrace_23601 : CollatzResearch.WordTrace tailWord_23601 prefixEnd_23601 12118656926867394678967 := by
  unfold tailWord_23601
  simp only [CollatzResearch.WordTrace]
  refine ⟨860799187505082575006657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 573866125003388383337771 860799187505082575006657)
  ·
    refine ⟨645599390628811931254993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 860799187505082575006657 645599390628811931254993)
    ·
      refine ⟨484199542971608948441245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 645599390628811931254993 484199542971608948441245)
      ·
        refine ⟨181574828614353355665467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484199542971608948441245 181574828614353355665467)
        ·
          refine ⟨272362242921530033498201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181574828614353355665467 272362242921530033498201)
          ·
            refine ⟨204271682191147525123651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272362242921530033498201 204271682191147525123651)
            ·
              refine ⟨306407523286721287685477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204271682191147525123651 306407523286721287685477)
              ·
                refine ⟨57451410616260241441027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306407523286721287685477 57451410616260241441027)
                ·
                  refine ⟨86177115924390362161541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57451410616260241441027 86177115924390362161541)
                  ·
                    refine ⟨16158209235823192905289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86177115924390362161541 16158209235823192905289)
                    ·
                      refine ⟨12118656926867394678967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16158209235823192905289 12118656926867394678967)
                      ·
                        rfl

theorem cell23_23601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_23601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23601 prefixEnd_23601 := by exact prefixLift 23601
  have htrace : WordTrace (prefixWord ++ tailWord_23601) baseStart_23601 baseEnd_23601 := by
    simpa [prefixWord, tailWord_23601, baseEnd_23601] using wordTrace_append hprefix tailTrace_23601
  have hstable : (prefixWord ++ tailWord_23601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23601).length < 2 ^ (prefixWord ++ tailWord_23601).sum := by decide
  have hdescent : baseEnd_23601 < baseStart_23601 := by decide
  rcases family_descends (prefixWord ++ tailWord_23601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23607 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 11]
def baseStart_23607 : Nat := 118140960795 + 23607 * 2 ^ 59
def prefixEnd_23607 : Nat := 4983230072969 + 3 ^ 40 * 23607 * 2
def baseEnd_23607 : Nat := 1346859756754930133771

theorem tailTrace_23607 : CollatzResearch.WordTrace tailWord_23607 prefixEnd_23607 1346859756754930133771 := by
  unfold tailWord_23607
  simp only [CollatzResearch.WordTrace]
  refine ⟨861018025483345599725075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 574012016988897066483383 861018025483345599725075)
  ·
    refine ⟨1291527038225018399587613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861018025483345599725075 1291527038225018399587613)
    ·
      refine ⟨484322639334381899845355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1291527038225018399587613 484322639334381899845355)
      ·
        refine ⟨726483959001572849768033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484322639334381899845355 726483959001572849768033)
        ·
          refine ⟨544862969251179637326025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726483959001572849768033 544862969251179637326025)
          ·
            refine ⟨408647226938384727994519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544862969251179637326025 408647226938384727994519)
            ·
              refine ⟨612970840407577091991779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408647226938384727994519 612970840407577091991779)
              ·
                refine ⟨919456260611365637987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612970840407577091991779 919456260611365637987669)
                ·
                  refine ⟨1346859756754930133771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 919456260611365637987669 1346859756754930133771)
                  ·
                    rfl

theorem cell23_23607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 11].length) (baseStart_23607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23607 prefixEnd_23607 := by exact prefixLift 23607
  have htrace : WordTrace (prefixWord ++ tailWord_23607) baseStart_23607 baseEnd_23607 := by
    simpa [prefixWord, tailWord_23607, baseEnd_23607] using wordTrace_append hprefix tailTrace_23607
  have hstable : (prefixWord ++ tailWord_23607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23607).length < 2 ^ (prefixWord ++ tailWord_23607).sum := by decide
  have hdescent : baseEnd_23607 < baseStart_23607 := by decide
  rcases family_descends (prefixWord ++ tailWord_23607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23624 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 7]
def baseStart_23624 : Nat := 118140960795 + 23624 * 2 ^ 59
def prefixEnd_23624 : Nat := 4983230072969 + 3 ^ 40 * 23624 * 2
def baseEnd_23624 : Nat := 1347829664657867187929

theorem tailTrace_23624 : CollatzResearch.WordTrace tailWord_23624 prefixEnd_23624 1347829664657867187929 := by
  unfold tailWord_23624
  simp only [CollatzResearch.WordTrace]
  refine ⟨430819033210878751546963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 574425377614505002062617 430819033210878751546963)
  ·
    refine ⟨646228549816318127320445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 430819033210878751546963 646228549816318127320445)
    ·
      refine ⟨242335706181119297745167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 646228549816318127320445 242335706181119297745167)
      ·
        refine ⟨363503559271678946617751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242335706181119297745167 363503559271678946617751)
        ·
          refine ⟨545255338907518419926627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363503559271678946617751 545255338907518419926627)
          ·
            refine ⟨817883008361277629889941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545255338907518419926627 817883008361277629889941)
            ·
              refine ⟨38338266016934888901091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 817883008361277629889941 38338266016934888901091)
              ·
                refine ⟨57507399025402333351637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38338266016934888901091 57507399025402333351637)
                ·
                  refine ⟨1347829664657867187929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 57507399025402333351637 1347829664657867187929)
                  ·
                    rfl

theorem cell23_23624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 7].length) (baseStart_23624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23624 prefixEnd_23624 := by exact prefixLift 23624
  have htrace : WordTrace (prefixWord ++ tailWord_23624) baseStart_23624 baseEnd_23624 := by
    simpa [prefixWord, tailWord_23624, baseEnd_23624] using wordTrace_append hprefix tailTrace_23624
  have hstable : (prefixWord ++ tailWord_23624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23624).length < 2 ^ (prefixWord ++ tailWord_23624).sum := by decide
  have hdescent : baseEnd_23624 < baseStart_23624 := by decide
  rcases family_descends (prefixWord ++ tailWord_23624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23627 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_23627 : Nat := 118140960795 + 23627 * 2 ^ 59
def prefixEnd_23627 : Nat := 4983230072969 + 3 ^ 40 * 23627 * 2
def baseEnd_23627 : Nat := 12132007423884292953847

theorem tailTrace_23627 : CollatzResearch.WordTrace tailWord_23627 prefixEnd_23627 12132007423884292953847 := by
  unfold tailWord_23627
  simp only [CollatzResearch.WordTrace]
  refine ⟨861747485410889015453135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 574498323607259343635423 861747485410889015453135)
  ·
    refine ⟨1292621228116333523179703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861747485410889015453135 1292621228116333523179703)
    ·
      refine ⟨1938931842174500284769555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292621228116333523179703 1938931842174500284769555)
      ·
        refine ⟨2908397763261750427154333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938931842174500284769555 2908397763261750427154333)
        ·
          refine ⟨1090649161223156410182875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2908397763261750427154333 1090649161223156410182875)
          ·
            refine ⟨1635973741834734615274313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090649161223156410182875 1635973741834734615274313)
            ·
              refine ⟨1226980306376050961455735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635973741834734615274313 1226980306376050961455735)
              ·
                refine ⟨1840470459564076442183603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226980306376050961455735 1840470459564076442183603)
                ·
                  refine ⟨2760705689346114663275405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840470459564076442183603 2760705689346114663275405)
                  ·
                    refine ⟨1035264633504792998728277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2760705689346114663275405 1035264633504792998728277)
                    ·
                      refine ⟨12132007423884292953847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 1035264633504792998728277 12132007423884292953847)
                      ·
                        rfl

theorem cell23_23627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_23627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23627 prefixEnd_23627 := by exact prefixLift 23627
  have htrace : WordTrace (prefixWord ++ tailWord_23627) baseStart_23627 baseEnd_23627 := by
    simpa [prefixWord, tailWord_23627, baseEnd_23627] using wordTrace_append hprefix tailTrace_23627
  have hstable : (prefixWord ++ tailWord_23627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23627).length < 2 ^ (prefixWord ++ tailWord_23627).sum := by decide
  have hdescent : baseEnd_23627 < baseStart_23627 := by decide
  rcases family_descends (prefixWord ++ tailWord_23627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23658 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_23658 : Nat := 118140960795 + 23658 * 2 ^ 59
def prefixEnd_23658 : Nat := 4983230072969 + 3 ^ 40 * 23658 * 2
def baseEnd_23658 : Nat := 1349769480463741296245

theorem tailTrace_23658 : CollatzResearch.WordTrace tailWord_23658 prefixEnd_23658 1349769480463741296245 := by
  unfold tailWord_23658
  simp only [CollatzResearch.WordTrace]
  refine ⟨215719537074645327457907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 575252098865720873221085 215719537074645327457907)
  ·
    refine ⟨323579305611967991186861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215719537074645327457907 323579305611967991186861)
    ·
      refine ⟨121342239604487996695073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323579305611967991186861 121342239604487996695073)
      ·
        refine ⟨91006679703365997521305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121342239604487996695073 91006679703365997521305)
        ·
          refine ⟨68255009777524498140979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91006679703365997521305 68255009777524498140979)
          ·
            refine ⟨102382514666286747211469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68255009777524498140979 102382514666286747211469)
            ·
              refine ⟨38393442999857530204301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102382514666286747211469 38393442999857530204301)
              ·
                refine ⟨14397541124946573826613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38393442999857530204301 14397541124946573826613)
                ·
                  refine ⟨1349769480463741296245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14397541124946573826613 1349769480463741296245)
                  ·
                    rfl

theorem cell23_23658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_23658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23658 prefixEnd_23658 := by exact prefixLift 23658
  have htrace : WordTrace (prefixWord ++ tailWord_23658) baseStart_23658 baseEnd_23658 := by
    simpa [prefixWord, tailWord_23658, baseEnd_23658] using wordTrace_append hprefix tailTrace_23658
  have hstable : (prefixWord ++ tailWord_23658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23658).length < 2 ^ (prefixWord ++ tailWord_23658).sum := by decide
  have hdescent : baseEnd_23658 < baseStart_23658 := by decide
  rcases family_descends (prefixWord ++ tailWord_23658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23664 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_23664 : Nat := 118140960795 + 23664 * 2 ^ 59
def prefixEnd_23664 : Nat := 4983230072969 + 3 ^ 40 * 23664 * 2
def baseEnd_23664 : Nat := 12151006208100648191177

theorem tailTrace_23664 : CollatzResearch.WordTrace tailWord_23664 prefixEnd_23664 12151006208100648191177 := by
  unfold tailWord_23664
  simp only [CollatzResearch.WordTrace]
  refine ⟨431548493138422167275023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 575397990851229556366697 431548493138422167275023)
  ·
    refine ⟨647322739707633250912535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431548493138422167275023 647322739707633250912535)
    ·
      refine ⟨970984109561449876368803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647322739707633250912535 970984109561449876368803)
      ·
        refine ⟨1456476164342174814553205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970984109561449876368803 1456476164342174814553205)
        ·
          refine ⟨136544640407078888864363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1456476164342174814553205 136544640407078888864363)
          ·
            refine ⟨204816960610618333296545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136544640407078888864363 204816960610618333296545)
            ·
              refine ⟨153612720457963749972409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204816960610618333296545 153612720457963749972409)
              ·
                refine ⟨115209540343472812479307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153612720457963749972409 115209540343472812479307)
                ·
                  refine ⟨172814310515209218718961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115209540343472812479307 172814310515209218718961)
                  ·
                    refine ⟨129610732886406914039221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172814310515209218718961 129610732886406914039221)
                    ·
                      refine ⟨12151006208100648191177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 129610732886406914039221 12151006208100648191177)
                      ·
                        rfl

theorem cell23_23664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_23664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23664 prefixEnd_23664 := by exact prefixLift 23664
  have htrace : WordTrace (prefixWord ++ tailWord_23664) baseStart_23664 baseEnd_23664 := by
    simpa [prefixWord, tailWord_23664, baseEnd_23664] using wordTrace_append hprefix tailTrace_23664
  have hstable : (prefixWord ++ tailWord_23664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23664).length < 2 ^ (prefixWord ++ tailWord_23664).sum := by decide
  have hdescent : baseEnd_23664 < baseStart_23664 := by decide
  rcases family_descends (prefixWord ++ tailWord_23664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23681 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_23681 : Nat := 118140960795 + 23681 * 2 ^ 59
def prefixEnd_23681 : Nat := 4983230072969 + 3 ^ 40 * 23681 * 2
def baseEnd_23681 : Nat := 12159735379227081678599

theorem tailTrace_23681 : CollatzResearch.WordTrace tailWord_23681 prefixEnd_23681 12159735379227081678599 := by
  unfold tailWord_23681
  simp only [CollatzResearch.WordTrace]
  refine ⟨863717027215256237918897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 575811351476837491945931 863717027215256237918897)
  ·
    refine ⟨647787770411442178439173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 863717027215256237918897 647787770411442178439173)
    ·
      refine ⟨121460206952145408457345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 647787770411442178439173 121460206952145408457345)
      ·
        refine ⟨91095155214109056343009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121460206952145408457345 91095155214109056343009)
        ·
          refine ⟨68321366410581792257257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91095155214109056343009 68321366410581792257257)
          ·
            refine ⟨51241024807936344192943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68321366410581792257257 51241024807936344192943)
            ·
              refine ⟨76861537211904516289415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51241024807936344192943 76861537211904516289415)
              ·
                refine ⟨115292305817856774434123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76861537211904516289415 115292305817856774434123)
                ·
                  refine ⟨172938458726785161651185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115292305817856774434123 172938458726785161651185)
                  ·
                    refine ⟨129703844045088871238389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172938458726785161651185 129703844045088871238389)
                    ·
                      refine ⟨12159735379227081678599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 129703844045088871238389 12159735379227081678599)
                      ·
                        rfl

theorem cell23_23681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_23681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23681 prefixEnd_23681 := by exact prefixLift 23681
  have htrace : WordTrace (prefixWord ++ tailWord_23681) baseStart_23681 baseEnd_23681 := by
    simpa [prefixWord, tailWord_23681, baseEnd_23681] using wordTrace_append hprefix tailTrace_23681
  have hstable : (prefixWord ++ tailWord_23681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23681).length < 2 ^ (prefixWord ++ tailWord_23681).sum := by decide
  have hdescent : baseEnd_23681 < baseStart_23681 := by decide
  rcases family_descends (prefixWord ++ tailWord_23681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23691 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 2, 4, 2]
def baseStart_23691 : Nat := 118140960795 + 23691 * 2 ^ 59
def prefixEnd_23691 : Nat := 4983230072969 + 3 ^ 40 * 23691 * 2
def baseEnd_23691 : Nat := 12164870185772042553553

theorem tailTrace_23691 : CollatzResearch.WordTrace tailWord_23691 prefixEnd_23691 12164870185772042553553 := by
  unfold tailWord_23691
  simp only [CollatzResearch.WordTrace]
  refine ⟨864081757179027945782927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 576054504786018630521951 864081757179027945782927)
  ·
    refine ⟨1296122635768541918674391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864081757179027945782927 1296122635768541918674391)
    ·
      refine ⟨1944183953652812878011587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296122635768541918674391 1944183953652812878011587)
      ·
        refine ⟨2916275930479219317017381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944183953652812878011587 2916275930479219317017381)
        ·
          refine ⟨546801736964853621940759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2916275930479219317017381 546801736964853621940759)
          ·
            refine ⟨820202605447280432911139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546801736964853621940759 820202605447280432911139)
            ·
              refine ⟨1230303908170920649366709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820202605447280432911139 1230303908170920649366709)
              ·
                refine ⟨115340991391023810878129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1230303908170920649366709 115340991391023810878129)
                ·
                  refine ⟨86505743543267858158597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115340991391023810878129 86505743543267858158597)
                  ·
                    refine ⟨16219826914362723404737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86505743543267858158597 16219826914362723404737)
                    ·
                      refine ⟨12164870185772042553553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16219826914362723404737 12164870185772042553553)
                      ·
                        rfl

theorem cell23_23691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4, 2].length) (baseStart_23691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23691 prefixEnd_23691 := by exact prefixLift 23691
  have htrace : WordTrace (prefixWord ++ tailWord_23691) baseStart_23691 baseEnd_23691 := by
    simpa [prefixWord, tailWord_23691, baseEnd_23691] using wordTrace_append hprefix tailTrace_23691
  have hstable : (prefixWord ++ tailWord_23691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23691).length < 2 ^ (prefixWord ++ tailWord_23691).sum := by decide
  have hdescent : baseEnd_23691 < baseStart_23691 := by decide
  rcases family_descends (prefixWord ++ tailWord_23691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23708 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_23708 : Nat := 118140960795 + 23708 * 2 ^ 59
def prefixEnd_23708 : Nat := 4983230072969 + 3 ^ 40 * 23708 * 2
def baseEnd_23708 : Nat := 12173599356898476040975

theorem tailTrace_23708 : CollatzResearch.WordTrace tailWord_23708 prefixEnd_23708 12173599356898476040975 := by
  unfold tailWord_23708
  simp only [CollatzResearch.WordTrace]
  refine ⟨432350899058719924575889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 576467865411626566101185 432350899058719924575889)
  ·
    refine ⟨324263174294039943431917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 432350899058719924575889 324263174294039943431917)
    ·
      refine ⟨121598690360264978786969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324263174294039943431917 121598690360264978786969)
      ·
        refine ⟨91199017770198734090227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121598690360264978786969 91199017770198734090227)
        ·
          refine ⟨136798526655298101135341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91199017770198734090227 136798526655298101135341)
          ·
            refine ⟨51299447495736787925753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136798526655298101135341 51299447495736787925753)
            ·
              refine ⟨38474585621802590944315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51299447495736787925753 38474585621802590944315)
              ·
                refine ⟨57711878432703886416473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38474585621802590944315 57711878432703886416473)
                ·
                  refine ⟨43283908824527914812355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57711878432703886416473 43283908824527914812355)
                  ·
                    refine ⟨64925863236791872218533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43283908824527914812355 64925863236791872218533)
                    ·
                      refine ⟨12173599356898476040975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 64925863236791872218533 12173599356898476040975)
                      ·
                        rfl

theorem cell23_23708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_23708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23708 prefixEnd_23708 := by exact prefixLift 23708
  have htrace : WordTrace (prefixWord ++ tailWord_23708) baseStart_23708 baseEnd_23708 := by
    simpa [prefixWord, tailWord_23708, baseEnd_23708] using wordTrace_append hprefix tailTrace_23708
  have hstable : (prefixWord ++ tailWord_23708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23708).length < 2 ^ (prefixWord ++ tailWord_23708).sum := by decide
  have hdescent : baseEnd_23708 < baseStart_23708 := by decide
  rcases family_descends (prefixWord ++ tailWord_23708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23761 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 1, 5]
def baseStart_23761 : Nat := 118140960795 + 23761 * 2 ^ 59
def prefixEnd_23761 : Nat := 4983230072969 + 3 ^ 40 * 23761 * 2
def baseEnd_23761 : Nat := 4066937943862256226077

theorem tailTrace_23761 : CollatzResearch.WordTrace tailWord_23761 prefixEnd_23761 4066937943862256226077 := by
  unfold tailWord_23761
  simp only [CollatzResearch.WordTrace]
  refine ⟨866634866925429900831137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 577756577950286600554091 866634866925429900831137)
  ·
    refine ⟨649976150194072425623353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 866634866925429900831137 649976150194072425623353)
    ·
      refine ⟨487482112645554319217515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 649976150194072425623353 487482112645554319217515)
      ·
        refine ⟨731223168968331478826273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487482112645554319217515 731223168968331478826273)
        ·
          refine ⟨548417376726248609119705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731223168968331478826273 548417376726248609119705)
          ·
            refine ⟨411313032544686456839779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548417376726248609119705 411313032544686456839779)
            ·
              refine ⟨616969548817029685259669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411313032544686456839779 616969548817029685259669)
              ·
                refine ⟨28920447600798266496547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 616969548817029685259669 28920447600798266496547)
                ·
                  refine ⟨43380671401197399744821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28920447600798266496547 43380671401197399744821)
                  ·
                    refine ⟨4066937943862256226077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43380671401197399744821 4066937943862256226077)
                    ·
                      rfl

theorem cell23_23761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_23761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23761 prefixEnd_23761 := by exact prefixLift 23761
  have htrace : WordTrace (prefixWord ++ tailWord_23761) baseStart_23761 baseEnd_23761 := by
    simpa [prefixWord, tailWord_23761, baseEnd_23761] using wordTrace_append hprefix tailTrace_23761
  have hstable : (prefixWord ++ tailWord_23761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23761).length < 2 ^ (prefixWord ++ tailWord_23761).sum := by decide
  have hdescent : baseEnd_23761 < baseStart_23761 := by decide
  rcases family_descends (prefixWord ++ tailWord_23761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23775 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 1, 1, 3]
def baseStart_23775 : Nat := 118140960795 + 23775 * 2 ^ 59
def prefixEnd_23775 : Nat := 4983230072969 + 3 ^ 40 * 23775 * 2
def baseEnd_23775 : Nat := 12208002560749713903167

theorem tailTrace_23775 : CollatzResearch.WordTrace tailWord_23775 prefixEnd_23775 12208002560749713903167 := by
  unfold tailWord_23775
  simp only [CollatzResearch.WordTrace]
  refine ⟨867145488874710291840779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 578096992583140194560519 867145488874710291840779)
  ·
    refine ⟨1300718233312065437761169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867145488874710291840779 1300718233312065437761169)
    ·
      refine ⟨975538674984049078320877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1300718233312065437761169 975538674984049078320877)
      ·
        refine ⟨365827003119018404370329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 975538674984049078320877 365827003119018404370329)
        ·
          refine ⟨274370252339263803277747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365827003119018404370329 274370252339263803277747)
          ·
            refine ⟨411555378508895704916621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274370252339263803277747 411555378508895704916621)
            ·
              refine ⟨154333266940835889343733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411555378508895704916621 154333266940835889343733)
              ·
                refine ⟨14468743775703364625975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154333266940835889343733 14468743775703364625975)
                ·
                  refine ⟨21703115663555046938963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14468743775703364625975 21703115663555046938963)
                  ·
                    refine ⟨32554673495332570408445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21703115663555046938963 32554673495332570408445)
                    ·
                      refine ⟨12208002560749713903167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 32554673495332570408445 12208002560749713903167)
                      ·
                        rfl

theorem cell23_23775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_23775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23775 prefixEnd_23775 := by exact prefixLift 23775
  have htrace : WordTrace (prefixWord ++ tailWord_23775) baseStart_23775 baseEnd_23775 := by
    simpa [prefixWord, tailWord_23775, baseEnd_23775] using wordTrace_append hprefix tailTrace_23775
  have hstable : (prefixWord ++ tailWord_23775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23775).length < 2 ^ (prefixWord ++ tailWord_23775).sum := by decide
  have hdescent : baseEnd_23775 < baseStart_23775 := by decide
  rcases family_descends (prefixWord ++ tailWord_23775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23801 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_23801 : Nat := 118140960795 + 23801 * 2 ^ 59
def prefixEnd_23801 : Nat := 4983230072969 + 3 ^ 40 * 23801 * 2
def baseEnd_23801 : Nat := 12221353057766612178047

theorem tailTrace_23801 : CollatzResearch.WordTrace tailWord_23801 prefixEnd_23801 12221353057766612178047 := by
  unfold tailWord_23801
  simp only [CollatzResearch.WordTrace]
  refine ⟨868093786780516732287257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 578729191187011154858171 868093786780516732287257)
  ·
    refine ⟨651070340085387549215443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 868093786780516732287257 651070340085387549215443)
    ·
      refine ⟨976605510128081323823165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 651070340085387549215443 976605510128081323823165)
      ·
        refine ⟨366227066298030496433687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 976605510128081323823165 366227066298030496433687)
        ·
          refine ⟨549340599447045744650531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366227066298030496433687 549340599447045744650531)
          ·
            refine ⟨824010899170568616975797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549340599447045744650531 824010899170568616975797)
            ·
              refine ⟨77251021797240807841481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 824010899170568616975797 77251021797240807841481)
              ·
                refine ⟨57938266347930605881111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77251021797240807841481 57938266347930605881111)
                ·
                  refine ⟨86907399521895908821667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57938266347930605881111 86907399521895908821667)
                  ·
                    refine ⟨130361099282843863232501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86907399521895908821667 130361099282843863232501)
                    ·
                      refine ⟨12221353057766612178047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 130361099282843863232501 12221353057766612178047)
                      ·
                        rfl

theorem cell23_23801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_23801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23801 prefixEnd_23801 := by exact prefixLift 23801
  have htrace : WordTrace (prefixWord ++ tailWord_23801) baseStart_23801 baseEnd_23801 := by
    simpa [prefixWord, tailWord_23801, baseEnd_23801] using wordTrace_append hprefix tailTrace_23801
  have hstable : (prefixWord ++ tailWord_23801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23801).length < 2 ^ (prefixWord ++ tailWord_23801).sum := by decide
  have hdescent : baseEnd_23801 < baseStart_23801 := by decide
  rcases family_descends (prefixWord ++ tailWord_23801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23811 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6]
def baseStart_23811 : Nat := 118140960795 + 23811 * 2 ^ 59
def prefixEnd_23811 : Nat := 4983230072969 + 3 ^ 40 * 23811 * 2
def baseEnd_23811 : Nat := 12226487864311573053001

theorem tailTrace_23811 : CollatzResearch.WordTrace tailWord_23811 prefixEnd_23811 12226487864311573053001 := by
  unfold tailWord_23811
  simp only [CollatzResearch.WordTrace]
  refine ⟨868458516744288440151287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 578972344496192293434191 868458516744288440151287)
  ·
    refine ⟨1302687775116432660226931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868458516744288440151287 1302687775116432660226931)
    ·
      refine ⟨1954031662674648990340397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302687775116432660226931 1954031662674648990340397)
      ·
        refine ⟨732761873502993371377649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1954031662674648990340397 732761873502993371377649)
        ·
          refine ⟨549571405127245028533237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732761873502993371377649 549571405127245028533237)
          ·
            refine ⟨51522319230679221424991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 549571405127245028533237 51522319230679221424991)
            ·
              refine ⟨77283478846018832137487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51522319230679221424991 77283478846018832137487)
              ·
                refine ⟨115925218269028248206231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77283478846018832137487 115925218269028248206231)
                ·
                  refine ⟨173887827403542372309347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115925218269028248206231 173887827403542372309347)
                  ·
                    refine ⟨260831741105313558464021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173887827403542372309347 260831741105313558464021)
                    ·
                      refine ⟨12226487864311573053001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 260831741105313558464021 12226487864311573053001)
                      ·
                        rfl

theorem cell23_23811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_23811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23811 prefixEnd_23811 := by exact prefixLift 23811
  have htrace : WordTrace (prefixWord ++ tailWord_23811) baseStart_23811 baseEnd_23811 := by
    simpa [prefixWord, tailWord_23811, baseEnd_23811] using wordTrace_append hprefix tailTrace_23811
  have hstable : (prefixWord ++ tailWord_23811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23811).length < 2 ^ (prefixWord ++ tailWord_23811).sum := by decide
  have hdescent : baseEnd_23811 < baseStart_23811 := by decide
  rcases family_descends (prefixWord ++ tailWord_23811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23869 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_23869 : Nat := 118140960795 + 23869 * 2 ^ 59
def prefixEnd_23869 : Nat := 4983230072969 + 3 ^ 40 * 23869 * 2
def baseEnd_23869 : Nat := 12256269742272346127735

theorem tailTrace_23869 : CollatzResearch.WordTrace tailWord_23869 prefixEnd_23869 12256269742272346127735 := by
  unfold tailWord_23869
  simp only [CollatzResearch.WordTrace]
  refine ⟨870573950534164345762661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 580382633689442897175107 870573950534164345762661)
  ·
    refine ⟨163232615725155814830499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 870573950534164345762661 163232615725155814830499)
    ·
      refine ⟨244848923587733722245749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163232615725155814830499 244848923587733722245749)
      ·
        refine ⟨22954586586350036460539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244848923587733722245749 22954586586350036460539)
        ·
          refine ⟨34431879879525054690809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22954586586350036460539 34431879879525054690809)
          ·
            refine ⟨25823909909643791018107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34431879879525054690809 25823909909643791018107)
            ·
              refine ⟨38735864864465686527161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25823909909643791018107 38735864864465686527161)
              ·
                refine ⟨29051898648349264895371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38735864864465686527161 29051898648349264895371)
                ·
                  refine ⟨43577847972523897343057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29051898648349264895371 43577847972523897343057)
                  ·
                    refine ⟨32683385979392923007293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43577847972523897343057 32683385979392923007293)
                    ·
                      refine ⟨12256269742272346127735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 32683385979392923007293 12256269742272346127735)
                      ·
                        rfl

theorem cell23_23869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_23869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23869 prefixEnd_23869 := by exact prefixLift 23869
  have htrace : WordTrace (prefixWord ++ tailWord_23869) baseStart_23869 baseEnd_23869 := by
    simpa [prefixWord, tailWord_23869, baseEnd_23869] using wordTrace_append hprefix tailTrace_23869
  have hstable : (prefixWord ++ tailWord_23869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23869).length < 2 ^ (prefixWord ++ tailWord_23869).sum := by decide
  have hdescent : baseEnd_23869 < baseStart_23869 := by decide
  rcases family_descends (prefixWord ++ tailWord_23869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23891 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5]
def baseStart_23891 : Nat := 118140960795 + 23891 * 2 ^ 59
def prefixEnd_23891 : Nat := 4983230072969 + 3 ^ 40 * 23891 * 2
def baseEnd_23891 : Nat := 12267566316671260052633

theorem tailTrace_23891 : CollatzResearch.WordTrace tailWord_23891 prefixEnd_23891 12267566316671260052633 := by
  unfold tailWord_23891
  simp only [CollatzResearch.WordTrace]
  refine ⟨871376356454462103063527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 580917570969641402042351 871376356454462103063527)
  ·
    refine ⟨1307064534681693154595291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 871376356454462103063527 1307064534681693154595291)
    ·
      refine ⟨1960596802022539731892937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307064534681693154595291 1960596802022539731892937)
      ·
        refine ⟨1470447601516904798919703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960596802022539731892937 1470447601516904798919703)
        ·
          refine ⟨2205671402275357198379555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470447601516904798919703 2205671402275357198379555)
          ·
            refine ⟨3308507103413035797569333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205671402275357198379555 3308507103413035797569333)
            ·
              refine ⟨310172540944972106022125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3308507103413035797569333 310172540944972106022125)
              ·
                refine ⟨116314702854364539758297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310172540944972106022125 116314702854364539758297)
                ·
                  refine ⟨87236027140773404818723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116314702854364539758297 87236027140773404818723)
                  ·
                    refine ⟨130854040711160107228085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87236027140773404818723 130854040711160107228085)
                    ·
                      refine ⟨12267566316671260052633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 130854040711160107228085 12267566316671260052633)
                      ·
                        rfl

theorem cell23_23891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_23891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23891 prefixEnd_23891 := by exact prefixLift 23891
  have htrace : WordTrace (prefixWord ++ tailWord_23891) baseStart_23891 baseEnd_23891 := by
    simpa [prefixWord, tailWord_23891, baseEnd_23891] using wordTrace_append hprefix tailTrace_23891
  have hstable : (prefixWord ++ tailWord_23891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23891).length < 2 ^ (prefixWord ++ tailWord_23891).sum := by decide
  have hdescent : baseEnd_23891 < baseStart_23891 := by decide
  rcases family_descends (prefixWord ++ tailWord_23891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23905 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_23905 : Nat := 118140960795 + 23905 * 2 ^ 59
def prefixEnd_23905 : Nat := 4983230072969 + 3 ^ 40 * 23905 * 2
def baseEnd_23905 : Nat := 12274755045834205277569

theorem tailTrace_23905 : CollatzResearch.WordTrace tailWord_23905 prefixEnd_23905 12274755045834205277569 := by
  unfold tailWord_23905
  simp only [CollatzResearch.WordTrace]
  refine ⟨871886978403742494073169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 581257985602494996048779 871886978403742494073169)
  ·
    refine ⟨653915233802806870554877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 871886978403742494073169 653915233802806870554877)
    ·
      refine ⟨245218212676052576458079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 653915233802806870554877 245218212676052576458079)
      ·
        refine ⟨367827319014078864687119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245218212676052576458079 367827319014078864687119)
        ·
          refine ⟨551740978521118297030679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367827319014078864687119 551740978521118297030679)
          ·
            refine ⟨827611467781677445546019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551740978521118297030679 827611467781677445546019)
            ·
              refine ⟨1241417201672516168319029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827611467781677445546019 1241417201672516168319029)
              ·
                refine ⟨116382862656798390779909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1241417201672516168319029 116382862656798390779909)
                ·
                  refine ⟨21821786748149698271233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116382862656798390779909 21821786748149698271233)
                  ·
                    refine ⟨16366340061112273703425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21821786748149698271233 16366340061112273703425)
                    ·
                      refine ⟨12274755045834205277569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16366340061112273703425 12274755045834205277569)
                      ·
                        rfl

theorem cell23_23905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_23905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23905 prefixEnd_23905 := by exact prefixLift 23905
  have htrace : WordTrace (prefixWord ++ tailWord_23905) baseStart_23905 baseEnd_23905 := by
    simpa [prefixWord, tailWord_23905, baseEnd_23905] using wordTrace_append hprefix tailTrace_23905
  have hstable : (prefixWord ++ tailWord_23905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23905).length < 2 ^ (prefixWord ++ tailWord_23905).sum := by decide
  have hdescent : baseEnd_23905 < baseStart_23905 := by decide
  rcases family_descends (prefixWord ++ tailWord_23905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23908 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_23908 : Nat := 118140960795 + 23908 * 2 ^ 59
def prefixEnd_23908 : Nat := 4983230072969 + 3 ^ 40 * 23908 * 2
def baseEnd_23908 : Nat := 12276295487797693540055

theorem tailTrace_23908 : CollatzResearch.WordTrace tailWord_23908 prefixEnd_23908 12276295487797693540055 := by
  unfold tailWord_23908
  simp only [CollatzResearch.WordTrace]
  refine ⟨435998198696437003216189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 581330931595249337621585 435998198696437003216189)
  ·
    refine ⟨163499324511163876206071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 435998198696437003216189 163499324511163876206071)
    ·
      refine ⟨245248986766745814309107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163499324511163876206071 245248986766745814309107)
      ·
        refine ⟨367873480150118721463661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245248986766745814309107 367873480150118721463661)
        ·
          refine ⟨137952555056294520548873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367873480150118721463661 137952555056294520548873)
          ·
            refine ⟨103464416292220890411655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137952555056294520548873 103464416292220890411655)
            ·
              refine ⟨155196624438331335617483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103464416292220890411655 155196624438331335617483)
              ·
                refine ⟨232794936657497003426225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155196624438331335617483 232794936657497003426225)
                ·
                  refine ⟨174596202493122752569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232794936657497003426225 174596202493122752569669)
                  ·
                    refine ⟨32736787967460516106813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174596202493122752569669 32736787967460516106813)
                    ·
                      refine ⟨12276295487797693540055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 32736787967460516106813 12276295487797693540055)
                      ·
                        rfl

theorem cell23_23908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_23908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23908 prefixEnd_23908 := by exact prefixLift 23908
  have htrace : WordTrace (prefixWord ++ tailWord_23908) baseStart_23908 baseEnd_23908 := by
    simpa [prefixWord, tailWord_23908, baseEnd_23908] using wordTrace_append hprefix tailTrace_23908
  have hstable : (prefixWord ++ tailWord_23908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23908).length < 2 ^ (prefixWord ++ tailWord_23908).sum := by decide
  have hdescent : baseEnd_23908 < baseStart_23908 := by decide
  rcases family_descends (prefixWord ++ tailWord_23908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23922 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_23922 : Nat := 118140960795 + 23922 * 2 ^ 59
def prefixEnd_23922 : Nat := 4983230072969 + 3 ^ 40 * 23922 * 2
def baseEnd_23922 : Nat := 12283484216960638764991

theorem tailTrace_23922 : CollatzResearch.WordTrace tailWord_23922 prefixEnd_23922 12283484216960638764991 := by
  unfold tailWord_23922
  simp only [CollatzResearch.WordTrace]
  refine ⟨218126754835538599360505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 581671346228102931628013 218126754835538599360505)
  ·
    refine ⟨163595066126653949520379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218126754835538599360505 163595066126653949520379)
    ·
      refine ⟨245392599189980924280569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163595066126653949520379 245392599189980924280569)
      ·
        refine ⟨184044449392485693210427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245392599189980924280569 184044449392485693210427)
        ·
          refine ⟨276066674088728539815641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184044449392485693210427 276066674088728539815641)
          ·
            refine ⟨207050005566546404861731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276066674088728539815641 207050005566546404861731)
            ·
              refine ⟨310575008349819607292597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207050005566546404861731 310575008349819607292597)
              ·
                refine ⟨29116407032795588183681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310575008349819607292597 29116407032795588183681)
                ·
                  refine ⟨21837305274596691137761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29116407032795588183681 21837305274596691137761)
                  ·
                    refine ⟨16377978955947518353321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21837305274596691137761 16377978955947518353321)
                    ·
                      refine ⟨12283484216960638764991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16377978955947518353321 12283484216960638764991)
                      ·
                        rfl

theorem cell23_23922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_23922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23922 prefixEnd_23922 := by exact prefixLift 23922
  have htrace : WordTrace (prefixWord ++ tailWord_23922) baseStart_23922 baseEnd_23922 := by
    simpa [prefixWord, tailWord_23922, baseEnd_23922] using wordTrace_append hprefix tailTrace_23922
  have hstable : (prefixWord ++ tailWord_23922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23922).length < 2 ^ (prefixWord ++ tailWord_23922).sum := by decide
  have hdescent : baseEnd_23922 < baseStart_23922 := by decide
  rcases family_descends (prefixWord ++ tailWord_23922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23956 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_23956 : Nat := 118140960795 + 23956 * 2 ^ 59
def prefixEnd_23956 : Nat := 4983230072969 + 3 ^ 40 * 23956 * 2
def baseEnd_23956 : Nat := 12300942559213505739835

theorem tailTrace_23956 : CollatzResearch.WordTrace tailWord_23956 prefixEnd_23956 12300942559213505739835 := by
  unfold tailWord_23956
  simp only [CollatzResearch.WordTrace]
  refine ⟨436873550609489102089861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 582498067479318802786481 436873550609489102089861)
  ·
    refine ⟨81913790739279206641849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 436873550609489102089861 81913790739279206641849)
    ·
      refine ⟨61435343054459404981387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81913790739279206641849 61435343054459404981387)
      ·
        refine ⟨92153014581689107472081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61435343054459404981387 92153014581689107472081)
        ·
          refine ⟨69114760936266830604061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92153014581689107472081 69114760936266830604061)
          ·
            refine ⟨25918035351100061476523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69114760936266830604061 25918035351100061476523)
            ·
              refine ⟨38877053026650092214785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25918035351100061476523 38877053026650092214785)
              ·
                refine ⟨29157789769987569161089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38877053026650092214785 29157789769987569161089)
                ·
                  refine ⟨21868342327490676870817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29157789769987569161089 21868342327490676870817)
                  ·
                    refine ⟨16401256745618007653113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21868342327490676870817 16401256745618007653113)
                    ·
                      refine ⟨12300942559213505739835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16401256745618007653113 12300942559213505739835)
                      ·
                        rfl

theorem cell23_23956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_23956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23956 prefixEnd_23956 := by exact prefixLift 23956
  have htrace : WordTrace (prefixWord ++ tailWord_23956) baseStart_23956 baseEnd_23956 := by
    simpa [prefixWord, tailWord_23956, baseEnd_23956] using wordTrace_append hprefix tailTrace_23956
  have hstable : (prefixWord ++ tailWord_23956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23956).length < 2 ^ (prefixWord ++ tailWord_23956).sum := by decide
  have hdescent : baseEnd_23956 < baseStart_23956 := by decide
  rcases family_descends (prefixWord ++ tailWord_23956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23998 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_23998 : Nat := 118140960795 + 23998 * 2 ^ 59
def prefixEnd_23998 : Nat := 4983230072969 + 3 ^ 40 * 23998 * 2
def baseEnd_23998 : Nat := 12322508746702341414641

theorem tailTrace_23998 : CollatzResearch.WordTrace tailWord_23998 prefixEnd_23998 12322508746702341414641 := by
  unfold tailWord_23998
  simp only [CollatzResearch.WordTrace]
  refine ⟨109409870883352422151081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 583519311377879584805765 109409870883352422151081)
  ·
    refine ⟨82057403162514316613311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109409870883352422151081 82057403162514316613311)
    ·
      refine ⟨123086104743771474919967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82057403162514316613311 123086104743771474919967)
      ·
        refine ⟨184629157115657212379951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123086104743771474919967 184629157115657212379951)
        ·
          refine ⟨276943735673485818569927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184629157115657212379951 276943735673485818569927)
          ·
            refine ⟨415415603510228727854891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276943735673485818569927 415415603510228727854891)
            ·
              refine ⟨623123405265343091782337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415415603510228727854891 623123405265343091782337)
              ·
                refine ⟨467342553949007318836753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623123405265343091782337 467342553949007318836753)
                ·
                  refine ⟨350506915461755489127565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467342553949007318836753 350506915461755489127565)
                  ·
                    refine ⟨131440093298158308422837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350506915461755489127565 131440093298158308422837)
                    ·
                      refine ⟨12322508746702341414641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 131440093298158308422837 12322508746702341414641)
                      ·
                        rfl

theorem cell23_23998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_23998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_23998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_23998 prefixEnd_23998 := by exact prefixLift 23998
  have htrace : WordTrace (prefixWord ++ tailWord_23998) baseStart_23998 baseEnd_23998 := by
    simpa [prefixWord, tailWord_23998, baseEnd_23998] using wordTrace_append hprefix tailTrace_23998
  have hstable : (prefixWord ++ tailWord_23998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23998).length < 2 ^ (prefixWord ++ tailWord_23998).sum := by decide
  have hdescent : baseEnd_23998 < baseStart_23998 := by decide
  rcases family_descends (prefixWord ++ tailWord_23998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24035 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 6]
def baseStart_24035 : Nat := 118140960795 + 24035 * 2 ^ 59
def prefixEnd_24035 : Nat := 4983230072969 + 3 ^ 40 * 24035 * 2
def baseEnd_24035 : Nat := 1371278614546521850219

theorem tailTrace_24035 : CollatzResearch.WordTrace tailWord_24035 prefixEnd_24035 1371278614546521850219 := by
  unfold tailWord_24035
  simp only [CollatzResearch.WordTrace]
  refine ⟨876628467932774696305559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 584418978621849797537039 876628467932774696305559)
  ·
    refine ⟨1314942701899162044458339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876628467932774696305559 1314942701899162044458339)
    ·
      refine ⟨1972414052848743066687509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314942701899162044458339 1972414052848743066687509)
      ·
        refine ⟨92456908727284831250977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1972414052848743066687509 92456908727284831250977)
        ·
          refine ⟨69342681545463623438233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92456908727284831250977 69342681545463623438233)
          ·
            refine ⟨52007011159097717578675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69342681545463623438233 52007011159097717578675)
            ·
              refine ⟨78010516738646576368013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52007011159097717578675 78010516738646576368013)
              ·
                refine ⟨29253943776992466138005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78010516738646576368013 29253943776992466138005)
                ·
                  refine ⟨1371278614546521850219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29253943776992466138005 1371278614546521850219)
                  ·
                    rfl

theorem cell23_24035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 6].length) (baseStart_24035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24035 prefixEnd_24035 := by exact prefixLift 24035
  have htrace : WordTrace (prefixWord ++ tailWord_24035) baseStart_24035 baseEnd_24035 := by
    simpa [prefixWord, tailWord_24035, baseEnd_24035] using wordTrace_append hprefix tailTrace_24035
  have hstable : (prefixWord ++ tailWord_24035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24035).length < 2 ^ (prefixWord ++ tailWord_24035).sum := by decide
  have hdescent : baseEnd_24035 < baseStart_24035 := by decide
  rcases family_descends (prefixWord ++ tailWord_24035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24072 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_24072 : Nat := 118140960795 + 24072 * 2 ^ 59
def prefixEnd_24072 : Nat := 4983230072969 + 3 ^ 40 * 24072 * 2
def baseEnd_24072 : Nat := 12360506315135051889301

theorem tailTrace_24072 : CollatzResearch.WordTrace tailWord_24072 prefixEnd_24072 12360506315135051889301 := by
  unfold tailWord_24072
  simp only [CollatzResearch.WordTrace]
  refine ⟨438988984399365007701235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 585318645865820010268313 438988984399365007701235)
  ·
    refine ⟨658483476599047511551853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438988984399365007701235 658483476599047511551853)
    ·
      refine ⟨246931303724642816831945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 658483476599047511551853 246931303724642816831945)
      ·
        refine ⟨185198477793482112623959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246931303724642816831945 185198477793482112623959)
        ·
          refine ⟨277797716690223168935939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185198477793482112623959 277797716690223168935939)
          ·
            refine ⟨416696575035334753403909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277797716690223168935939 416696575035334753403909)
            ·
              refine ⟨78130607819125266263233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416696575035334753403909 78130607819125266263233)
              ·
                refine ⟨58597955864343949697425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78130607819125266263233 58597955864343949697425)
                ·
                  refine ⟨43948466898257962273069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58597955864343949697425 43948466898257962273069)
                  ·
                    refine ⟨16480675086846735852401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43948466898257962273069 16480675086846735852401)
                    ·
                      refine ⟨12360506315135051889301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16480675086846735852401 12360506315135051889301)
                      ·
                        rfl

theorem cell23_24072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_24072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24072 prefixEnd_24072 := by exact prefixLift 24072
  have htrace : WordTrace (prefixWord ++ tailWord_24072) baseStart_24072 baseEnd_24072 := by
    simpa [prefixWord, tailWord_24072, baseEnd_24072] using wordTrace_append hprefix tailTrace_24072
  have hstable : (prefixWord ++ tailWord_24072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24072).length < 2 ^ (prefixWord ++ tailWord_24072).sum := by decide
  have hdescent : baseEnd_24072 < baseStart_24072 := by decide
  rcases family_descends (prefixWord ++ tailWord_24072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24085 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_24085 : Nat := 118140960795 + 24085 * 2 ^ 59
def prefixEnd_24085 : Nat := 4983230072969 + 3 ^ 40 * 24085 * 2
def baseEnd_24085 : Nat := 12367181563643501026741

theorem tailTrace_24085 : CollatzResearch.WordTrace tailWord_24085 prefixEnd_24085 12367181563643501026741 := by
  unfold tailWord_24085
  simp only [CollatzResearch.WordTrace]
  refine ⟨878452117751633235625709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 585634745167755490417139 878452117751633235625709)
  ·
    refine ⟨329419544156862463359641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 878452117751633235625709 329419544156862463359641)
    ·
      refine ⟨247064658117646847519731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329419544156862463359641 247064658117646847519731)
      ·
        refine ⟨370596987176470271279597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247064658117646847519731 370596987176470271279597)
        ·
          refine ⟨138973870191176351729849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370596987176470271279597 138973870191176351729849)
          ·
            refine ⟨104230402643382263797387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138973870191176351729849 104230402643382263797387)
            ·
              refine ⟨156345603965073395696081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104230402643382263797387 156345603965073395696081)
              ·
                refine ⟨117259202973805046772061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156345603965073395696081 117259202973805046772061)
                ·
                  refine ⟨43972201115176892539523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117259202973805046772061 43972201115176892539523)
                  ·
                    refine ⟨65958301672765338809285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43972201115176892539523 65958301672765338809285)
                    ·
                      refine ⟨12367181563643501026741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 65958301672765338809285 12367181563643501026741)
                      ·
                        rfl

theorem cell23_24085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_24085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24085 prefixEnd_24085 := by exact prefixLift 24085
  have htrace : WordTrace (prefixWord ++ tailWord_24085) baseStart_24085 baseEnd_24085 := by
    simpa [prefixWord, tailWord_24085, baseEnd_24085] using wordTrace_append hprefix tailTrace_24085
  have hstable : (prefixWord ++ tailWord_24085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24085).length < 2 ^ (prefixWord ++ tailWord_24085).sum := by decide
  have hdescent : baseEnd_24085 < baseStart_24085 := by decide
  rcases family_descends (prefixWord ++ tailWord_24085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24115 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4]
def baseStart_24115 : Nat := 118140960795 + 24115 * 2 ^ 59
def prefixEnd_24115 : Nat := 4983230072969 + 3 ^ 40 * 24115 * 2
def baseEnd_24115 : Nat := 12382585983278383651603

theorem tailTrace_24115 : CollatzResearch.WordTrace tailWord_24115 prefixEnd_24115 12382585983278383651603 := by
  unfold tailWord_24115
  simp only [CollatzResearch.WordTrace]
  refine ⟨879546307642948359217799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 586364205095298906145199 879546307642948359217799)
  ·
    refine ⟨1319319461464422538826699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879546307642948359217799 1319319461464422538826699)
    ·
      refine ⟨1978979192196633808240049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319319461464422538826699 1978979192196633808240049)
      ·
        refine ⟨1484234394147475356180037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978979192196633808240049 1484234394147475356180037)
        ·
          refine ⟨278293948902651629283757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1484234394147475356180037 278293948902651629283757)
          ·
            refine ⟨104360230838494360981409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278293948902651629283757 104360230838494360981409)
            ·
              refine ⟨78270173128870770736057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104360230838494360981409 78270173128870770736057)
              ·
                refine ⟨58702629846653078052043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78270173128870770736057 58702629846653078052043)
                ·
                  refine ⟨88053944769979617078065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58702629846653078052043 88053944769979617078065)
                  ·
                    refine ⟨66040458577484712808549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88053944769979617078065 66040458577484712808549)
                    ·
                      refine ⟨12382585983278383651603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 66040458577484712808549 12382585983278383651603)
                      ·
                        rfl

theorem cell23_24115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_24115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24115 prefixEnd_24115 := by exact prefixLift 24115
  have htrace : WordTrace (prefixWord ++ tailWord_24115) baseStart_24115 baseEnd_24115 := by
    simpa [prefixWord, tailWord_24115, baseEnd_24115] using wordTrace_append hprefix tailTrace_24115
  have hstable : (prefixWord ++ tailWord_24115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24115).length < 2 ^ (prefixWord ++ tailWord_24115).sum := by decide
  have hdescent : baseEnd_24115 < baseStart_24115 := by decide
  rcases family_descends (prefixWord ++ tailWord_24115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24119 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 1, 1, 4]
def baseStart_24119 : Nat := 118140960795 + 24119 * 2 ^ 59
def prefixEnd_24119 : Nat := 4983230072969 + 3 ^ 40 * 24119 * 2
def baseEnd_24119 : Nat := 12384639905896368001585

theorem tailTrace_24119 : CollatzResearch.WordTrace tailWord_24119 prefixEnd_24119 12384639905896368001585 := by
  unfold tailWord_24119
  simp only [CollatzResearch.WordTrace]
  refine ⟨879692199628457042363411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 586461466418971361575607 879692199628457042363411)
  ·
    refine ⟨1319538299442685563545117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879692199628457042363411 1319538299442685563545117)
    ·
      refine ⟨494826862291007086329419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1319538299442685563545117 494826862291007086329419)
      ·
        refine ⟨742240293436510629494129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494826862291007086329419 742240293436510629494129)
        ·
          refine ⟨556680220077382972120597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742240293436510629494129 556680220077382972120597)
          ·
            refine ⟨26094385316127326818153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 556680220077382972120597 26094385316127326818153)
            ·
              refine ⟨19570788987095495113615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26094385316127326818153 19570788987095495113615)
              ·
                refine ⟨29356183480643242670423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19570788987095495113615 29356183480643242670423)
                ·
                  refine ⟨44034275220964864005635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29356183480643242670423 44034275220964864005635)
                  ·
                    refine ⟨66051412831447296008453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44034275220964864005635 66051412831447296008453)
                    ·
                      refine ⟨12384639905896368001585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 66051412831447296008453 12384639905896368001585)
                      ·
                        rfl

theorem cell23_24119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_24119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24119 prefixEnd_24119 := by exact prefixLift 24119
  have htrace : WordTrace (prefixWord ++ tailWord_24119) baseStart_24119 baseEnd_24119 := by
    simpa [prefixWord, tailWord_24119, baseEnd_24119] using wordTrace_append hprefix tailTrace_24119
  have hstable : (prefixWord ++ tailWord_24119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24119).length < 2 ^ (prefixWord ++ tailWord_24119).sum := by decide
  have hdescent : baseEnd_24119 < baseStart_24119 := by decide
  rcases family_descends (prefixWord ++ tailWord_24119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24122 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_24122 : Nat := 118140960795 + 24122 * 2 ^ 59
def prefixEnd_24122 : Nat := 4983230072969 + 3 ^ 40 * 24122 * 2
def baseEnd_24122 : Nat := 12386180347859856264071

theorem tailTrace_24122 : CollatzResearch.WordTrace tailWord_24122 prefixEnd_24122 12386180347859856264071 := by
  unfold tailWord_24122
  simp only [CollatzResearch.WordTrace]
  refine ⟨219950404654397138680655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 586534412411725703148413 219950404654397138680655)
  ·
    refine ⟨329925606981595708020983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219950404654397138680655 329925606981595708020983)
    ·
      refine ⟨494888410472393562031475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329925606981595708020983 494888410472393562031475)
      ·
        refine ⟨742332615708590343047213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494888410472393562031475 742332615708590343047213)
        ·
          refine ⟨278374730890721378642705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742332615708590343047213 278374730890721378642705)
          ·
            refine ⟨208781048168041033982029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278374730890721378642705 208781048168041033982029)
            ·
              refine ⟨78292893063015387743261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208781048168041033982029 78292893063015387743261)
              ·
                refine ⟨29359834898630770403723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78292893063015387743261 29359834898630770403723)
                ·
                  refine ⟨44039752347946155605585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29359834898630770403723 44039752347946155605585)
                  ·
                    refine ⟨33029814260959616704189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44039752347946155605585 33029814260959616704189)
                    ·
                      refine ⟨12386180347859856264071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33029814260959616704189 12386180347859856264071)
                      ·
                        rfl

theorem cell23_24122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_24122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24122 prefixEnd_24122 := by exact prefixLift 24122
  have htrace : WordTrace (prefixWord ++ tailWord_24122) baseStart_24122 baseEnd_24122 := by
    simpa [prefixWord, tailWord_24122, baseEnd_24122] using wordTrace_append hprefix tailTrace_24122
  have hstable : (prefixWord ++ tailWord_24122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24122).length < 2 ^ (prefixWord ++ tailWord_24122).sum := by decide
  have hdescent : baseEnd_24122 < baseStart_24122 := by decide
  rcases family_descends (prefixWord ++ tailWord_24122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24125 : List Nat := [1, 4, 1, 3, 3, 1, 10]
def baseStart_24125 : Nat := 118140960795 + 24125 * 2 ^ 59
def prefixEnd_24125 : Nat := 4983230072969 + 3 ^ 40 * 24125 * 2
def baseEnd_24125 : Nat := 152934824565720302797

theorem tailTrace_24125 : CollatzResearch.WordTrace tailWord_24125 prefixEnd_24125 152934824565720302797 := by
  unfold tailWord_24125
  simp only [CollatzResearch.WordTrace]
  refine ⟨879911037606720067081829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 586607358404480044721219 879911037606720067081829)
  ·
    refine ⟨164983319551260012577843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 879911037606720067081829 164983319551260012577843)
    ·
      refine ⟨247474979326890018866765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164983319551260012577843 247474979326890018866765)
      ·
        refine ⟨92803117247583757075037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247474979326890018866765 92803117247583757075037)
        ·
          refine ⟨34801168967843908903139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92803117247583757075037 34801168967843908903139)
          ·
            refine ⟨52201753451765863354709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34801168967843908903139 52201753451765863354709)
            ·
              refine ⟨152934824565720302797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 52201753451765863354709 152934824565720302797)
              ·
                rfl

theorem cell23_24125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 10].length) (baseStart_24125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24125 prefixEnd_24125 := by exact prefixLift 24125
  have htrace : WordTrace (prefixWord ++ tailWord_24125) baseStart_24125 baseEnd_24125 := by
    simpa [prefixWord, tailWord_24125, baseEnd_24125] using wordTrace_append hprefix tailTrace_24125
  have hstable : (prefixWord ++ tailWord_24125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24125).length < 2 ^ (prefixWord ++ tailWord_24125).sum := by decide
  have hdescent : baseEnd_24125 < baseStart_24125 := by decide
  rcases family_descends (prefixWord ++ tailWord_24125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24128 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_24128 : Nat := 118140960795 + 24128 * 2 ^ 59
def prefixEnd_24128 : Nat := 4983230072969 + 3 ^ 40 * 24128 * 2
def baseEnd_24128 : Nat := 12389261231786832789043

theorem tailTrace_24128 : CollatzResearch.WordTrace tailWord_24128 prefixEnd_24128 12389261231786832789043 := by
  unfold tailWord_24128
  simp only [CollatzResearch.WordTrace]
  refine ⟨440010228297925789720519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 586680304397234386294025 440010228297925789720519)
  ·
    refine ⟨660015342446888684580779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 440010228297925789720519 660015342446888684580779)
    ·
      refine ⟨990023013670333026871169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660015342446888684580779 990023013670333026871169)
      ·
        refine ⟨742517260252749770153377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990023013670333026871169 742517260252749770153377)
        ·
          refine ⟨556887945189562327615033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742517260252749770153377 556887945189562327615033)
          ·
            refine ⟨417665958892171745711275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556887945189562327615033 417665958892171745711275)
            ·
              refine ⟨626498938338257618566913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417665958892171745711275 626498938338257618566913)
              ·
                refine ⟨469874203753693213925185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626498938338257618566913 469874203753693213925185)
                ·
                  refine ⟨352405652815269910443889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469874203753693213925185 352405652815269910443889)
                  ·
                    refine ⟨264304239611452432832917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 352405652815269910443889 264304239611452432832917)
                    ·
                      refine ⟨12389261231786832789043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 264304239611452432832917 12389261231786832789043)
                      ·
                        rfl

theorem cell23_24128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_24128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24128 prefixEnd_24128 := by exact prefixLift 24128
  have htrace : WordTrace (prefixWord ++ tailWord_24128) baseStart_24128 baseEnd_24128 := by
    simpa [prefixWord, tailWord_24128, baseEnd_24128] using wordTrace_append hprefix tailTrace_24128
  have hstable : (prefixWord ++ tailWord_24128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24128).length < 2 ^ (prefixWord ++ tailWord_24128).sum := by decide
  have hdescent : baseEnd_24128 < baseStart_24128 := by decide
  rcases family_descends (prefixWord ++ tailWord_24128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24165 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_24165 : Nat := 118140960795 + 24165 * 2 ^ 59
def prefixEnd_24165 : Nat := 4983230072969 + 3 ^ 40 * 24165 * 2
def baseEnd_24165 : Nat := 12408260016003188026373

theorem tailTrace_24165 : CollatzResearch.WordTrace tailWord_24165 prefixEnd_24165 12408260016003188026373 := by
  unfold tailWord_24165
  simp only [CollatzResearch.WordTrace]
  refine ⟨881369957461806898537949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 587579971641204599025299 881369957461806898537949)
  ·
    refine ⟨330513734048177586951731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 881369957461806898537949 330513734048177586951731)
    ·
      refine ⟨495770601072266380427597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330513734048177586951731 495770601072266380427597)
      ·
        refine ⟨185913975402099892660349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495770601072266380427597 185913975402099892660349)
        ·
          refine ⟨69717740775787459747631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185913975402099892660349 69717740775787459747631)
          ·
            refine ⟨104576611163681189621447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69717740775787459747631 104576611163681189621447)
            ·
              refine ⟨156864916745521784432171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104576611163681189621447 156864916745521784432171)
              ·
                refine ⟨235297375118282676648257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156864916745521784432171 235297375118282676648257)
                ·
                  refine ⟨176473031338712007486193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235297375118282676648257 176473031338712007486193)
                  ·
                    refine ⟨132354773504034005614645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176473031338712007486193 132354773504034005614645)
                    ·
                      refine ⟨12408260016003188026373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 132354773504034005614645 12408260016003188026373)
                      ·
                        rfl

theorem cell23_24165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_24165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24165 prefixEnd_24165 := by exact prefixLift 24165
  have htrace : WordTrace (prefixWord ++ tailWord_24165) baseStart_24165 baseEnd_24165 := by
    simpa [prefixWord, tailWord_24165, baseEnd_24165] using wordTrace_append hprefix tailTrace_24165
  have hstable : (prefixWord ++ tailWord_24165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24165).length < 2 ^ (prefixWord ++ tailWord_24165).sum := by decide
  have hdescent : baseEnd_24165 < baseStart_24165 := by decide
  rcases family_descends (prefixWord ++ tailWord_24165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24195 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3]
def baseStart_24195 : Nat := 118140960795 + 24195 * 2 ^ 59
def prefixEnd_24195 : Nat := 4983230072969 + 3 ^ 40 * 24195 * 2
def baseEnd_24195 : Nat := 12423664435638070651235

theorem tailTrace_24195 : CollatzResearch.WordTrace tailWord_24195 prefixEnd_24195 12423664435638070651235 := by
  unfold tailWord_24195
  simp only [CollatzResearch.WordTrace]
  refine ⟨882464147353122022130039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 588309431568748014753359 882464147353122022130039)
  ·
    refine ⟨1323696221029683033195059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882464147353122022130039 1323696221029683033195059)
    ·
      refine ⟨1985544331544524549792589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323696221029683033195059 1985544331544524549792589)
      ·
        refine ⟨744579124329196706172221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1985544331544524549792589 744579124329196706172221)
        ·
          refine ⟨279217171623448764814583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 744579124329196706172221 279217171623448764814583)
          ·
            refine ⟨418825757435173147221875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279217171623448764814583 418825757435173147221875)
            ·
              refine ⟨628238636152759720832813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418825757435173147221875 628238636152759720832813)
              ·
                refine ⟨235589488557284895312305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 628238636152759720832813 235589488557284895312305)
                ·
                  refine ⟨176692116417963671484229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235589488557284895312305 176692116417963671484229)
                  ·
                    refine ⟨33129771828368188403293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176692116417963671484229 33129771828368188403293)
                    ·
                      refine ⟨12423664435638070651235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33129771828368188403293 12423664435638070651235)
                      ·
                        rfl

theorem cell23_24195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_24195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24195 prefixEnd_24195 := by exact prefixLift 24195
  have htrace : WordTrace (prefixWord ++ tailWord_24195) baseStart_24195 baseEnd_24195 := by
    simpa [prefixWord, tailWord_24195, baseEnd_24195] using wordTrace_append hprefix tailTrace_24195
  have hstable : (prefixWord ++ tailWord_24195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24195).length < 2 ^ (prefixWord ++ tailWord_24195).sum := by decide
  have hdescent : baseEnd_24195 < baseStart_24195 := by decide
  rcases family_descends (prefixWord ++ tailWord_24195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24249 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 5]
def baseStart_24249 : Nat := 118140960795 + 24249 * 2 ^ 59
def prefixEnd_24249 : Nat := 4983230072969 + 3 ^ 40 * 24249 * 2
def baseEnd_24249 : Nat := 1383488043442317708443

theorem tailTrace_24249 : CollatzResearch.WordTrace tailWord_24249 prefixEnd_24249 1383488043442317708443 := by
  unfold tailWord_24249
  simp only [CollatzResearch.WordTrace]
  refine ⟨884433689157489244595801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 589622459438326163063867 884433689157489244595801)
  ·
    refine ⟨663325266868116933446851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 884433689157489244595801 663325266868116933446851)
    ·
      refine ⟨994987900302175400170277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663325266868116933446851 994987900302175400170277)
      ·
        refine ⟨186560231306657887531927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 994987900302175400170277 186560231306657887531927)
        ·
          refine ⟨279840346959986831297891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186560231306657887531927 279840346959986831297891)
          ·
            refine ⟨419760520439980246946837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279840346959986831297891 419760520439980246946837)
            ·
              refine ⟨19676274395624074075633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 419760520439980246946837 19676274395624074075633)
              ·
                refine ⟨14757205796718055556725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19676274395624074075633 14757205796718055556725)
                ·
                  refine ⟨1383488043442317708443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14757205796718055556725 1383488043442317708443)
                  ·
                    rfl

theorem cell23_24249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 5].length) (baseStart_24249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24249 prefixEnd_24249 := by exact prefixLift 24249
  have htrace : WordTrace (prefixWord ++ tailWord_24249) baseStart_24249 baseEnd_24249 := by
    simpa [prefixWord, tailWord_24249, baseEnd_24249] using wordTrace_append hprefix tailTrace_24249
  have hstable : (prefixWord ++ tailWord_24249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24249).length < 2 ^ (prefixWord ++ tailWord_24249).sum := by decide
  have hdescent : baseEnd_24249 < baseStart_24249 := by decide
  rcases family_descends (prefixWord ++ tailWord_24249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24255 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_24255 : Nat := 118140960795 + 24255 * 2 ^ 59
def prefixEnd_24255 : Nat := 4983230072969 + 3 ^ 40 * 24255 * 2
def baseEnd_24255 : Nat := 12454473274907835900959

theorem tailTrace_24255 : CollatzResearch.WordTrace tailWord_24255 prefixEnd_24255 12454473274907835900959 := by
  unfold tailWord_24255
  simp only [CollatzResearch.WordTrace]
  refine ⟨884652527135752269314219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 589768351423834846209479 884652527135752269314219)
  ·
    refine ⟨1326978790703628403971329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884652527135752269314219 1326978790703628403971329)
    ·
      refine ⟨995234093027721302978497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1326978790703628403971329 995234093027721302978497)
      ·
        refine ⟨746425569770790977233873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995234093027721302978497 746425569770790977233873)
        ·
          refine ⟨559819177328093232925405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746425569770790977233873 559819177328093232925405)
          ·
            refine ⟨209932191498034962347027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559819177328093232925405 209932191498034962347027)
            ·
              refine ⟨314898287247052443520541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209932191498034962347027 314898287247052443520541)
              ·
                refine ⟨118086857717644666320203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314898287247052443520541 118086857717644666320203)
                ·
                  refine ⟨177130286576466999480305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118086857717644666320203 177130286576466999480305)
                  ·
                    refine ⟨132847714932350249610229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177130286576466999480305 132847714932350249610229)
                    ·
                      refine ⟨12454473274907835900959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 132847714932350249610229 12454473274907835900959)
                      ·
                        rfl

theorem cell23_24255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_24255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24255 prefixEnd_24255 := by exact prefixLift 24255
  have htrace : WordTrace (prefixWord ++ tailWord_24255) baseStart_24255 baseEnd_24255 := by
    simpa [prefixWord, tailWord_24255, baseEnd_24255] using wordTrace_append hprefix tailTrace_24255
  have hstable : (prefixWord ++ tailWord_24255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24255).length < 2 ^ (prefixWord ++ tailWord_24255).sum := by decide
  have hdescent : baseEnd_24255 < baseStart_24255 := by decide
  rcases family_descends (prefixWord ++ tailWord_24255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24282 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_24282 : Nat := 118140960795 + 24282 * 2 ^ 59
def prefixEnd_24282 : Nat := 4983230072969 + 3 ^ 40 * 24282 * 2
def baseEnd_24282 : Nat := 12468337252579230263335

theorem tailTrace_24282 : CollatzResearch.WordTrace tailWord_24282 prefixEnd_24282 12468337252579230263335 := by
  unfold tailWord_24282
  simp only [CollatzResearch.WordTrace]
  refine ⟨221409324509483970136775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 590424865358623920364733 221409324509483970136775)
  ·
    refine ⟨332113986764225955205163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221409324509483970136775 332113986764225955205163)
    ·
      refine ⟨498170980146338932807745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332113986764225955205163 498170980146338932807745)
      ·
        refine ⟨373628235109754199605809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498170980146338932807745 373628235109754199605809)
        ·
          refine ⟨280221176332315649704357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373628235109754199605809 280221176332315649704357)
          ·
            refine ⟨52541470562309184319567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280221176332315649704357 52541470562309184319567)
            ·
              refine ⟨78812205843463776479351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52541470562309184319567 78812205843463776479351)
              ·
                refine ⟨118218308765195664719027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78812205843463776479351 118218308765195664719027)
                ·
                  refine ⟨177327463147793497078541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118218308765195664719027 177327463147793497078541)
                  ·
                    refine ⟨66497798680422561404453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177327463147793497078541 66497798680422561404453)
                    ·
                      refine ⟨12468337252579230263335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 66497798680422561404453 12468337252579230263335)
                      ·
                        rfl

theorem cell23_24282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_24282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24282 prefixEnd_24282 := by exact prefixLift 24282
  have htrace : WordTrace (prefixWord ++ tailWord_24282) baseStart_24282 baseEnd_24282 := by
    simpa [prefixWord, tailWord_24282, baseEnd_24282] using wordTrace_append hprefix tailTrace_24282
  have hstable : (prefixWord ++ tailWord_24282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24282).length < 2 ^ (prefixWord ++ tailWord_24282).sum := by decide
  have hdescent : baseEnd_24282 < baseStart_24282 := by decide
  rcases family_descends (prefixWord ++ tailWord_24282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24292 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_24292 : Nat := 118140960795 + 24292 * 2 ^ 59
def prefixEnd_24292 : Nat := 4983230072969 + 3 ^ 40 * 24292 * 2
def baseEnd_24292 : Nat := 4157824019708063712763

theorem tailTrace_24292 : CollatzResearch.WordTrace tailWord_24292 prefixEnd_24292 4157824019708063712763 := by
  unfold tailWord_24292
  simp only [CollatzResearch.WordTrace]
  refine ⟨443001014000853794205565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 590668018667805058940753 443001014000853794205565)
  ·
    refine ⟨166125380250320172827087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 443001014000853794205565 166125380250320172827087)
    ·
      refine ⟨249188070375480259240631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166125380250320172827087 249188070375480259240631)
      ·
        refine ⟨373782105563220388860947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249188070375480259240631 373782105563220388860947)
        ·
          refine ⟨560673158344830583291421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373782105563220388860947 560673158344830583291421)
          ·
            refine ⟨210252434379311468734283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560673158344830583291421 210252434379311468734283)
            ·
              refine ⟨315378651568967203101425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210252434379311468734283 315378651568967203101425)
              ·
                refine ⟨236533988676725402326069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315378651568967203101425 236533988676725402326069)
                ·
                  refine ⟨22175061438443006468069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236533988676725402326069 22175061438443006468069)
                  ·
                    refine ⟨4157824019708063712763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22175061438443006468069 4157824019708063712763)
                    ·
                      rfl

theorem cell23_24292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_24292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24292 prefixEnd_24292 := by exact prefixLift 24292
  have htrace : WordTrace (prefixWord ++ tailWord_24292) baseStart_24292 baseEnd_24292 := by
    simpa [prefixWord, tailWord_24292, baseEnd_24292] using wordTrace_append hprefix tailTrace_24292
  have hstable : (prefixWord ++ tailWord_24292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24292).length < 2 ^ (prefixWord ++ tailWord_24292).sum := by decide
  have hdescent : baseEnd_24292 < baseStart_24292 := by decide
  rcases family_descends (prefixWord ++ tailWord_24292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24343 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 1, 4]
def baseStart_24343 : Nat := 118140960795 + 24343 * 2 ^ 59
def prefixEnd_24343 : Nat := 4983230072969 + 3 ^ 40 * 24343 * 2
def baseEnd_24343 : Nat := 4166553190834497200185

theorem tailTrace_24343 : CollatzResearch.WordTrace tailWord_24343 prefixEnd_24343 4166553190834497200185 := by
  unfold tailWord_24343
  simp only [CollatzResearch.WordTrace]
  refine ⟨887862150816943298517683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 591908100544628865678455 887862150816943298517683)
  ·
    refine ⟨1331793226225414947776525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887862150816943298517683 1331793226225414947776525)
    ·
      refine ⟨499422459834530605416197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1331793226225414947776525 499422459834530605416197)
      ·
        refine ⟨93641711218974488515537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 499422459834530605416197 93641711218974488515537)
        ·
          refine ⟨70231283414230866386653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93641711218974488515537 70231283414230866386653)
          ·
            refine ⟨26336731280336574894995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70231283414230866386653 26336731280336574894995)
            ·
              refine ⟨39505096920504862342493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26336731280336574894995 39505096920504862342493)
              ·
                refine ⟨14814411345189323378435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39505096920504862342493 14814411345189323378435)
                ·
                  refine ⟨22221617017783985067653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14814411345189323378435 22221617017783985067653)
                  ·
                    refine ⟨4166553190834497200185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22221617017783985067653 4166553190834497200185)
                    ·
                      rfl

theorem cell23_24343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_24343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24343 prefixEnd_24343 := by exact prefixLift 24343
  have htrace : WordTrace (prefixWord ++ tailWord_24343) baseStart_24343 baseEnd_24343 := by
    simpa [prefixWord, tailWord_24343, baseEnd_24343] using wordTrace_append hprefix tailTrace_24343
  have hstable : (prefixWord ++ tailWord_24343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24343).length < 2 ^ (prefixWord ++ tailWord_24343).sum := by decide
  have hdescent : baseEnd_24343 < baseStart_24343 := by decide
  rcases family_descends (prefixWord ++ tailWord_24343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24345 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_24345 : Nat := 118140960795 + 24345 * 2 ^ 59
def prefixEnd_24345 : Nat := 4983230072969 + 3 ^ 40 * 24345 * 2
def baseEnd_24345 : Nat := 12500686533812483775545

theorem tailTrace_24345 : CollatzResearch.WordTrace tailWord_24345 prefixEnd_24345 12500686533812483775545 := by
  unfold tailWord_24345
  simp only [CollatzResearch.WordTrace]
  refine ⟨887935096809697640090489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 591956731206465093393659 887935096809697640090489)
  ·
    refine ⟨665951322607273230067867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 887935096809697640090489 665951322607273230067867)
    ·
      refine ⟨998926983910909845101801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665951322607273230067867 998926983910909845101801)
      ·
        refine ⟨749195237933182383826351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 998926983910909845101801 749195237933182383826351)
        ·
          refine ⟨1123792856899773575739527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749195237933182383826351 1123792856899773575739527)
          ·
            refine ⟨1685689285349660363609291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123792856899773575739527 1685689285349660363609291)
            ·
              refine ⟨2528533928024490545413937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685689285349660363609291 2528533928024490545413937)
              ·
                refine ⟨1896400446018367909060453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528533928024490545413937 1896400446018367909060453)
                ·
                  refine ⟨355575083628443982948835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896400446018367909060453 355575083628443982948835)
                  ·
                    refine ⟨533362625442665974423253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 355575083628443982948835 533362625442665974423253)
                    ·
                      refine ⟨12500686533812483775545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 533362625442665974423253 12500686533812483775545)
                      ·
                        rfl

theorem cell23_24345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_24345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24345 prefixEnd_24345 := by exact prefixLift 24345
  have htrace : WordTrace (prefixWord ++ tailWord_24345) baseStart_24345 baseEnd_24345 := by
    simpa [prefixWord, tailWord_24345, baseEnd_24345] using wordTrace_append hprefix tailTrace_24345
  have hstable : (prefixWord ++ tailWord_24345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24345).length < 2 ^ (prefixWord ++ tailWord_24345).sum := by decide
  have hdescent : baseEnd_24345 < baseStart_24345 := by decide
  rcases family_descends (prefixWord ++ tailWord_24345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24373 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 6]
def baseStart_24373 : Nat := 118140960795 + 24373 * 2 ^ 59
def prefixEnd_24373 : Nat := 4983230072969 + 3 ^ 40 * 24373 * 2
def baseEnd_24373 : Nat := 1390562665793152691713

theorem tailTrace_24373 : CollatzResearch.WordTrace tailWord_24373 prefixEnd_24373 1390562665793152691713 := by
  unfold tailWord_24373
  simp only [CollatzResearch.WordTrace]
  refine ⟨888956340708258422109773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 592637560472172281406515 888956340708258422109773)
  ·
    refine ⟨333358627765596908291165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 888956340708258422109773 333358627765596908291165)
    ·
      refine ⟨125009485412098840609187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333358627765596908291165 125009485412098840609187)
      ·
        refine ⟨187514228118148260913781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125009485412098840609187 187514228118148260913781)
        ·
          refine ⟨17579458886076399460667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187514228118148260913781 17579458886076399460667)
          ·
            refine ⟨26369188329114599191001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17579458886076399460667 26369188329114599191001)
            ·
              refine ⟨19776891246835949393251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26369188329114599191001 19776891246835949393251)
              ·
                refine ⟨29665336870253924089877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19776891246835949393251 29665336870253924089877)
                ·
                  refine ⟨1390562665793152691713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29665336870253924089877 1390562665793152691713)
                  ·
                    rfl

theorem cell23_24373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_24373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24373 prefixEnd_24373 := by exact prefixLift 24373
  have htrace : WordTrace (prefixWord ++ tailWord_24373) baseStart_24373 baseEnd_24373 := by
    simpa [prefixWord, tailWord_24373, baseEnd_24373] using wordTrace_append hprefix tailTrace_24373
  have hstable : (prefixWord ++ tailWord_24373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24373).length < 2 ^ (prefixWord ++ tailWord_24373).sum := by decide
  have hdescent : baseEnd_24373 < baseStart_24373 := by decide
  rcases family_descends (prefixWord ++ tailWord_24373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24412 : List Nat := [2, 2, 4, 2, 13]
def baseStart_24412 : Nat := 118140960795 + 24412 * 2 ^ 59
def prefixEnd_24412 : Nat := 4983230072969 + 3 ^ 40 * 24412 * 2
def baseEnd_24412 : Nat := 17194910476904967953

theorem tailTrace_24412 : CollatzResearch.WordTrace tailWord_24412 prefixEnd_24412 17194910476904967953 := by
  unfold tailWord_24412
  simp only [CollatzResearch.WordTrace]
  refine ⟨445189393783484041389745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 593585858377978721852993 445189393783484041389745)
  ·
    refine ⟨333892045337613031042309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 445189393783484041389745 333892045337613031042309)
    ·
      refine ⟨62604758500802443320433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333892045337613031042309 62604758500802443320433)
      ·
        refine ⟨46953568875601832490325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62604758500802443320433 46953568875601832490325)
        ·
          refine ⟨17194910476904967953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 46953568875601832490325 17194910476904967953)
          ·
            rfl

theorem cell23_24412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 13].length) (baseStart_24412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24412 prefixEnd_24412 := by exact prefixLift 24412
  have htrace : WordTrace (prefixWord ++ tailWord_24412) baseStart_24412 baseEnd_24412 := by
    simpa [prefixWord, tailWord_24412, baseEnd_24412] using wordTrace_append hprefix tailTrace_24412
  have hstable : (prefixWord ++ tailWord_24412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24412).length < 2 ^ (prefixWord ++ tailWord_24412).sum := by decide
  have hdescent : baseEnd_24412 < baseStart_24412 := by decide
  rcases family_descends (prefixWord ++ tailWord_24412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24416 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 2, 4]
def baseStart_24416 : Nat := 118140960795 + 24416 * 2 ^ 59
def prefixEnd_24416 : Nat := 4983230072969 + 3 ^ 40 * 24416 * 2
def baseEnd_24416 : Nat := 4179047886760568662573

theorem tailTrace_24416 : CollatzResearch.WordTrace tailWord_24416 prefixEnd_24416 4179047886760568662573 := by
  unfold tailWord_24416
  simp only [CollatzResearch.WordTrace]
  refine ⟨445262339776238382962551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 593683119701651177283401 445262339776238382962551)
  ·
    refine ⟨667893509664357574443827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445262339776238382962551 667893509664357574443827)
    ·
      refine ⟨1001840264496536361665741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667893509664357574443827 1001840264496536361665741)
      ·
        refine ⟨375690099186201135624653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1001840264496536361665741 375690099186201135624653)
        ·
          refine ⟨140883787194825425859245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375690099186201135624653 140883787194825425859245)
          ·
            refine ⟨52831420198059534697217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140883787194825425859245 52831420198059534697217)
            ·
              refine ⟨39623565148544651022913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52831420198059534697217 39623565148544651022913)
              ·
                refine ⟨29717673861408488267185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39623565148544651022913 29717673861408488267185)
                ·
                  refine ⟨22288255396056366200389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29717673861408488267185 22288255396056366200389)
                  ·
                    refine ⟨4179047886760568662573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22288255396056366200389 4179047886760568662573)
                    ·
                      rfl

theorem cell23_24416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_24416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24416 prefixEnd_24416 := by exact prefixLift 24416
  have htrace : WordTrace (prefixWord ++ tailWord_24416) baseStart_24416 baseEnd_24416 := by
    simpa [prefixWord, tailWord_24416, baseEnd_24416] using wordTrace_append hprefix tailTrace_24416
  have hstable : (prefixWord ++ tailWord_24416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24416).length < 2 ^ (prefixWord ++ tailWord_24416).sum := by decide
  have hdescent : baseEnd_24416 < baseStart_24416 := by decide
  rcases family_descends (prefixWord ++ tailWord_24416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24439 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_24439 : Nat := 118140960795 + 24439 * 2 ^ 59
def prefixEnd_24439 : Nat := 4983230072969 + 3 ^ 40 * 24439 * 2
def baseEnd_24439 : Nat := 12548953715335116000113

theorem tailTrace_24439 : CollatzResearch.WordTrace tailWord_24439 prefixEnd_24439 12548953715335116000113 := by
  unfold tailWord_24439
  simp only [CollatzResearch.WordTrace]
  refine ⟨891363558469151694012371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 594242372312767796008247 891363558469151694012371)
  ·
    refine ⟨1337045337703727541018557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891363558469151694012371 1337045337703727541018557)
    ·
      refine ⟨501392001638897827881959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1337045337703727541018557 501392001638897827881959)
      ·
        refine ⟨752088002458346741822939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501392001638897827881959 752088002458346741822939)
        ·
          refine ⟨1128132003687520112734409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752088002458346741822939 1128132003687520112734409)
          ·
            refine ⟨846099002765640084550807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128132003687520112734409 846099002765640084550807)
            ·
              refine ⟨1269148504148460126826211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846099002765640084550807 1269148504148460126826211)
              ·
                refine ⟨1903722756222690190239317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269148504148460126826211 1903722756222690190239317)
                ·
                  refine ⟨22309251049484650666867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1903722756222690190239317 22309251049484650666867)
                  ·
                    refine ⟨33463876574226976000301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22309251049484650666867 33463876574226976000301)
                    ·
                      refine ⟨12548953715335116000113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33463876574226976000301 12548953715335116000113)
                      ·
                        rfl

theorem cell23_24439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_24439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24439 prefixEnd_24439 := by exact prefixLift 24439
  have htrace : WordTrace (prefixWord ++ tailWord_24439) baseStart_24439 baseEnd_24439 := by
    simpa [prefixWord, tailWord_24439, baseEnd_24439] using wordTrace_append hprefix tailTrace_24439
  have hstable : (prefixWord ++ tailWord_24439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24439).length < 2 ^ (prefixWord ++ tailWord_24439).sum := by decide
  have hdescent : baseEnd_24439 < baseStart_24439 := by decide
  rcases family_descends (prefixWord ++ tailWord_24439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24529 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_24529 : Nat := 118140960795 + 24529 * 2 ^ 59
def prefixEnd_24529 : Nat := 4983230072969 + 3 ^ 40 * 24529 * 2
def baseEnd_24529 : Nat := 12595166974239763874699

theorem tailTrace_24529 : CollatzResearch.WordTrace tailWord_24529 prefixEnd_24529 12595166974239763874699 := by
  unfold tailWord_24529
  simp only [CollatzResearch.WordTrace]
  refine ⟨894646128143097064788641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 596430752095398043192427 894646128143097064788641)
  ·
    refine ⟨670984596107322798591481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 894646128143097064788641 670984596107322798591481)
    ·
      refine ⟨503238447080492098943611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 670984596107322798591481 503238447080492098943611)
      ·
        refine ⟨754857670620738148415417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503238447080492098943611 754857670620738148415417)
        ·
          refine ⟨566143252965553611311563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754857670620738148415417 566143252965553611311563)
          ·
            refine ⟨849214879448330416967345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566143252965553611311563 849214879448330416967345)
            ·
              refine ⟨636911159586247812725509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849214879448330416967345 636911159586247812725509)
              ·
                refine ⟨119420842422421464886033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636911159586247812725509 119420842422421464886033)
                ·
                  refine ⟨89565631816816098664525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119420842422421464886033 89565631816816098664525)
                  ·
                    refine ⟨33587111931306036999197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89565631816816098664525 33587111931306036999197)
                    ·
                      refine ⟨12595166974239763874699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33587111931306036999197 12595166974239763874699)
                      ·
                        rfl

theorem cell23_24529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_24529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24529 prefixEnd_24529 := by exact prefixLift 24529
  have htrace : WordTrace (prefixWord ++ tailWord_24529) baseStart_24529 baseEnd_24529 := by
    simpa [prefixWord, tailWord_24529, baseEnd_24529] using wordTrace_append hprefix tailTrace_24529
  have hstable : (prefixWord ++ tailWord_24529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24529).length < 2 ^ (prefixWord ++ tailWord_24529).sum := by decide
  have hdescent : baseEnd_24529 < baseStart_24529 := by decide
  rcases family_descends (prefixWord ++ tailWord_24529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24547 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 2, 2, 2]
def baseStart_24547 : Nat := 118140960795 + 24547 * 2 ^ 59
def prefixEnd_24547 : Nat := 4983230072969 + 3 ^ 40 * 24547 * 2
def baseEnd_24547 : Nat := 12604409626020693449617

theorem tailTrace_24547 : CollatzResearch.WordTrace tailWord_24547 prefixEnd_24547 12604409626020693449617 := by
  unfold tailWord_24547
  simp only [CollatzResearch.WordTrace]
  refine ⟨895302642077886138943895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 596868428051924092629263 895302642077886138943895)
  ·
    refine ⟨1342953963116829208415843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 895302642077886138943895 1342953963116829208415843)
    ·
      refine ⟨2014430944675243812623765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342953963116829208415843 2014430944675243812623765)
      ·
        refine ⟨94426450531652053716739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2014430944675243812623765 94426450531652053716739)
        ·
          refine ⟨141639675797478080575109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94426450531652053716739 141639675797478080575109)
          ·
            refine ⟨26557439212027140107833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141639675797478080575109 26557439212027140107833)
            ·
              refine ⟨19918079409020355080875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26557439212027140107833 19918079409020355080875)
              ·
                refine ⟨29877119113530532621313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19918079409020355080875 29877119113530532621313)
                ·
                  refine ⟨22407839335147899465985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29877119113530532621313 22407839335147899465985)
                  ·
                    refine ⟨16805879501360924599489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22407839335147899465985 16805879501360924599489)
                    ·
                      refine ⟨12604409626020693449617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16805879501360924599489 12604409626020693449617)
                      ·
                        rfl

theorem cell23_24547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_24547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24547 prefixEnd_24547 := by exact prefixLift 24547
  have htrace : WordTrace (prefixWord ++ tailWord_24547) baseStart_24547 baseEnd_24547 := by
    simpa [prefixWord, tailWord_24547, baseEnd_24547] using wordTrace_append hprefix tailTrace_24547
  have hstable : (prefixWord ++ tailWord_24547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24547).length < 2 ^ (prefixWord ++ tailWord_24547).sum := by decide
  have hdescent : baseEnd_24547 < baseStart_24547 := by decide
  rcases family_descends (prefixWord ++ tailWord_24547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24619 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 3]
def baseStart_24619 : Nat := 118140960795 + 24619 * 2 ^ 59
def prefixEnd_24619 : Nat := 4983230072969 + 3 ^ 40 * 24619 * 2
def baseEnd_24619 : Nat := 12641380233144411749285

theorem tailTrace_24619 : CollatzResearch.WordTrace tailWord_24619 prefixEnd_24619 12641380233144411749285 := by
  unfold tailWord_24619
  simp only [CollatzResearch.WordTrace]
  refine ⟨897928697817042435564911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 598619131878028290376607 897928697817042435564911)
  ·
    refine ⟨1346893046725563653347367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897928697817042435564911 1346893046725563653347367)
    ·
      refine ⟨2020339570088345480021051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346893046725563653347367 2020339570088345480021051)
      ·
        refine ⟨3030509355132518220031577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020339570088345480021051 3030509355132518220031577)
        ·
          refine ⟨2272882016349388665023683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3030509355132518220031577 2272882016349388665023683)
          ·
            refine ⟨3409323024524082997535525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272882016349388665023683 3409323024524082997535525)
            ·
              refine ⟨639248067098265562037911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3409323024524082997535525 639248067098265562037911)
              ·
                refine ⟨958872100647398343056867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639248067098265562037911 958872100647398343056867)
                ·
                  refine ⟨1438308150971097514585301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958872100647398343056867 1438308150971097514585301)
                  ·
                    refine ⟨33710347288385097998093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1438308150971097514585301 33710347288385097998093)
                    ·
                      refine ⟨12641380233144411749285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33710347288385097998093 12641380233144411749285)
                      ·
                        rfl

theorem cell23_24619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 3].length) (baseStart_24619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24619 prefixEnd_24619 := by exact prefixLift 24619
  have htrace : WordTrace (prefixWord ++ tailWord_24619) baseStart_24619 baseEnd_24619 := by
    simpa [prefixWord, tailWord_24619, baseEnd_24619] using wordTrace_append hprefix tailTrace_24619
  have hstable : (prefixWord ++ tailWord_24619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24619).length < 2 ^ (prefixWord ++ tailWord_24619).sum := by decide
  have hdescent : baseEnd_24619 < baseStart_24619 := by decide
  rcases family_descends (prefixWord ++ tailWord_24619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24676 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_24676 : Nat := 118140960795 + 24676 * 2 ^ 59
def prefixEnd_24676 : Nat := 4983230072969 + 3 ^ 40 * 24676 * 2
def baseEnd_24676 : Nat := 12670648630450688736523

theorem tailTrace_24676 : CollatzResearch.WordTrace tailWord_24676 prefixEnd_24676 12670648630450688736523 := by
  unfold tailWord_24676
  simp only [CollatzResearch.WordTrace]
  refine ⟨450003829305270585194941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 600005105740360780259921 450003829305270585194941)
  ·
    refine ⟨168751435989476469448103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 450003829305270585194941 168751435989476469448103)
    ·
      refine ⟨253127153984214704172155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168751435989476469448103 253127153984214704172155)
      ·
        refine ⟨379690730976322056258233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253127153984214704172155 379690730976322056258233)
        ·
          refine ⟨284768048232241542193675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379690730976322056258233 284768048232241542193675)
          ·
            refine ⟨427152072348362313290513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284768048232241542193675 427152072348362313290513)
            ·
              refine ⟨320364054261271734967885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427152072348362313290513 320364054261271734967885)
              ·
                refine ⟨120136520347976900612957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320364054261271734967885 120136520347976900612957)
                ·
                  refine ⟨45051195130491337729859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120136520347976900612957 45051195130491337729859)
                  ·
                    refine ⟨67576792695737006594789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45051195130491337729859 67576792695737006594789)
                    ·
                      refine ⟨12670648630450688736523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 67576792695737006594789 12670648630450688736523)
                      ·
                        rfl

theorem cell23_24676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_24676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24676 prefixEnd_24676 := by exact prefixLift 24676
  have htrace : WordTrace (prefixWord ++ tailWord_24676) baseStart_24676 baseEnd_24676 := by
    simpa [prefixWord, tailWord_24676, baseEnd_24676] using wordTrace_append hprefix tailTrace_24676
  have hstable : (prefixWord ++ tailWord_24676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24676).length < 2 ^ (prefixWord ++ tailWord_24676).sum := by decide
  have hdescent : baseEnd_24676 < baseStart_24676 := by decide
  rcases family_descends (prefixWord ++ tailWord_24676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24686 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_24686 : Nat := 118140960795 + 24686 * 2 ^ 59
def prefixEnd_24686 : Nat := 4983230072969 + 3 ^ 40 * 24686 * 2
def baseEnd_24686 : Nat := 4225261145665216537159

theorem tailTrace_24686 : CollatzResearch.WordTrace tailWord_24686 prefixEnd_24686 4225261145665216537159 := by
  unfold tailWord_24686
  simp only [CollatzResearch.WordTrace]
  refine ⟨112546548571789109781739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 600248259049541918835941 112546548571789109781739)
  ·
    refine ⟨168819822857683664672609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112546548571789109781739 168819822857683664672609)
    ·
      refine ⟨126614867143262748504457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168819822857683664672609 126614867143262748504457)
      ·
        refine ⟨94961150357447061378343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126614867143262748504457 94961150357447061378343)
        ·
          refine ⟨142441725536170592067515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94961150357447061378343 142441725536170592067515)
          ·
            refine ⟨213662588304255888101273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142441725536170592067515 213662588304255888101273)
            ·
              refine ⟨160246941228191916075955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213662588304255888101273 160246941228191916075955)
              ·
                refine ⟨240370411842287874113933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160246941228191916075955 240370411842287874113933)
                ·
                  refine ⟨90138904440857952792725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240370411842287874113933 90138904440857952792725)
                  ·
                    refine ⟨4225261145665216537159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90138904440857952792725 4225261145665216537159)
                    ·
                      rfl

theorem cell23_24686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_24686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24686 prefixEnd_24686 := by exact prefixLift 24686
  have htrace : WordTrace (prefixWord ++ tailWord_24686) baseStart_24686 baseEnd_24686 := by
    simpa [prefixWord, tailWord_24686, baseEnd_24686] using wordTrace_append hprefix tailTrace_24686
  have hstable : (prefixWord ++ tailWord_24686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24686).length < 2 ^ (prefixWord ++ tailWord_24686).sum := by decide
  have hdescent : baseEnd_24686 < baseStart_24686 := by decide
  rcases family_descends (prefixWord ++ tailWord_24686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24687 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 1, 1, 3]
def baseStart_24687 : Nat := 118140960795 + 24687 * 2 ^ 59
def prefixEnd_24687 : Nat := 4983230072969 + 3 ^ 40 * 24687 * 2
def baseEnd_24687 : Nat := 12676296917650145698973

theorem tailTrace_24687 : CollatzResearch.WordTrace tailWord_24687 prefixEnd_24687 12676296917650145698973 := by
  unfold tailWord_24687
  simp only [CollatzResearch.WordTrace]
  refine ⟨900408861570690049040315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 600272574380460032693543 900408861570690049040315)
  ·
    refine ⟨1350613292356035073560473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 900408861570690049040315 1350613292356035073560473)
    ·
      refine ⟨1012959969267026305170355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1350613292356035073560473 1012959969267026305170355)
      ·
        refine ⟨1519439953900539457755533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012959969267026305170355 1519439953900539457755533)
        ·
          refine ⟨569789982712702296658325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1519439953900539457755533 569789982712702296658325)
          ·
            refine ⟨26708905439657920155859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 569789982712702296658325 26708905439657920155859)
            ·
              refine ⟨40063358159486880233789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26708905439657920155859 40063358159486880233789)
              ·
                refine ⟨15023759309807580087671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40063358159486880233789 15023759309807580087671)
                ·
                  refine ⟨22535638964711370131507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15023759309807580087671 22535638964711370131507)
                  ·
                    refine ⟨33803458447067055197261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22535638964711370131507 33803458447067055197261)
                    ·
                      refine ⟨12676296917650145698973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33803458447067055197261 12676296917650145698973)
                      ·
                        rfl

theorem cell23_24687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 1, 3].length) (baseStart_24687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24687 prefixEnd_24687 := by exact prefixLift 24687
  have htrace : WordTrace (prefixWord ++ tailWord_24687) baseStart_24687 baseEnd_24687 := by
    simpa [prefixWord, tailWord_24687, baseEnd_24687] using wordTrace_append hprefix tailTrace_24687
  have hstable : (prefixWord ++ tailWord_24687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24687).length < 2 ^ (prefixWord ++ tailWord_24687).sum := by decide
  have hdescent : baseEnd_24687 < baseStart_24687 := by decide
  rcases family_descends (prefixWord ++ tailWord_24687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24696 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_24696 : Nat := 118140960795 + 24696 * 2 ^ 59
def prefixEnd_24696 : Nat := 4983230072969 + 3 ^ 40 * 24696 * 2
def baseEnd_24696 : Nat := 12680918243540610486431

theorem tailTrace_24696 : CollatzResearch.WordTrace tailWord_24696 prefixEnd_24696 12680918243540610486431 := by
  unfold tailWord_24696
  simp only [CollatzResearch.WordTrace]
  refine ⟨450368559269042293058971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 600491412358723057411961 450368559269042293058971)
  ·
    refine ⟨675552838903563439588457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450368559269042293058971 675552838903563439588457)
    ·
      refine ⟨506664629177672579691343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675552838903563439588457 506664629177672579691343)
      ·
        refine ⟨759996943766508869537015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506664629177672579691343 759996943766508869537015)
        ·
          refine ⟨1139995415649763304305523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759996943766508869537015 1139995415649763304305523)
          ·
            refine ⟨1709993123474644956458285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139995415649763304305523 1709993123474644956458285)
            ·
              refine ⟨641247421302991858671857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1709993123474644956458285 641247421302991858671857)
              ·
                refine ⟨480935565977243894003893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641247421302991858671857 480935565977243894003893)
                ·
                  refine ⟨45087709310366615062865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480935565977243894003893 45087709310366615062865)
                  ·
                    refine ⟨33815781982774961297149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45087709310366615062865 33815781982774961297149)
                    ·
                      refine ⟨12680918243540610486431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33815781982774961297149 12680918243540610486431)
                      ·
                        rfl

theorem cell23_24696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_24696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24696 prefixEnd_24696 := by exact prefixLift 24696
  have htrace : WordTrace (prefixWord ++ tailWord_24696) baseStart_24696 baseEnd_24696 := by
    simpa [prefixWord, tailWord_24696, baseEnd_24696] using wordTrace_append hprefix tailTrace_24696
  have hstable : (prefixWord ++ tailWord_24696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24696).length < 2 ^ (prefixWord ++ tailWord_24696).sum := by decide
  have hdescent : baseEnd_24696 < baseStart_24696 := by decide
  rcases family_descends (prefixWord ++ tailWord_24696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24724 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_24724 : Nat := 118140960795 + 24724 * 2 ^ 59
def prefixEnd_24724 : Nat := 4983230072969 + 3 ^ 40 * 24724 * 2
def baseEnd_24724 : Nat := 4231765233955500312101

theorem tailTrace_24724 : CollatzResearch.WordTrace tailWord_24724 prefixEnd_24724 4231765233955500312101 := by
  unfold tailWord_24724
  simp only [CollatzResearch.WordTrace]
  refine ⟨450879181218322684068613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 601172241624430245424817 450879181218322684068613)
  ·
    refine ⟨84539846478435503262865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 450879181218322684068613 84539846478435503262865)
    ·
      refine ⟨63404884858826627447149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84539846478435503262865 63404884858826627447149)
      ·
        refine ⟨23776831822059985292681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63404884858826627447149 23776831822059985292681)
        ·
          refine ⟨17832623866544988969511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23776831822059985292681 17832623866544988969511)
          ·
            refine ⟨26748935799817483454267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17832623866544988969511 26748935799817483454267)
            ·
              refine ⟨40123403699726225181401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26748935799817483454267 40123403699726225181401)
              ·
                refine ⟨30092552774794668886051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40123403699726225181401 30092552774794668886051)
                ·
                  refine ⟨45138829162192003329077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30092552774794668886051 45138829162192003329077)
                  ·
                    refine ⟨4231765233955500312101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45138829162192003329077 4231765233955500312101)
                    ·
                      rfl

theorem cell23_24724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_24724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24724 prefixEnd_24724 := by exact prefixLift 24724
  have htrace : WordTrace (prefixWord ++ tailWord_24724) baseStart_24724 baseEnd_24724 := by
    simpa [prefixWord, tailWord_24724, baseEnd_24724] using wordTrace_append hprefix tailTrace_24724
  have hstable : (prefixWord ++ tailWord_24724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24724).length < 2 ^ (prefixWord ++ tailWord_24724).sum := by decide
  have hdescent : baseEnd_24724 < baseStart_24724 := by decide
  rcases family_descends (prefixWord ++ tailWord_24724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24727 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 1, 1, 4]
def baseStart_24727 : Nat := 118140960795 + 24727 * 2 ^ 59
def prefixEnd_24727 : Nat := 4983230072969 + 3 ^ 40 * 24727 * 2
def baseEnd_24727 : Nat := 12696836143829989198789

theorem tailTrace_24727 : CollatzResearch.WordTrace tailWord_24727 prefixEnd_24727 12696836143829989198789 := by
  unfold tailWord_24727
  simp only [CollatzResearch.WordTrace]
  refine ⟨901867781425776880496435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 601245187617184586997623 901867781425776880496435)
  ·
    refine ⟨1352801672138665320744653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 901867781425776880496435 1352801672138665320744653)
    ·
      refine ⟨507300627051999495279245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1352801672138665320744653 507300627051999495279245)
      ·
        refine ⟨190237735144499810729717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507300627051999495279245 190237735144499810729717)
        ·
          refine ⟨17834787669796857255911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190237735144499810729717 17834787669796857255911)
          ·
            refine ⟨26752181504695285883867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17834787669796857255911 26752181504695285883867)
            ·
              refine ⟨40128272257042928825801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26752181504695285883867 40128272257042928825801)
              ·
                refine ⟨30096204192782196619351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40128272257042928825801 30096204192782196619351)
                ·
                  refine ⟨45144306289173294929027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30096204192782196619351 45144306289173294929027)
                  ·
                    refine ⟨67716459433759942393541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45144306289173294929027 67716459433759942393541)
                    ·
                      refine ⟨12696836143829989198789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 67716459433759942393541 12696836143829989198789)
                      ·
                        rfl

theorem cell23_24727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_24727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24727 prefixEnd_24727 := by exact prefixLift 24727
  have htrace : WordTrace (prefixWord ++ tailWord_24727) baseStart_24727 baseEnd_24727 := by
    simpa [prefixWord, tailWord_24727, baseEnd_24727] using wordTrace_append hprefix tailTrace_24727
  have hstable : (prefixWord ++ tailWord_24727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24727).length < 2 ^ (prefixWord ++ tailWord_24727).sum := by decide
  have hdescent : baseEnd_24727 < baseStart_24727 := by decide
  rcases family_descends (prefixWord ++ tailWord_24727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24730 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_24730 : Nat := 118140960795 + 24730 * 2 ^ 59
def prefixEnd_24730 : Nat := 4983230072969 + 3 ^ 40 * 24730 * 2
def baseEnd_24730 : Nat := 12698376585793477461275

theorem tailTrace_24730 : CollatzResearch.WordTrace tailWord_24730 prefixEnd_24730 12698376585793477461275 := by
  unfold tailWord_24730
  simp only [CollatzResearch.WordTrace]
  refine ⟨225494300103727098213911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 601318133609938928570429 225494300103727098213911)
  ·
    refine ⟨338241450155590647320867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225494300103727098213911 338241450155590647320867)
    ·
      refine ⟨507362175233385970981301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338241450155590647320867 507362175233385970981301)
      ·
        refine ⟨47565203928129934779497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 507362175233385970981301 47565203928129934779497)
        ·
          refine ⟨35673902946097451084623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47565203928129934779497 35673902946097451084623)
          ·
            refine ⟨53510854419146176626935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35673902946097451084623 53510854419146176626935)
            ·
              refine ⟨80266281628719264940403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53510854419146176626935 80266281628719264940403)
              ·
                refine ⟨120399422443078897410605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80266281628719264940403 120399422443078897410605)
                ·
                  refine ⟨45149783416154586528977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120399422443078897410605 45149783416154586528977)
                  ·
                    refine ⟨33862337562115939896733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45149783416154586528977 33862337562115939896733)
                    ·
                      refine ⟨12698376585793477461275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33862337562115939896733 12698376585793477461275)
                      ·
                        rfl

theorem cell23_24730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_24730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24730 prefixEnd_24730 := by exact prefixLift 24730
  have htrace : WordTrace (prefixWord ++ tailWord_24730) baseStart_24730 baseEnd_24730 := by
    simpa [prefixWord, tailWord_24730, baseEnd_24730] using wordTrace_append hprefix tailTrace_24730
  have hstable : (prefixWord ++ tailWord_24730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24730).length < 2 ^ (prefixWord ++ tailWord_24730).sum := by decide
  have hdescent : baseEnd_24730 < baseStart_24730 := by decide
  rcases family_descends (prefixWord ++ tailWord_24730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24750 : List Nat := [4, 1, 4, 2, 2, 10]
def baseStart_24750 : Nat := 118140960795 + 24750 * 2 ^ 59
def prefixEnd_24750 : Nat := 4983230072969 + 3 ^ 40 * 24750 * 2
def baseEnd_24750 : Nat := 52298955550960490581

theorem tailTrace_24750 : CollatzResearch.WordTrace tailWord_24750 prefixEnd_24750 52298955550960490581 := by
  unfold tailWord_24750
  simp only [CollatzResearch.WordTrace]
  refine ⟨112838332542806476072963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 601804440228301205722469 112838332542806476072963)
  ·
    refine ⟨169257498814209714109445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112838332542806476072963 169257498814209714109445)
    ·
      refine ⟨31735781027664321395521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169257498814209714109445 31735781027664321395521)
      ·
        refine ⟨23801835770748241046641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31735781027664321395521 23801835770748241046641)
        ·
          refine ⟨17851376828061180784981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23801835770748241046641 17851376828061180784981)
          ·
            refine ⟨52298955550960490581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 17851376828061180784981 52298955550960490581)
            ·
              rfl

theorem cell23_24750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 10].length) (baseStart_24750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24750 prefixEnd_24750 := by exact prefixLift 24750
  have htrace : WordTrace (prefixWord ++ tailWord_24750) baseStart_24750 baseEnd_24750 := by
    simpa [prefixWord, tailWord_24750, baseEnd_24750] using wordTrace_append hprefix tailTrace_24750
  have hstable : (prefixWord ++ tailWord_24750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24750).length < 2 ^ (prefixWord ++ tailWord_24750).sum := by decide
  have hdescent : baseEnd_24750 < baseStart_24750 := by decide
  rcases family_descends (prefixWord ++ tailWord_24750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24760 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_24760 : Nat := 118140960795 + 24760 * 2 ^ 59
def prefixEnd_24760 : Nat := 4983230072969 + 3 ^ 40 * 24760 * 2
def baseEnd_24760 : Nat := 12713781005428360086137

theorem tailTrace_24760 : CollatzResearch.WordTrace tailWord_24760 prefixEnd_24760 12713781005428360086137 := by
  unfold tailWord_24760
  simp only [CollatzResearch.WordTrace]
  refine ⟨451535695153111758223867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 602047593537482344298489 451535695153111758223867)
  ·
    refine ⟨677303542729667637335801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451535695153111758223867 677303542729667637335801)
    ·
      refine ⟨507977657047250728001851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677303542729667637335801 507977657047250728001851)
      ·
        refine ⟨761966485570876092002777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507977657047250728001851 761966485570876092002777)
        ·
          refine ⟨571474864178157069002083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761966485570876092002777 571474864178157069002083)
          ·
            refine ⟨857212296267235603503125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571474864178157069002083 857212296267235603503125)
            ·
              refine ⟨40181826387526668914209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 857212296267235603503125 40181826387526668914209)
              ·
                refine ⟨30136369790645001685657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40181826387526668914209 30136369790645001685657)
                ·
                  refine ⟨22602277342983751264243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30136369790645001685657 22602277342983751264243)
                  ·
                    refine ⟨33903416014475626896365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22602277342983751264243 33903416014475626896365)
                    ·
                      refine ⟨12713781005428360086137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 33903416014475626896365 12713781005428360086137)
                      ·
                        rfl

theorem cell23_24760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_24760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24760 prefixEnd_24760 := by exact prefixLift 24760
  have htrace : WordTrace (prefixWord ++ tailWord_24760) baseStart_24760 baseEnd_24760 := by
    simpa [prefixWord, tailWord_24760, baseEnd_24760] using wordTrace_append hprefix tailTrace_24760
  have hstable : (prefixWord ++ tailWord_24760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24760).length < 2 ^ (prefixWord ++ tailWord_24760).sum := by decide
  have hdescent : baseEnd_24760 < baseStart_24760 := by decide
  rcases family_descends (prefixWord ++ tailWord_24760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24800 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 4, 2, 2]
def baseStart_24800 : Nat := 118140960795 + 24800 * 2 ^ 59
def prefixEnd_24800 : Nat := 4983230072969 + 3 ^ 40 * 24800 * 2
def baseEnd_24800 : Nat := 12734320231608203585953

theorem tailTrace_24800 : CollatzResearch.WordTrace tailWord_24800 prefixEnd_24800 12734320231608203585953 := by
  unfold tailWord_24800
  simp only [CollatzResearch.WordTrace]
  refine ⟨452265155080655173951927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 603020206774206898602569 452265155080655173951927)
  ·
    refine ⟨678397732620982760927891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 452265155080655173951927 678397732620982760927891)
    ·
      refine ⟨1017596598931474141391837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678397732620982760927891 1017596598931474141391837)
      ·
        refine ⟨381598724599302803021939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1017596598931474141391837 381598724599302803021939)
        ·
          refine ⟨572398086898954204532909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381598724599302803021939 572398086898954204532909)
          ·
            refine ⟨214649282587107826699841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572398086898954204532909 214649282587107826699841)
            ·
              refine ⟨160986961940330870024881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214649282587107826699841 160986961940330870024881)
              ·
                refine ⟨120740221455248152518661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160986961940330870024881 120740221455248152518661)
                ·
                  refine ⟨22638791522859028597249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120740221455248152518661 22638791522859028597249)
                  ·
                    refine ⟨16979093642144271447937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22638791522859028597249 16979093642144271447937)
                    ·
                      refine ⟨12734320231608203585953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16979093642144271447937 12734320231608203585953)
                      ·
                        rfl

theorem cell23_24800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_24800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24800 prefixEnd_24800 := by exact prefixLift 24800
  have htrace : WordTrace (prefixWord ++ tailWord_24800) baseStart_24800 baseEnd_24800 := by
    simpa [prefixWord, tailWord_24800, baseEnd_24800] using wordTrace_append hprefix tailTrace_24800
  have hstable : (prefixWord ++ tailWord_24800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24800).length < 2 ^ (prefixWord ++ tailWord_24800).sum := by decide
  have hdescent : baseEnd_24800 < baseStart_24800 := by decide
  rcases family_descends (prefixWord ++ tailWord_24800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24817 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 2, 2, 2]
def baseStart_24817 : Nat := 118140960795 + 24817 * 2 ^ 59
def prefixEnd_24817 : Nat := 4983230072969 + 3 ^ 40 * 24817 * 2
def baseEnd_24817 : Nat := 12743049402734637073375

theorem tailTrace_24817 : CollatzResearch.WordTrace tailWord_24817 prefixEnd_24817 12743049402734637073375 := by
  unfold tailWord_24817
  simp only [CollatzResearch.WordTrace]
  refine ⟨905150351099722251272705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 603433567399814834181803 905150351099722251272705)
  ·
    refine ⟨678862763324791688454529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 905150351099722251272705 678862763324791688454529)
    ·
      refine ⟨509147072493593766340897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678862763324791688454529 509147072493593766340897)
      ·
        refine ⟨381860304370195324755673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509147072493593766340897 381860304370195324755673)
        ·
          refine ⟨286395228277646493566755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381860304370195324755673 286395228277646493566755)
          ·
            refine ⟨429592842416469740350133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286395228277646493566755 429592842416469740350133)
            ·
              refine ⟨40274328976544038157825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 429592842416469740350133 40274328976544038157825)
              ·
                refine ⟨30205746732408028618369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40274328976544038157825 30205746732408028618369)
                ·
                  refine ⟨22654310049306021463777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30205746732408028618369 22654310049306021463777)
                  ·
                    refine ⟨16990732536979516097833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22654310049306021463777 16990732536979516097833)
                    ·
                      refine ⟨12743049402734637073375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 16990732536979516097833 12743049402734637073375)
                      ·
                        rfl

theorem cell23_24817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_24817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24817 prefixEnd_24817 := by exact prefixLift 24817
  have htrace : WordTrace (prefixWord ++ tailWord_24817) baseStart_24817 baseEnd_24817 := by
    simpa [prefixWord, tailWord_24817, baseEnd_24817] using wordTrace_append hprefix tailTrace_24817
  have hstable : (prefixWord ++ tailWord_24817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24817).length < 2 ^ (prefixWord ++ tailWord_24817).sum := by decide
  have hdescent : baseEnd_24817 < baseStart_24817 := by decide
  rcases family_descends (prefixWord ++ tailWord_24817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24833 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_24833 : Nat := 118140960795 + 24833 * 2 ^ 59
def prefixEnd_24833 : Nat := 4983230072969 + 3 ^ 40 * 24833 * 2
def baseEnd_24833 : Nat := 12751265093206574473301

theorem tailTrace_24833 : CollatzResearch.WordTrace tailWord_24833 prefixEnd_24833 12751265093206574473301 := by
  unfold tailWord_24833
  simp only [CollatzResearch.WordTrace]
  refine ⟨905733919041756983855153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 603822612694504655903435 905733919041756983855153)
  ·
    refine ⟨679300439281317737891365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 905733919041756983855153 679300439281317737891365)
    ·
      refine ⟨127368832365247075854631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 679300439281317737891365 127368832365247075854631)
      ·
        refine ⟨191053248547870613781947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127368832365247075854631 191053248547870613781947)
        ·
          refine ⟨286579872821805920672921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191053248547870613781947 286579872821805920672921)
          ·
            refine ⟨214934904616354440504691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286579872821805920672921 214934904616354440504691)
            ·
              refine ⟨322402356924531660757037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214934904616354440504691 322402356924531660757037)
              ·
                refine ⟨120900883846699372783889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322402356924531660757037 120900883846699372783889)
                ·
                  refine ⟨90675662885024529587917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120900883846699372783889 90675662885024529587917)
                  ·
                    refine ⟨34003373581884198595469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90675662885024529587917 34003373581884198595469)
                    ·
                      refine ⟨12751265093206574473301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34003373581884198595469 12751265093206574473301)
                      ·
                        rfl

theorem cell23_24833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_24833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24833 prefixEnd_24833 := by exact prefixLift 24833
  have htrace : WordTrace (prefixWord ++ tailWord_24833) baseStart_24833 baseEnd_24833 := by
    simpa [prefixWord, tailWord_24833, baseEnd_24833] using wordTrace_append hprefix tailTrace_24833
  have hstable : (prefixWord ++ tailWord_24833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24833).length < 2 ^ (prefixWord ++ tailWord_24833).sum := by decide
  have hdescent : baseEnd_24833 < baseStart_24833 := by decide
  rcases family_descends (prefixWord ++ tailWord_24833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24834 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_24834 : Nat := 118140960795 + 24834 * 2 ^ 59
def prefixEnd_24834 : Nat := 4983230072969 + 3 ^ 40 * 24834 * 2
def baseEnd_24834 : Nat := 12751778573861070560797

theorem tailTrace_24834 : CollatzResearch.WordTrace tailWord_24834 prefixEnd_24834 12751778573861070560797 := by
  unfold tailWord_24834
  simp only [CollatzResearch.WordTrace]
  refine ⟨226442598009533538660389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 603846928025422769761037 226442598009533538660389)
  ·
    refine ⟨42457987126787538498823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226442598009533538660389 42457987126787538498823)
    ·
      refine ⟨63686980690181307748235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42457987126787538498823 63686980690181307748235)
      ·
        refine ⟨95530471035271961622353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63686980690181307748235 95530471035271961622353)
        ·
          refine ⟨71647853276453971216765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95530471035271961622353 71647853276453971216765)
          ·
            refine ⟨26867944978670239206287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71647853276453971216765 26867944978670239206287)
            ·
              refine ⟨40301917468005358809431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26867944978670239206287 40301917468005358809431)
              ·
                refine ⟨60452876202008038214147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40301917468005358809431 60452876202008038214147)
                ·
                  refine ⟨90679314303012057321221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60452876202008038214147 90679314303012057321221)
                  ·
                    refine ⟨17002371431814760747729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90679314303012057321221 17002371431814760747729)
                    ·
                      refine ⟨12751778573861070560797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17002371431814760747729 12751778573861070560797)
                      ·
                        rfl

theorem cell23_24834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_24834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24834 prefixEnd_24834 := by exact prefixLift 24834
  have htrace : WordTrace (prefixWord ++ tailWord_24834) baseStart_24834 baseEnd_24834 := by
    simpa [prefixWord, tailWord_24834, baseEnd_24834] using wordTrace_append hprefix tailTrace_24834
  have hstable : (prefixWord ++ tailWord_24834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24834).length < 2 ^ (prefixWord ++ tailWord_24834).sum := by decide
  have hdescent : baseEnd_24834 < baseStart_24834 := by decide
  rcases family_descends (prefixWord ++ tailWord_24834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24874 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_24874 : Nat := 118140960795 + 24874 * 2 ^ 59
def prefixEnd_24874 : Nat := 4983230072969 + 3 ^ 40 * 24874 * 2
def baseEnd_24874 : Nat := 1419146422226768228957

theorem tailTrace_24874 : CollatzResearch.WordTrace tailWord_24874 prefixEnd_24874 1419146422226768228957 := by
  unfold tailWord_24874
  simp only [CollatzResearch.WordTrace]
  refine ⟨226807327973305246524419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 604819541262147324065117 226807327973305246524419)
  ·
    refine ⟨340210991959957869786629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226807327973305246524419 340210991959957869786629)
    ·
      refine ⟨63789560992492100584993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340210991959957869786629 63789560992492100584993)
      ·
        refine ⟨47842170744369075438745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63789560992492100584993 47842170744369075438745)
        ·
          refine ⟨35881628058276806579059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47842170744369075438745 35881628058276806579059)
          ·
            refine ⟨53822442087415209868589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35881628058276806579059 53822442087415209868589)
            ·
              refine ⟨20183415782780703700721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53822442087415209868589 20183415782780703700721)
              ·
                refine ⟨15137561837085527775541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20183415782780703700721 15137561837085527775541)
                ·
                  refine ⟨1419146422226768228957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15137561837085527775541 1419146422226768228957)
                  ·
                    rfl

theorem cell23_24874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_24874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24874 prefixEnd_24874 := by exact prefixLift 24874
  have htrace : WordTrace (prefixWord ++ tailWord_24874) baseStart_24874 baseEnd_24874 := by
    simpa [prefixWord, tailWord_24874, baseEnd_24874] using wordTrace_append hprefix tailTrace_24874
  have hstable : (prefixWord ++ tailWord_24874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24874).length < 2 ^ (prefixWord ++ tailWord_24874).sum := by decide
  have hdescent : baseEnd_24874 < baseStart_24874 := by decide
  rcases family_descends (prefixWord ++ tailWord_24874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24896 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 10]
def baseStart_24896 : Nat := 118140960795 + 24896 * 2 ^ 59
def prefixEnd_24896 : Nat := 4983230072969 + 3 ^ 40 * 24896 * 2
def baseEnd_24896 : Nat := 1420401597159980887279

theorem tailTrace_24896 : CollatzResearch.WordTrace tailWord_24896 prefixEnd_24896 1420401597159980887279 := by
  unfold tailWord_24896
  simp only [CollatzResearch.WordTrace]
  refine ⟨454015858906759371699271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 605354478542345828932361 454015858906759371699271)
  ·
    refine ⟨681023788360139057548907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454015858906759371699271 681023788360139057548907)
    ·
      refine ⟨1021535682540208586323361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681023788360139057548907 1021535682540208586323361)
      ·
        refine ⟨766151761905156439742521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1021535682540208586323361 766151761905156439742521)
        ·
          refine ⟨574613821428867329806891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766151761905156439742521 574613821428867329806891)
          ·
            refine ⟨861920732143300994710337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574613821428867329806891 861920732143300994710337)
            ·
              refine ⟨646440549107475746032753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861920732143300994710337 646440549107475746032753)
              ·
                refine ⟨484830411830606809524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646440549107475746032753 484830411830606809524565)
                ·
                  refine ⟨1420401597159980887279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 484830411830606809524565 1420401597159980887279)
                  ·
                    rfl

theorem cell23_24896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_24896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24896 prefixEnd_24896 := by exact prefixLift 24896
  have htrace : WordTrace (prefixWord ++ tailWord_24896) baseStart_24896 baseEnd_24896 := by
    simpa [prefixWord, tailWord_24896, baseEnd_24896] using wordTrace_append hprefix tailTrace_24896
  have hstable : (prefixWord ++ tailWord_24896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24896).length < 2 ^ (prefixWord ++ tailWord_24896).sum := by decide
  have hdescent : baseEnd_24896 < baseStart_24896 := by decide
  rcases family_descends (prefixWord ++ tailWord_24896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24930 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_24930 : Nat := 118140960795 + 24930 * 2 ^ 59
def prefixEnd_24930 : Nat := 4983230072969 + 3 ^ 40 * 24930 * 2
def baseEnd_24930 : Nat := 1422341412965854995595

theorem tailTrace_24930 : CollatzResearch.WordTrace tailWord_24930 prefixEnd_24930 1422341412965854995595 := by
  unfold tailWord_24930
  simp only [CollatzResearch.WordTrace]
  refine ⟨227317949922585637534061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 606181199793561700090829 227317949922585637534061)
  ·
    refine ⟨85244231220969614075273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227317949922585637534061 85244231220969614075273)
    ·
      refine ⟨63933173415727210556455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85244231220969614075273 63933173415727210556455)
      ·
        refine ⟨95899760123590815834683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63933173415727210556455 95899760123590815834683)
        ·
          refine ⟨143849640185386223752025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95899760123590815834683 143849640185386223752025)
          ·
            refine ⟨107887230139039667814019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143849640185386223752025 107887230139039667814019)
            ·
              refine ⟨161830845208559501721029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107887230139039667814019 161830845208559501721029)
              ·
                refine ⟨30343283476604906572693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161830845208559501721029 30343283476604906572693)
                ·
                  refine ⟨1422341412965854995595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30343283476604906572693 1422341412965854995595)
                  ·
                    rfl

theorem cell23_24930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_24930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24930 prefixEnd_24930 := by exact prefixLift 24930
  have htrace : WordTrace (prefixWord ++ tailWord_24930) baseStart_24930 baseEnd_24930 := by
    simpa [prefixWord, tailWord_24930, baseEnd_24930] using wordTrace_append hprefix tailTrace_24930
  have hstable : (prefixWord ++ tailWord_24930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24930).length < 2 ^ (prefixWord ++ tailWord_24930).sum := by decide
  have hdescent : baseEnd_24930 < baseStart_24930 := by decide
  rcases family_descends (prefixWord ++ tailWord_24930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24957 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_24957 : Nat := 118140960795 + 24957 * 2 ^ 59
def prefixEnd_24957 : Nat := 4983230072969 + 3 ^ 40 * 24957 * 2
def baseEnd_24957 : Nat := 12814936694364089322731

theorem tailTrace_24957 : CollatzResearch.WordTrace tailWord_24957 prefixEnd_24957 12814936694364089322731 := by
  unfold tailWord_24957
  simp only [CollatzResearch.WordTrace]
  refine ⟨910256570592526161369125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606837713728350774246083 910256570592526161369125)
  ·
    refine ⟨170673106986098655256711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 910256570592526161369125 170673106986098655256711)
    ·
      refine ⟨256009660479147982885067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170673106986098655256711 256009660479147982885067)
      ·
        refine ⟨384014490718721974327601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256009660479147982885067 384014490718721974327601)
        ·
          refine ⟨288010868039041480745701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384014490718721974327601 288010868039041480745701)
          ·
            refine ⟨54002037757320277639819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288010868039041480745701 54002037757320277639819)
            ·
              refine ⟨81003056635980416459729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54002037757320277639819 81003056635980416459729)
              ·
                refine ⟨60752292476985312344797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81003056635980416459729 60752292476985312344797)
                ·
                  refine ⟨22782109678869492129299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60752292476985312344797 22782109678869492129299)
                  ·
                    refine ⟨34173164518304238193949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22782109678869492129299 34173164518304238193949)
                    ·
                      refine ⟨12814936694364089322731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34173164518304238193949 12814936694364089322731)
                      ·
                        rfl

theorem cell23_24957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_24957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_24957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_24957 prefixEnd_24957 := by exact prefixLift 24957
  have htrace : WordTrace (prefixWord ++ tailWord_24957) baseStart_24957 baseEnd_24957 := by
    simpa [prefixWord, tailWord_24957, baseEnd_24957] using wordTrace_append hprefix tailTrace_24957
  have hstable : (prefixWord ++ tailWord_24957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24957).length < 2 ^ (prefixWord ++ tailWord_24957).sum := by decide
  have hdescent : baseEnd_24957 < baseStart_24957 := by decide
  rcases family_descends (prefixWord ++ tailWord_24957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25017 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 3]
def baseStart_25017 : Nat := 118140960795 + 25017 * 2 ^ 59
def prefixEnd_25017 : Nat := 4983230072969 + 3 ^ 40 * 25017 * 2
def baseEnd_25017 : Nat := 12845745533633854572455

theorem tailTrace_25017 : CollatzResearch.WordTrace tailWord_25017 prefixEnd_25017 12845745533633854572455 := by
  unfold tailWord_25017
  simp only [CollatzResearch.WordTrace]
  refine ⟨912444950375156408553305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 608296633583437605702203 912444950375156408553305)
  ·
    refine ⟨684333712781367306414979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 912444950375156408553305 684333712781367306414979)
    ·
      refine ⟨1026500569172050959622469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684333712781367306414979 1026500569172050959622469)
      ·
        refine ⟨192468856719759554929213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1026500569172050959622469 192468856719759554929213)
        ·
          refine ⟨72175821269909833098455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192468856719759554929213 72175821269909833098455)
          ·
            refine ⟨108263731904864749647683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72175821269909833098455 108263731904864749647683)
            ·
              refine ⟨162395597857297124471525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108263731904864749647683 162395597857297124471525)
              ·
                refine ⟨30449174598243210838411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162395597857297124471525 30449174598243210838411)
                ·
                  refine ⟨45673761897364816257617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30449174598243210838411 45673761897364816257617)
                  ·
                    refine ⟨34255321423023612193213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45673761897364816257617 34255321423023612193213)
                    ·
                      refine ⟨12845745533633854572455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34255321423023612193213 12845745533633854572455)
                      ·
                        rfl

theorem cell23_25017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_25017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25017 prefixEnd_25017 := by exact prefixLift 25017
  have htrace : WordTrace (prefixWord ++ tailWord_25017) baseStart_25017 baseEnd_25017 := by
    simpa [prefixWord, tailWord_25017, baseEnd_25017] using wordTrace_append hprefix tailTrace_25017
  have hstable : (prefixWord ++ tailWord_25017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25017).length < 2 ^ (prefixWord ++ tailWord_25017).sum := by decide
  have hdescent : baseEnd_25017 < baseStart_25017 := by decide
  rcases family_descends (prefixWord ++ tailWord_25017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25020 : List Nat := [2, 2, 2, 4, 1, 2, 1, 9]
def baseStart_25020 : Nat := 118140960795 + 25020 * 2 ^ 59
def prefixEnd_25020 : Nat := 4983230072969 + 3 ^ 40 * 25020 * 2
def baseEnd_25020 : Nat := 475825406503605290183

theorem tailTrace_25020 : CollatzResearch.WordTrace tailWord_25020 prefixEnd_25020 475825406503605290183 := by
  unfold tailWord_25020
  simp only [CollatzResearch.WordTrace]
  refine ⟨456277184682143960456257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 608369579576191947275009 456277184682143960456257)
  ·
    refine ⟨342207888511607970342193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 456277184682143960456257 342207888511607970342193)
    ·
      refine ⟨256655916383705977756645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342207888511607970342193 256655916383705977756645)
      ·
        refine ⟨48122984321944870829371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256655916383705977756645 48122984321944870829371)
        ·
          refine ⟨72184476482917306244057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48122984321944870829371 72184476482917306244057)
          ·
            refine ⟨54138357362187979683043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72184476482917306244057 54138357362187979683043)
            ·
              refine ⟨81207536043281969524565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54138357362187979683043 81207536043281969524565)
              ·
                refine ⟨475825406503605290183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 81207536043281969524565 475825406503605290183)
                ·
                  rfl

theorem cell23_25020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 9].length) (baseStart_25020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25020 prefixEnd_25020 := by exact prefixLift 25020
  have htrace : WordTrace (prefixWord ++ tailWord_25020) baseStart_25020 baseEnd_25020 := by
    simpa [prefixWord, tailWord_25020, baseEnd_25020] using wordTrace_append hprefix tailTrace_25020
  have hstable : (prefixWord ++ tailWord_25020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25020).length < 2 ^ (prefixWord ++ tailWord_25020).sum := by decide
  have hdescent : baseEnd_25020 < baseStart_25020 := by decide
  rcases family_descends (prefixWord ++ tailWord_25020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25031 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_25031 : Nat := 118140960795 + 25031 * 2 ^ 59
def prefixEnd_25031 : Nat := 4983230072969 + 3 ^ 40 * 25031 * 2
def baseEnd_25031 : Nat := 12852934262796799797391

theorem tailTrace_25031 : CollatzResearch.WordTrace tailWord_25031 prefixEnd_25031 12852934262796799797391 := by
  unfold tailWord_25031
  simp only [CollatzResearch.WordTrace]
  refine ⟨912955572324436799562947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 608637048216291199708631 912955572324436799562947)
  ·
    refine ⟨1369433358486655199344421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912955572324436799562947 1369433358486655199344421)
    ·
      refine ⟨256768754716247849877079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1369433358486655199344421 256768754716247849877079)
      ·
        refine ⟨385153132074371774815619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256768754716247849877079 385153132074371774815619)
        ·
          refine ⟨577729698111557662223429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385153132074371774815619 577729698111557662223429)
          ·
            refine ⟨108324318395917061666893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 577729698111557662223429 108324318395917061666893)
            ·
              refine ⟨40621619398468898125085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108324318395917061666893 40621619398468898125085)
              ·
                refine ⟨15233107274425836796907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40621619398468898125085 15233107274425836796907)
                ·
                  refine ⟨22849660911638755195361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15233107274425836796907 22849660911638755195361)
                  ·
                    refine ⟨17137245683729066396521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22849660911638755195361 17137245683729066396521)
                    ·
                      refine ⟨12852934262796799797391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17137245683729066396521 12852934262796799797391)
                      ·
                        rfl

theorem cell23_25031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_25031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25031 prefixEnd_25031 := by exact prefixLift 25031
  have htrace : WordTrace (prefixWord ++ tailWord_25031) baseStart_25031 baseEnd_25031 := by
    simpa [prefixWord, tailWord_25031, baseEnd_25031] using wordTrace_append hprefix tailTrace_25031
  have hstable : (prefixWord ++ tailWord_25031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25031).length < 2 ^ (prefixWord ++ tailWord_25031).sum := by decide
  have hdescent : baseEnd_25031 < baseStart_25031 := by decide
  rcases family_descends (prefixWord ++ tailWord_25031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25057 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_25057 : Nat := 118140960795 + 25057 * 2 ^ 59
def prefixEnd_25057 : Nat := 4983230072969 + 3 ^ 40 * 25057 * 2
def baseEnd_25057 : Nat := 12866284759813698072271

theorem tailTrace_25057 : CollatzResearch.WordTrace tailWord_25057 prefixEnd_25057 12866284759813698072271 := by
  unfold tailWord_25057
  simp only [CollatzResearch.WordTrace]
  refine ⟨913903870230243240009425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 609269246820162160006283 913903870230243240009425)
  ·
    refine ⟨685427902672682430007069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 913903870230243240009425 685427902672682430007069)
    ·
      refine ⟨257035463502255911252651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 685427902672682430007069 257035463502255911252651)
      ·
        refine ⟨385553195253383866878977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257035463502255911252651 385553195253383866878977)
        ·
          refine ⟨289164896440037900159233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385553195253383866878977 289164896440037900159233)
          ·
            refine ⟨216873672330028425119425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289164896440037900159233 216873672330028425119425)
            ·
              refine ⟨162655254247521318839569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216873672330028425119425 162655254247521318839569)
              ·
                refine ⟨121991440685640989129677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162655254247521318839569 121991440685640989129677)
                ·
                  refine ⟨45746790257115370923629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121991440685640989129677 45746790257115370923629)
                  ·
                    refine ⟨17155046346418264096361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45746790257115370923629 17155046346418264096361)
                    ·
                      refine ⟨12866284759813698072271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17155046346418264096361 12866284759813698072271)
                      ·
                        rfl

theorem cell23_25057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_25057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25057 prefixEnd_25057 := by exact prefixLift 25057
  have htrace : WordTrace (prefixWord ++ tailWord_25057) baseStart_25057 baseEnd_25057 := by
    simpa [prefixWord, tailWord_25057, baseEnd_25057] using wordTrace_append hprefix tailTrace_25057
  have hstable : (prefixWord ++ tailWord_25057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25057).length < 2 ^ (prefixWord ++ tailWord_25057).sum := by decide
  have hdescent : baseEnd_25057 < baseStart_25057 := by decide
  rcases family_descends (prefixWord ++ tailWord_25057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25064 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_25064 : Nat := 118140960795 + 25064 * 2 ^ 59
def prefixEnd_25064 : Nat := 4983230072969 + 3 ^ 40 * 25064 * 2
def baseEnd_25064 : Nat := 12869879124395170684739

theorem tailTrace_25064 : CollatzResearch.WordTrace tailWord_25064 prefixEnd_25064 12869879124395170684739 := by
  unfold tailWord_25064
  simp only [CollatzResearch.WordTrace]
  refine ⟨457079590602441717757123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 609439454136588957009497 457079590602441717757123)
  ·
    refine ⟨685619385903662576635685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457079590602441717757123 685619385903662576635685)
    ·
      refine ⟨128553634856936733119191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 685619385903662576635685 128553634856936733119191)
      ·
        refine ⟨192830452285405099678787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128553634856936733119191 192830452285405099678787)
        ·
          refine ⟨289245678428107649518181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192830452285405099678787 289245678428107649518181)
          ·
            refine ⟨54233564705270184284659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289245678428107649518181 54233564705270184284659)
            ·
              refine ⟨81350347057905276426989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54233564705270184284659 81350347057905276426989)
              ·
                refine ⟨30506380146714478660121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81350347057905276426989 30506380146714478660121)
                ·
                  refine ⟨22879785110035858995091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30506380146714478660121 22879785110035858995091)
                  ·
                    refine ⟨34319677665053788492637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22879785110035858995091 34319677665053788492637)
                    ·
                      refine ⟨12869879124395170684739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34319677665053788492637 12869879124395170684739)
                      ·
                        rfl

theorem cell23_25064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_25064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25064 prefixEnd_25064 := by exact prefixLift 25064
  have htrace : WordTrace (prefixWord ++ tailWord_25064) baseStart_25064 baseEnd_25064 := by
    simpa [prefixWord, tailWord_25064, baseEnd_25064] using wordTrace_append hprefix tailTrace_25064
  have hstable : (prefixWord ++ tailWord_25064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25064).length < 2 ^ (prefixWord ++ tailWord_25064).sum := by decide
  have hdescent : baseEnd_25064 < baseStart_25064 := by decide
  rcases family_descends (prefixWord ++ tailWord_25064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25087 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 1, 4, 2]
def baseStart_25087 : Nat := 118140960795 + 25087 * 2 ^ 59
def prefixEnd_25087 : Nat := 4983230072969 + 3 ^ 40 * 25087 * 2
def baseEnd_25087 : Nat := 12881689179448580697133

theorem tailTrace_25087 : CollatzResearch.WordTrace tailWord_25087 prefixEnd_25087 12881689179448580697133 := by
  unfold tailWord_25087
  simp only [CollatzResearch.WordTrace]
  refine ⟨914998060121558363601515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 609998706747705575734343 914998060121558363601515)
  ·
    refine ⟨1372497090182337545402273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914998060121558363601515 1372497090182337545402273)
    ·
      refine ⟨1029372817636753159051705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1372497090182337545402273 1029372817636753159051705)
      ·
        refine ⟨772029613227564869288779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1029372817636753159051705 772029613227564869288779)
        ·
          refine ⟨1158044419841347303933169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772029613227564869288779 1158044419841347303933169)
          ·
            refine ⟨868533314881010477949877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158044419841347303933169 868533314881010477949877)
            ·
              refine ⟨81424998270094732307801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 868533314881010477949877 81424998270094732307801)
              ·
                refine ⟨61068748702571049230851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81424998270094732307801 61068748702571049230851)
                ·
                  refine ⟨91603123053856573846277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61068748702571049230851 91603123053856573846277)
                  ·
                    refine ⟨17175585572598107596177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91603123053856573846277 17175585572598107596177)
                    ·
                      refine ⟨12881689179448580697133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17175585572598107596177 12881689179448580697133)
                      ·
                        rfl

theorem cell23_25087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_25087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25087 prefixEnd_25087 := by exact prefixLift 25087
  have htrace : WordTrace (prefixWord ++ tailWord_25087) baseStart_25087 baseEnd_25087 := by
    simpa [prefixWord, tailWord_25087, baseEnd_25087] using wordTrace_append hprefix tailTrace_25087
  have hstable : (prefixWord ++ tailWord_25087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25087).length < 2 ^ (prefixWord ++ tailWord_25087).sum := by decide
  have hdescent : baseEnd_25087 < baseStart_25087 := by decide
  rcases family_descends (prefixWord ++ tailWord_25087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25103 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_25103 : Nat := 118140960795 + 25103 * 2 ^ 59
def prefixEnd_25103 : Nat := 4983230072969 + 3 ^ 40 * 25103 * 2
def baseEnd_25103 : Nat := 12889904869920518097059

theorem tailTrace_25103 : CollatzResearch.WordTrace tailWord_25103 prefixEnd_25103 12889904869920518097059 := by
  unfold tailWord_25103
  simp only [CollatzResearch.WordTrace]
  refine ⟨915581628063593096183963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 610387752042395397455975 915581628063593096183963)
  ·
    refine ⟨1373372442095389644275945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915581628063593096183963 1373372442095389644275945)
    ·
      refine ⟨1030029331571542233206959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1373372442095389644275945 1030029331571542233206959)
      ·
        refine ⟨1545043997357313349810439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030029331571542233206959 1545043997357313349810439)
        ·
          refine ⟨2317565996035970024715659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545043997357313349810439 2317565996035970024715659)
          ·
            refine ⟨3476348994053955037073489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317565996035970024715659 3476348994053955037073489)
            ·
              refine ⟨2607261745540466277805117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476348994053955037073489 2607261745540466277805117)
              ·
                refine ⟨977723154577674854176919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607261745540466277805117 977723154577674854176919)
                ·
                  refine ⟨1466584731866512281265379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977723154577674854176919 1466584731866512281265379)
                  ·
                    refine ⟨2199877097799768421898069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466584731866512281265379 2199877097799768421898069)
                    ·
                      refine ⟨12889904869920518097059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 2199877097799768421898069 12889904869920518097059)
                      ·
                        rfl

theorem cell23_25103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_25103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25103 prefixEnd_25103 := by exact prefixLift 25103
  have htrace : WordTrace (prefixWord ++ tailWord_25103) baseStart_25103 baseEnd_25103 := by
    simpa [prefixWord, tailWord_25103, baseEnd_25103] using wordTrace_append hprefix tailTrace_25103
  have hstable : (prefixWord ++ tailWord_25103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25103).length < 2 ^ (prefixWord ++ tailWord_25103).sum := by decide
  have hdescent : baseEnd_25103 < baseStart_25103 := by decide
  rcases family_descends (prefixWord ++ tailWord_25103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25117 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_25117 : Nat := 118140960795 + 25117 * 2 ^ 59
def prefixEnd_25117 : Nat := 4983230072969 + 3 ^ 40 * 25117 * 2
def baseEnd_25117 : Nat := 12897093599083463321995

theorem tailTrace_25117 : CollatzResearch.WordTrace tailWord_25117 prefixEnd_25117 12897093599083463321995 := by
  unfold tailWord_25117
  simp only [CollatzResearch.WordTrace]
  refine ⟨916092250012873487193605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 610728166675248991462403 916092250012873487193605)
  ·
    refine ⟨171767296877413778848801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 916092250012873487193605 171767296877413778848801)
    ·
      refine ⟨128825472658060334136601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171767296877413778848801 128825472658060334136601)
      ·
        refine ⟨96619104493545250602451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128825472658060334136601 96619104493545250602451)
        ·
          refine ⟨144928656740317875903677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96619104493545250602451 144928656740317875903677)
          ·
            refine ⟨54348246277619203463879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144928656740317875903677 54348246277619203463879)
            ·
              refine ⟨81522369416428805195819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54348246277619203463879 81522369416428805195819)
              ·
                refine ⟨122283554124643207793729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81522369416428805195819 122283554124643207793729)
                ·
                  refine ⟨91712665593482405845297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122283554124643207793729 91712665593482405845297)
                  ·
                    refine ⟨68784499195111804383973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91712665593482405845297 68784499195111804383973)
                    ·
                      refine ⟨12897093599083463321995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 68784499195111804383973 12897093599083463321995)
                      ·
                        rfl

theorem cell23_25117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_25117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25117 prefixEnd_25117 := by exact prefixLift 25117
  have htrace : WordTrace (prefixWord ++ tailWord_25117) baseStart_25117 baseEnd_25117 := by
    simpa [prefixWord, tailWord_25117, baseEnd_25117] using wordTrace_append hprefix tailTrace_25117
  have hstable : (prefixWord ++ tailWord_25117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25117).length < 2 ^ (prefixWord ++ tailWord_25117).sum := by decide
  have hdescent : baseEnd_25117 < baseStart_25117 := by decide
  rcases family_descends (prefixWord ++ tailWord_25117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25187 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 3, 4]
def baseStart_25187 : Nat := 118140960795 + 25187 * 2 ^ 59
def prefixEnd_25187 : Nat := 4983230072969 + 3 ^ 40 * 25187 * 2
def baseEnd_25187 : Nat := 4311012414966063148891

theorem tailTrace_25187 : CollatzResearch.WordTrace tailWord_25187 prefixEnd_25187 4311012414966063148891 := by
  unfold tailWord_25187
  simp only [CollatzResearch.WordTrace]
  refine ⟨918645359759275442241815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 612430239839516961494543 918645359759275442241815)
  ·
    refine ⟨1377968039638913163362723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918645359759275442241815 1377968039638913163362723)
    ·
      refine ⟨2066952059458369745044085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377968039638913163362723 2066952059458369745044085)
      ·
        refine ⟨193776755574222163597883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2066952059458369745044085 193776755574222163597883)
        ·
          refine ⟨290665133361333245396825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193776755574222163597883 290665133361333245396825)
          ·
            refine ⟨217998850020999934047619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290665133361333245396825 217998850020999934047619)
            ·
              refine ⟨326998275031499901071429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217998850020999934047619 326998275031499901071429)
              ·
                refine ⟨61312176568406231450893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326998275031499901071429 61312176568406231450893)
                ·
                  refine ⟨22992066213152336794085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61312176568406231450893 22992066213152336794085)
                  ·
                    refine ⟨4311012414966063148891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22992066213152336794085 4311012414966063148891)
                    ·
                      rfl

theorem cell23_25187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 4].length) (baseStart_25187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25187 prefixEnd_25187 := by exact prefixLift 25187
  have htrace : WordTrace (prefixWord ++ tailWord_25187) baseStart_25187 baseEnd_25187 := by
    simpa [prefixWord, tailWord_25187, baseEnd_25187] using wordTrace_append hprefix tailTrace_25187
  have hstable : (prefixWord ++ tailWord_25187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25187).length < 2 ^ (prefixWord ++ tailWord_25187).sum := by decide
  have hdescent : baseEnd_25187 < baseStart_25187 := by decide
  rcases family_descends (prefixWord ++ tailWord_25187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25217 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 6]
def baseStart_25217 : Nat := 118140960795 + 25217 * 2 ^ 59
def prefixEnd_25217 : Nat := 4983230072969 + 3 ^ 40 * 25217 * 2
def baseEnd_25217 : Nat := 1438715740503674674615

theorem tailTrace_25217 : CollatzResearch.WordTrace tailWord_25217 prefixEnd_25217 1438715740503674674615 := by
  unfold tailWord_25217
  simp only [CollatzResearch.WordTrace]
  refine ⟨919739549650590565833905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 613159699767060377222603 919739549650590565833905)
  ·
    refine ⟨689804662237942924375429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 919739549650590565833905 689804662237942924375429)
    ·
      refine ⟨129338374169614298320393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 689804662237942924375429 129338374169614298320393)
      ·
        refine ⟨97003780627210723740295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129338374169614298320393 97003780627210723740295)
        ·
          refine ⟨145505670940816085610443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97003780627210723740295 145505670940816085610443)
          ·
            refine ⟨218258506411224128415665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145505670940816085610443 218258506411224128415665)
            ·
              refine ⟨163693879808418096311749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218258506411224128415665 163693879808418096311749)
              ·
                refine ⟨30692602464078393058453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163693879808418096311749 30692602464078393058453)
                ·
                  refine ⟨1438715740503674674615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30692602464078393058453 1438715740503674674615)
                  ·
                    rfl

theorem cell23_25217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 6].length) (baseStart_25217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25217 prefixEnd_25217 := by exact prefixLift 25217
  have htrace : WordTrace (prefixWord ++ tailWord_25217) baseStart_25217 baseEnd_25217 := by
    simpa [prefixWord, tailWord_25217, baseEnd_25217] using wordTrace_append hprefix tailTrace_25217
  have hstable : (prefixWord ++ tailWord_25217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25217).length < 2 ^ (prefixWord ++ tailWord_25217).sum := by decide
  have hdescent : baseEnd_25217 < baseStart_25217 := by decide
  rcases family_descends (prefixWord ++ tailWord_25217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25218 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_25218 : Nat := 118140960795 + 25218 * 2 ^ 59
def prefixEnd_25218 : Nat := 4983230072969 + 3 ^ 40 * 25218 * 2
def baseEnd_25218 : Nat := 12948955145187568159031

theorem tailTrace_25218 : CollatzResearch.WordTrace tailWord_25218 prefixEnd_25218 12948955145187568159031 := by
  unfold tailWord_25218
  simp only [CollatzResearch.WordTrace]
  refine ⟨229944005661741934155077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 613184015097978491080205 229944005661741934155077)
  ·
    refine ⟨43114501061576612654077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229944005661741934155077 43114501061576612654077)
    ·
      refine ⟨16167937898091229745279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43114501061576612654077 16167937898091229745279)
      ·
        refine ⟨24251906847136844617919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167937898091229745279 24251906847136844617919)
        ·
          refine ⟨36377860270705266926879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24251906847136844617919 36377860270705266926879)
          ·
            refine ⟨54566790406057900390319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36377860270705266926879 54566790406057900390319)
            ·
              refine ⟨81850185609086850585479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54566790406057900390319 81850185609086850585479)
              ·
                refine ⟨122775278413630275878219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81850185609086850585479 122775278413630275878219)
                ·
                  refine ⟨184162917620445413817329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122775278413630275878219 184162917620445413817329)
                  ·
                    refine ⟨138122188215334060362997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184162917620445413817329 138122188215334060362997)
                    ·
                      refine ⟨12948955145187568159031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 138122188215334060362997 12948955145187568159031)
                      ·
                        rfl

theorem cell23_25218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_25218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25218 prefixEnd_25218 := by exact prefixLift 25218
  have htrace : WordTrace (prefixWord ++ tailWord_25218) baseStart_25218 baseEnd_25218 := by
    simpa [prefixWord, tailWord_25218, baseEnd_25218] using wordTrace_append hprefix tailTrace_25218
  have hstable : (prefixWord ++ tailWord_25218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25218).length < 2 ^ (prefixWord ++ tailWord_25218).sum := by decide
  have hdescent : baseEnd_25218 < baseStart_25218 := by decide
  rcases family_descends (prefixWord ++ tailWord_25218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25234 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_25234 : Nat := 118140960795 + 25234 * 2 ^ 59
def prefixEnd_25234 : Nat := 4983230072969 + 3 ^ 40 * 25234 * 2
def baseEnd_25234 : Nat := 1439685648406611728773

theorem tailTrace_25234 : CollatzResearch.WordTrace tailWord_25234 prefixEnd_25234 1439685648406611728773 := by
  unfold tailWord_25234
  simp only [CollatzResearch.WordTrace]
  refine ⟨230089897647250617300689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 613573060392668312801837 230089897647250617300689)
  ·
    refine ⟨172567423235437962975517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230089897647250617300689 172567423235437962975517)
    ·
      refine ⟨64712783713289236115819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172567423235437962975517 64712783713289236115819)
      ·
        refine ⟨97069175569933854173729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64712783713289236115819 97069175569933854173729)
        ·
          refine ⟨72801881677450390630297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97069175569933854173729 72801881677450390630297)
          ·
            refine ⟨54601411258087792972723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72801881677450390630297 54601411258087792972723)
            ·
              refine ⟨81902116887131689459085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54601411258087792972723 81902116887131689459085)
              ·
                refine ⟨30713293832674383547157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81902116887131689459085 30713293832674383547157)
                ·
                  refine ⟨1439685648406611728773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30713293832674383547157 1439685648406611728773)
                  ·
                    rfl

theorem cell23_25234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_25234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25234 prefixEnd_25234 := by exact prefixLift 25234
  have htrace : WordTrace (prefixWord ++ tailWord_25234) baseStart_25234 baseEnd_25234 := by
    simpa [prefixWord, tailWord_25234, baseEnd_25234] using wordTrace_append hprefix tailTrace_25234
  have hstable : (prefixWord ++ tailWord_25234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25234).length < 2 ^ (prefixWord ++ tailWord_25234).sum := by decide
  have hdescent : baseEnd_25234 < baseStart_25234 := by decide
  rcases family_descends (prefixWord ++ tailWord_25234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25278 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_25278 : Nat := 118140960795 + 25278 * 2 ^ 59
def prefixEnd_25278 : Nat := 4983230072969 + 3 ^ 40 * 25278 * 2
def baseEnd_25278 : Nat := 12979763984457333408755

theorem tailTrace_25278 : CollatzResearch.WordTrace tailWord_25278 prefixEnd_25278 12979763984457333408755 := by
  unfold tailWord_25278
  simp only [CollatzResearch.WordTrace]
  refine ⟨115245550303699747975561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 614642934953065322536325 115245550303699747975561)
  ·
    refine ⟨86434162727774810981671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115245550303699747975561 86434162727774810981671)
    ·
      refine ⟨129651244091662216472507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86434162727774810981671 129651244091662216472507)
      ·
        refine ⟨194476866137493324708761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129651244091662216472507 194476866137493324708761)
        ·
          refine ⟨145857649603119993531571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194476866137493324708761 145857649603119993531571)
          ·
            refine ⟨218786474404679990297357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145857649603119993531571 218786474404679990297357)
            ·
              refine ⟨82044927901754996361509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218786474404679990297357 82044927901754996361509)
              ·
                refine ⟨15383423981579061817783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82044927901754996361509 15383423981579061817783)
                ·
                  refine ⟨23075135972368592726675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15383423981579061817783 23075135972368592726675)
                  ·
                    refine ⟨34612703958552889090013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23075135972368592726675 34612703958552889090013)
                    ·
                      refine ⟨12979763984457333408755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34612703958552889090013 12979763984457333408755)
                      ·
                        rfl

theorem cell23_25278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_25278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25278 prefixEnd_25278 := by exact prefixLift 25278
  have htrace : WordTrace (prefixWord ++ tailWord_25278) baseStart_25278 baseEnd_25278 := by
    simpa [prefixWord, tailWord_25278, baseEnd_25278] using wordTrace_append hprefix tailTrace_25278
  have hstable : (prefixWord ++ tailWord_25278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25278).length < 2 ^ (prefixWord ++ tailWord_25278).sum := by decide
  have hdescent : baseEnd_25278 < baseStart_25278 := by decide
  rcases family_descends (prefixWord ++ tailWord_25278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25284 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_25284 : Nat := 118140960795 + 25284 * 2 ^ 59
def prefixEnd_25284 : Nat := 4983230072969 + 3 ^ 40 * 25284 * 2
def baseEnd_25284 : Nat := 12982844868384309933727

theorem tailTrace_25284 : CollatzResearch.WordTrace tailWord_25284 prefixEnd_25284 12982844868384309933727 := by
  unfold tailWord_25284
  simp only [CollatzResearch.WordTrace]
  refine ⟨461091620203930504261453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 614788826938574005681937 461091620203930504261453)
  ·
    refine ⟨172909357576473939098045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 461091620203930504261453 172909357576473939098045)
    ·
      refine ⟨64841009091177727161767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172909357576473939098045 64841009091177727161767)
      ·
        refine ⟨97261513636766590742651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64841009091177727161767 97261513636766590742651)
        ·
          refine ⟨145892270455149886113977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97261513636766590742651 145892270455149886113977)
          ·
            refine ⟨109419202841362414585483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145892270455149886113977 109419202841362414585483)
            ·
              refine ⟨164128804262043621878225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109419202841362414585483 164128804262043621878225)
              ·
                refine ⟨123096603196532716408669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164128804262043621878225 123096603196532716408669)
                ·
                  refine ⟨46161226198699768653251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123096603196532716408669 46161226198699768653251)
                  ·
                    refine ⟨69241839298049652979877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46161226198699768653251 69241839298049652979877)
                    ·
                      refine ⟨12982844868384309933727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 69241839298049652979877 12982844868384309933727)
                      ·
                        rfl

theorem cell23_25284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_25284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25284 prefixEnd_25284 := by exact prefixLift 25284
  have htrace : WordTrace (prefixWord ++ tailWord_25284) baseStart_25284 baseEnd_25284 := by
    simpa [prefixWord, tailWord_25284, baseEnd_25284] using wordTrace_append hprefix tailTrace_25284
  have hstable : (prefixWord ++ tailWord_25284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25284).length < 2 ^ (prefixWord ++ tailWord_25284).sum := by decide
  have hdescent : baseEnd_25284 < baseStart_25284 := by decide
  rcases family_descends (prefixWord ++ tailWord_25284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25294 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_25294 : Nat := 118140960795 + 25294 * 2 ^ 59
def prefixEnd_25294 : Nat := 4983230072969 + 3 ^ 40 * 25294 * 2
def baseEnd_25294 : Nat := 4329326558309756936227

theorem tailTrace_25294 : CollatzResearch.WordTrace tailWord_25294 prefixEnd_25294 4329326558309756936227 := by
  unfold tailWord_25294
  simp only [CollatzResearch.WordTrace]
  refine ⟨115318496296454089548367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 615031980247755144257957 115318496296454089548367)
  ·
    refine ⟨172977744444681134322551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115318496296454089548367 172977744444681134322551)
    ·
      refine ⟨259466616667021701483827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172977744444681134322551 259466616667021701483827)
      ·
        refine ⟨389199925000532552225741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259466616667021701483827 389199925000532552225741)
        ·
          refine ⟨145949971875199707084653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389199925000532552225741 145949971875199707084653)
          ·
            refine ⟨54731239453199890156745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145949971875199707084653 54731239453199890156745)
            ·
              refine ⟨41048429589899917617559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54731239453199890156745 41048429589899917617559)
              ·
                refine ⟨61572644384849876426339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41048429589899917617559 61572644384849876426339)
                ·
                  refine ⟨92358966577274814639509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61572644384849876426339 92358966577274814639509)
                  ·
                    refine ⟨4329326558309756936227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92358966577274814639509 4329326558309756936227)
                    ·
                      rfl

theorem cell23_25294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_25294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25294 prefixEnd_25294 := by exact prefixLift 25294
  have htrace : WordTrace (prefixWord ++ tailWord_25294) baseStart_25294 baseEnd_25294 := by
    simpa [prefixWord, tailWord_25294, baseEnd_25294] using wordTrace_append hprefix tailTrace_25294
  have hstable : (prefixWord ++ tailWord_25294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25294).length < 2 ^ (prefixWord ++ tailWord_25294).sum := by decide
  have hdescent : baseEnd_25294 < baseStart_25294 := by decide
  rcases family_descends (prefixWord ++ tailWord_25294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25304 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_25304 : Nat := 118140960795 + 25304 * 2 ^ 59
def prefixEnd_25304 : Nat := 4983230072969 + 3 ^ 40 * 25304 * 2
def baseEnd_25304 : Nat := 12993114481474231683635

theorem tailTrace_25304 : CollatzResearch.WordTrace tailWord_25304 prefixEnd_25304 12993114481474231683635 := by
  unfold tailWord_25304
  simp only [CollatzResearch.WordTrace]
  refine ⟨461456350167702212125483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 615275133556936282833977 461456350167702212125483)
  ·
    refine ⟨692184525251553318188225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 461456350167702212125483 692184525251553318188225)
    ·
      refine ⟨519138393938664988641169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 692184525251553318188225 519138393938664988641169)
      ·
        refine ⟨389353795453998741480877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519138393938664988641169 389353795453998741480877)
        ·
          refine ⟨146007673295249528055329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389353795453998741480877 146007673295249528055329)
          ·
            refine ⟨109505754971437146041497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146007673295249528055329 109505754971437146041497)
            ·
              refine ⟨82129316228577859531123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109505754971437146041497 82129316228577859531123)
              ·
                refine ⟨123193974342866789296685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82129316228577859531123 123193974342866789296685)
                ·
                  refine ⟨46197740378575045986257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123193974342866789296685 46197740378575045986257)
                  ·
                    refine ⟨34648305283931284489693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46197740378575045986257 34648305283931284489693)
                    ·
                      refine ⟨12993114481474231683635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34648305283931284489693 12993114481474231683635)
                      ·
                        rfl

theorem cell23_25304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_25304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25304 prefixEnd_25304 := by exact prefixLift 25304
  have htrace : WordTrace (prefixWord ++ tailWord_25304) baseStart_25304 baseEnd_25304 := by
    simpa [prefixWord, tailWord_25304, baseEnd_25304] using wordTrace_append hprefix tailTrace_25304
  have hstable : (prefixWord ++ tailWord_25304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25304).length < 2 ^ (prefixWord ++ tailWord_25304).sum := by decide
  have hdescent : baseEnd_25304 < baseStart_25304 := by decide
  rcases family_descends (prefixWord ++ tailWord_25304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25321 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 1, 2, 3]
def baseStart_25321 : Nat := 118140960795 + 25321 * 2 ^ 59
def prefixEnd_25321 : Nat := 4983230072969 + 3 ^ 40 * 25321 * 2
def baseEnd_25321 : Nat := 13001843652600665171057

theorem tailTrace_25321 : CollatzResearch.WordTrace tailWord_25321 prefixEnd_25321 13001843652600665171057 := by
  unfold tailWord_25321
  simp only [CollatzResearch.WordTrace]
  refine ⟨923532741273816327619817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 615688494182544218413211 923532741273816327619817)
  ·
    refine ⟨692649555955362245714863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 923532741273816327619817 692649555955362245714863)
    ·
      refine ⟨1038974333933043368572295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692649555955362245714863 1038974333933043368572295)
      ·
        refine ⟨1558461500899565052858443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038974333933043368572295 1558461500899565052858443)
        ·
          refine ⟨2337692251349347579287665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558461500899565052858443 2337692251349347579287665)
          ·
            refine ⟨1753269188512010684465749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337692251349347579287665 1753269188512010684465749)
            ·
              refine ⟨20546123302875125208583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1753269188512010684465749 20546123302875125208583)
              ·
                refine ⟨30819184954312687812875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20546123302875125208583 30819184954312687812875)
                ·
                  refine ⟨46228777431469031719313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30819184954312687812875 46228777431469031719313)
                  ·
                    refine ⟨34671583073601773789485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46228777431469031719313 34671583073601773789485)
                    ·
                      refine ⟨13001843652600665171057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34671583073601773789485 13001843652600665171057)
                      ·
                        rfl

theorem cell23_25321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 2, 3].length) (baseStart_25321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25321 prefixEnd_25321 := by exact prefixLift 25321
  have htrace : WordTrace (prefixWord ++ tailWord_25321) baseStart_25321 baseEnd_25321 := by
    simpa [prefixWord, tailWord_25321, baseEnd_25321] using wordTrace_append hprefix tailTrace_25321
  have hstable : (prefixWord ++ tailWord_25321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25321).length < 2 ^ (prefixWord ++ tailWord_25321).sum := by decide
  have hdescent : baseEnd_25321 < baseStart_25321 := by decide
  rcases family_descends (prefixWord ++ tailWord_25321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25351 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_25351 : Nat := 118140960795 + 25351 * 2 ^ 59
def prefixEnd_25351 : Nat := 4983230072969 + 3 ^ 40 * 25351 * 2
def baseEnd_25351 : Nat := 13017248072235547795919

theorem tailTrace_25351 : CollatzResearch.WordTrace tailWord_25351 prefixEnd_25351 13017248072235547795919 := by
  unfold tailWord_25351
  simp only [CollatzResearch.WordTrace]
  refine ⟨924626931165131451211907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 616417954110087634141271 924626931165131451211907)
  ·
    refine ⟨1386940396747697176817861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924626931165131451211907 1386940396747697176817861)
    ·
      refine ⟨260051324390193220653349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1386940396747697176817861 260051324390193220653349)
      ·
        refine ⟨48759623323161228872503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260051324390193220653349 48759623323161228872503)
        ·
          refine ⟨73139434984741843308755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48759623323161228872503 73139434984741843308755)
          ·
            refine ⟨109709152477112764963133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73139434984741843308755 109709152477112764963133)
            ·
              refine ⟨41140932178917286861175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109709152477112764963133 41140932178917286861175)
              ·
                refine ⟨61711398268375930291763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41140932178917286861175 61711398268375930291763)
                ·
                  refine ⟨92567097402563895437645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61711398268375930291763 92567097402563895437645)
                  ·
                    refine ⟨34712661525961460789117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92567097402563895437645 34712661525961460789117)
                    ·
                      refine ⟨13017248072235547795919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34712661525961460789117 13017248072235547795919)
                      ·
                        rfl

theorem cell23_25351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_25351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25351 prefixEnd_25351 := by exact prefixLift 25351
  have htrace : WordTrace (prefixWord ++ tailWord_25351) baseStart_25351 baseEnd_25351 := by
    simpa [prefixWord, tailWord_25351, baseEnd_25351] using wordTrace_append hprefix tailTrace_25351
  have hstable : (prefixWord ++ tailWord_25351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25351).length < 2 ^ (prefixWord ++ tailWord_25351).sum := by decide
  have hdescent : baseEnd_25351 < baseStart_25351 := by decide
  rcases family_descends (prefixWord ++ tailWord_25351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25361 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 1, 3, 2]
def baseStart_25361 : Nat := 118140960795 + 25361 * 2 ^ 59
def prefixEnd_25361 : Nat := 4983230072969 + 3 ^ 40 * 25361 * 2
def baseEnd_25361 : Nat := 13022382878780508670873

theorem tailTrace_25361 : CollatzResearch.WordTrace tailWord_25361 prefixEnd_25361 13022382878780508670873 := by
  unfold tailWord_25361
  simp only [CollatzResearch.WordTrace]
  refine ⟨924991661128903159075937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 616661107419268772717291 924991661128903159075937)
  ·
    refine ⟨693743745846677369306953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 924991661128903159075937 693743745846677369306953)
    ·
      refine ⟨520307809385008026980215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 693743745846677369306953 520307809385008026980215)
      ·
        refine ⟨780461714077512040470323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520307809385008026980215 780461714077512040470323)
        ·
          refine ⟨1170692571116268060705485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780461714077512040470323 1170692571116268060705485)
          ·
            refine ⟨439009714168600522764557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1170692571116268060705485 439009714168600522764557)
            ·
              refine ⟨164628642813225196036709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439009714168600522764557 164628642813225196036709)
              ·
                refine ⟨30867870527479724256883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164628642813225196036709 30867870527479724256883)
                ·
                  refine ⟨46301805791219586385325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30867870527479724256883 46301805791219586385325)
                  ·
                    refine ⟨17363177171707344894497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46301805791219586385325 17363177171707344894497)
                    ·
                      refine ⟨13022382878780508670873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17363177171707344894497 13022382878780508670873)
                      ·
                        rfl

theorem cell23_25361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_25361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25361 prefixEnd_25361 := by exact prefixLift 25361
  have htrace : WordTrace (prefixWord ++ tailWord_25361) baseStart_25361 baseEnd_25361 := by
    simpa [prefixWord, tailWord_25361, baseEnd_25361] using wordTrace_append hprefix tailTrace_25361
  have hstable : (prefixWord ++ tailWord_25361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25361).length < 2 ^ (prefixWord ++ tailWord_25361).sum := by decide
  have hdescent : baseEnd_25361 < baseStart_25361 := by decide
  rcases family_descends (prefixWord ++ tailWord_25361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25378 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_25378 : Nat := 118140960795 + 25378 * 2 ^ 59
def prefixEnd_25378 : Nat := 4983230072969 + 3 ^ 40 * 25378 * 2
def baseEnd_25378 : Nat := 13031112049906942158295

theorem tailTrace_25378 : CollatzResearch.WordTrace tailWord_25378 prefixEnd_25378 13031112049906942158295 := by
  unfold tailWord_25378
  simp only [CollatzResearch.WordTrace]
  refine ⟨231402925516828765611197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 617074468044876708296525 231402925516828765611197)
  ·
    refine ⟨86776097068810787104199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231402925516828765611197 86776097068810787104199)
    ·
      refine ⟨130164145603216180656299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86776097068810787104199 130164145603216180656299)
      ·
        refine ⟨195246218404824270984449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130164145603216180656299 195246218404824270984449)
        ·
          refine ⟨146434663803618203238337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195246218404824270984449 146434663803618203238337)
          ·
            refine ⟨109825997852713652428753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146434663803618203238337 109825997852713652428753)
            ·
              refine ⟨82369498389535239321565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109825997852713652428753 82369498389535239321565)
              ·
                refine ⟨30888561896075714745587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82369498389535239321565 30888561896075714745587)
                ·
                  refine ⟨46332842844113572118381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30888561896075714745587 46332842844113572118381)
                  ·
                    refine ⟨17374816066542589544393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46332842844113572118381 17374816066542589544393)
                    ·
                      refine ⟨13031112049906942158295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17374816066542589544393 13031112049906942158295)
                      ·
                        rfl

theorem cell23_25378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_25378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25378 prefixEnd_25378 := by exact prefixLift 25378
  have htrace : WordTrace (prefixWord ++ tailWord_25378) baseStart_25378 baseEnd_25378 := by
    simpa [prefixWord, tailWord_25378, baseEnd_25378] using wordTrace_append hprefix tailTrace_25378
  have hstable : (prefixWord ++ tailWord_25378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25378).length < 2 ^ (prefixWord ++ tailWord_25378).sum := by decide
  have hdescent : baseEnd_25378 < baseStart_25378 := by decide
  rcases family_descends (prefixWord ++ tailWord_25378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25394 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_25394 : Nat := 118140960795 + 25394 * 2 ^ 59
def prefixEnd_25394 : Nat := 4983230072969 + 3 ^ 40 * 25394 * 2
def baseEnd_25394 : Nat := 13039327740378879558221

theorem tailTrace_25394 : CollatzResearch.WordTrace tailWord_25394 prefixEnd_25394 13039327740378879558221 := by
  unfold tailWord_25394
  simp only [CollatzResearch.WordTrace]
  refine ⟨231548817502337448756809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 617463513339566530018157 231548817502337448756809)
  ·
    refine ⟨173661613126753086567607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231548817502337448756809 173661613126753086567607)
    ·
      refine ⟨260492419690129629851411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173661613126753086567607 260492419690129629851411)
      ·
        refine ⟨390738629535194444777117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260492419690129629851411 390738629535194444777117)
        ·
          refine ⟨146526986075697916791419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390738629535194444777117 146526986075697916791419)
          ·
            refine ⟨219790479113546875187129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146526986075697916791419 219790479113546875187129)
            ·
              refine ⟨164842859335160156390347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219790479113546875187129 164842859335160156390347)
              ·
                refine ⟨247264289002740234585521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164842859335160156390347 247264289002740234585521)
                ·
                  refine ⟨185448216752055175939141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247264289002740234585521 185448216752055175939141)
                  ·
                    refine ⟨34771540641010345488589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185448216752055175939141 34771540641010345488589)
                    ·
                      refine ⟨13039327740378879558221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34771540641010345488589 13039327740378879558221)
                      ·
                        rfl

theorem cell23_25394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_25394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25394 prefixEnd_25394 := by exact prefixLift 25394
  have htrace : WordTrace (prefixWord ++ tailWord_25394) baseStart_25394 baseEnd_25394 := by
    simpa [prefixWord, tailWord_25394, baseEnd_25394] using wordTrace_append hprefix tailTrace_25394
  have hstable : (prefixWord ++ tailWord_25394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25394).length < 2 ^ (prefixWord ++ tailWord_25394).sum := by decide
  have hdescent : baseEnd_25394 < baseStart_25394 := by decide
  rcases family_descends (prefixWord ++ tailWord_25394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25402 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3]
def baseStart_25402 : Nat := 118140960795 + 25402 * 2 ^ 59
def prefixEnd_25402 : Nat := 4983230072969 + 3 ^ 40 * 25402 * 2
def baseEnd_25402 : Nat := 13043435585614848258185

theorem tailTrace_25402 : CollatzResearch.WordTrace tailWord_25402 prefixEnd_25402 13043435585614848258185 := by
  unfold tailWord_25402
  simp only [CollatzResearch.WordTrace]
  refine ⟨231621763495091790329615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 617658035986911440878973 231621763495091790329615)
  ·
    refine ⟨347432645242637685494423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231621763495091790329615 347432645242637685494423)
    ·
      refine ⟨521148967863956528241635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347432645242637685494423 521148967863956528241635)
      ·
        refine ⟨781723451795934792362453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521148967863956528241635 781723451795934792362453)
        ·
          refine ⟨18321643401467221695995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 781723451795934792362453 18321643401467221695995)
          ·
            refine ⟨27482465102200832543993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18321643401467221695995 27482465102200832543993)
            ·
              refine ⟨20611848826650624407995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27482465102200832543993 20611848826650624407995)
              ·
                refine ⟨30917773239975936611993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20611848826650624407995 30917773239975936611993)
                ·
                  refine ⟨23188329929981952458995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30917773239975936611993 23188329929981952458995)
                  ·
                    refine ⟨34782494894972928688493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23188329929981952458995 34782494894972928688493)
                    ·
                      refine ⟨13043435585614848258185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34782494894972928688493 13043435585614848258185)
                      ·
                        rfl

theorem cell23_25402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_25402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25402 prefixEnd_25402 := by exact prefixLift 25402
  have htrace : WordTrace (prefixWord ++ tailWord_25402) baseStart_25402 baseEnd_25402 := by
    simpa [prefixWord, tailWord_25402, baseEnd_25402] using wordTrace_append hprefix tailTrace_25402
  have hstable : (prefixWord ++ tailWord_25402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25402).length < 2 ^ (prefixWord ++ tailWord_25402).sum := by decide
  have hdescent : baseEnd_25402 < baseStart_25402 := by decide
  rcases family_descends (prefixWord ++ tailWord_25402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25427 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 1, 7]
def baseStart_25427 : Nat := 118140960795 + 25427 * 2 ^ 59
def prefixEnd_25427 : Nat := 4983230072969 + 3 ^ 40 * 25427 * 2
def baseEnd_25427 : Nat := 4352090867325750148523

theorem tailTrace_25427 : CollatzResearch.WordTrace tailWord_25427 prefixEnd_25427 4352090867325750148523 := by
  unfold tailWord_25427
  simp only [CollatzResearch.WordTrace]
  refine ⟨927398878889796430978535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 618265919259864287319023 927398878889796430978535)
  ·
    refine ⟨1391098318334694646467803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 927398878889796430978535 1391098318334694646467803)
    ·
      refine ⟨2086647477502041969701705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391098318334694646467803 2086647477502041969701705)
      ·
        refine ⟨1564985608126531477276279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2086647477502041969701705 1564985608126531477276279)
        ·
          refine ⟨2347478412189797215914419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564985608126531477276279 2347478412189797215914419)
          ·
            refine ⟨3521217618284695823871629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347478412189797215914419 3521217618284695823871629)
            ·
              refine ⟨1320456606856760933951861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3521217618284695823871629 1320456606856760933951861)
              ·
                refine ⟨123792806892821337557987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1320456606856760933951861 123792806892821337557987)
                ·
                  refine ⟨185689210339232006336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123792806892821337557987 185689210339232006336981)
                  ·
                    refine ⟨4352090867325750148523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185689210339232006336981 4352090867325750148523)
                    ·
                      rfl

theorem cell23_25427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 7].length) (baseStart_25427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25427 prefixEnd_25427 := by exact prefixLift 25427
  have htrace : WordTrace (prefixWord ++ tailWord_25427) baseStart_25427 baseEnd_25427 := by
    simpa [prefixWord, tailWord_25427, baseEnd_25427] using wordTrace_append hprefix tailTrace_25427
  have hstable : (prefixWord ++ tailWord_25427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25427).length < 2 ^ (prefixWord ++ tailWord_25427).sum := by decide
  have hdescent : baseEnd_25427 < baseStart_25427 := by decide
  rcases family_descends (prefixWord ++ tailWord_25427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25442 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_25442 : Nat := 118140960795 + 25442 * 2 ^ 59
def prefixEnd_25442 : Nat := 4983230072969 + 3 ^ 40 * 25442 * 2
def baseEnd_25442 : Nat := 13063974811794691758001

theorem tailTrace_25442 : CollatzResearch.WordTrace tailWord_25442 prefixEnd_25442 13063974811794691758001 := by
  unfold tailWord_25442
  simp only [CollatzResearch.WordTrace]
  refine ⟨231986493458863498193645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 618630649223635995183053 231986493458863498193645)
  ·
    refine ⟨86994935047073811822617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231986493458863498193645 86994935047073811822617)
    ·
      refine ⟨65246201285305358866963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86994935047073811822617 65246201285305358866963)
      ·
        refine ⟨97869301927958038300445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65246201285305358866963 97869301927958038300445)
        ·
          refine ⟨36700988222984264362667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97869301927958038300445 36700988222984264362667)
          ·
            refine ⟨55051482334476396544001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36700988222984264362667 55051482334476396544001)
            ·
              refine ⟨41288611750857297408001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55051482334476396544001 41288611750857297408001)
              ·
                refine ⟨30966458813142973056001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41288611750857297408001 30966458813142973056001)
                ·
                  refine ⟨23224844109857229792001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30966458813142973056001 23224844109857229792001)
                  ·
                    refine ⟨17418633082392922344001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23224844109857229792001 17418633082392922344001)
                    ·
                      refine ⟨13063974811794691758001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17418633082392922344001 13063974811794691758001)
                      ·
                        rfl

theorem cell23_25442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_25442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25442 prefixEnd_25442 := by exact prefixLift 25442
  have htrace : WordTrace (prefixWord ++ tailWord_25442) baseStart_25442 baseEnd_25442 := by
    simpa [prefixWord, tailWord_25442, baseEnd_25442] using wordTrace_append hprefix tailTrace_25442
  have hstable : (prefixWord ++ tailWord_25442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25442).length < 2 ^ (prefixWord ++ tailWord_25442).sum := by decide
  have hdescent : baseEnd_25442 < baseStart_25442 := by decide
  rcases family_descends (prefixWord ++ tailWord_25442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25448 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 5]
def baseStart_25448 : Nat := 118140960795 + 25448 * 2 ^ 59
def prefixEnd_25448 : Nat := 4983230072969 + 3 ^ 40 * 25448 * 2
def baseEnd_25448 : Nat := 1451895077302407586997

theorem tailTrace_25448 : CollatzResearch.WordTrace tailWord_25448 prefixEnd_25448 1451895077302407586997 := by
  unfold tailWord_25448
  simp only [CollatzResearch.WordTrace]
  refine ⟨464082405906858508746499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 618776541209144678328665 464082405906858508746499)
  ·
    refine ⟨696123608860287763119749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 464082405906858508746499 696123608860287763119749)
    ·
      refine ⟨130523176661303955584953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 696123608860287763119749 130523176661303955584953)
      ·
        refine ⟨97892382495977966688715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130523176661303955584953 97892382495977966688715)
        ·
          refine ⟨146838573743966950033073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97892382495977966688715 146838573743966950033073)
          ·
            refine ⟨110128930307975212524805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146838573743966950033073 110128930307975212524805)
            ·
              refine ⟨20649174432745352348401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110128930307975212524805 20649174432745352348401)
              ·
                refine ⟨15486880824559014261301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20649174432745352348401 15486880824559014261301)
                ·
                  refine ⟨1451895077302407586997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15486880824559014261301 1451895077302407586997)
                  ·
                    rfl

theorem cell23_25448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 5].length) (baseStart_25448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25448 prefixEnd_25448 := by exact prefixLift 25448
  have htrace : WordTrace (prefixWord ++ tailWord_25448) baseStart_25448 baseEnd_25448 := by
    simpa [prefixWord, tailWord_25448, baseEnd_25448] using wordTrace_append hprefix tailTrace_25448
  have hstable : (prefixWord ++ tailWord_25448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25448).length < 2 ^ (prefixWord ++ tailWord_25448).sum := by decide
  have hdescent : baseEnd_25448 < baseStart_25448 := by decide
  rcases family_descends (prefixWord ++ tailWord_25448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25481 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_25481 : Nat := 118140960795 + 25481 * 2 ^ 59
def prefixEnd_25481 : Nat := 4983230072969 + 3 ^ 40 * 25481 * 2
def baseEnd_25481 : Nat := 13084000557320039170321

theorem tailTrace_25481 : CollatzResearch.WordTrace tailWord_25481 prefixEnd_25481 13084000557320039170321 := by
  unfold tailWord_25481
  simp only [CollatzResearch.WordTrace]
  refine ⟨929368420694163653444297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 619578947129442435629531 929368420694163653444297)
  ·
    refine ⟨697026315520622740083223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 929368420694163653444297 697026315520622740083223)
    ·
      refine ⟨1045539473280934110124835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 697026315520622740083223 1045539473280934110124835)
      ·
        refine ⟨1568309209921401165187253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045539473280934110124835 1568309209921401165187253)
        ·
          refine ⟨147028988430131359236305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1568309209921401165187253 147028988430131359236305)
          ·
            refine ⟨110271741322598519427229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147028988430131359236305 110271741322598519427229)
            ·
              refine ⟨41351902995974444785211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110271741322598519427229 41351902995974444785211)
              ·
                refine ⟨62027854493961667177817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41351902995974444785211 62027854493961667177817)
                ·
                  refine ⟨46520890870471250383363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62027854493961667177817 46520890870471250383363)
                  ·
                    refine ⟨69781336305706875575045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46520890870471250383363 69781336305706875575045)
                    ·
                      refine ⟨13084000557320039170321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 69781336305706875575045 13084000557320039170321)
                      ·
                        rfl

theorem cell23_25481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_25481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25481 prefixEnd_25481 := by exact prefixLift 25481
  have htrace : WordTrace (prefixWord ++ tailWord_25481) baseStart_25481 baseEnd_25481 := by
    simpa [prefixWord, tailWord_25481, baseEnd_25481] using wordTrace_append hprefix tailTrace_25481
  have hstable : (prefixWord ++ tailWord_25481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25481).length < 2 ^ (prefixWord ++ tailWord_25481).sum := by decide
  have hdescent : baseEnd_25481 < baseStart_25481 := by decide
  rcases family_descends (prefixWord ++ tailWord_25481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25501 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_25501 : Nat := 118140960795 + 25501 * 2 ^ 59
def prefixEnd_25501 : Nat := 4983230072969 + 3 ^ 40 * 25501 * 2
def baseEnd_25501 : Nat := 13094270170409960920229

theorem tailTrace_25501 : CollatzResearch.WordTrace tailWord_25501 prefixEnd_25501 13094270170409960920229 := by
  unfold tailWord_25501
  simp only [CollatzResearch.WordTrace]
  refine ⟨930097880621707069172357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 620065253747804712781571 930097880621707069172357)
  ·
    refine ⟨174393352616570075469817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 930097880621707069172357 174393352616570075469817)
    ·
      refine ⟨130795014462427556602363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174393352616570075469817 130795014462427556602363)
      ·
        refine ⟨196192521693641334903545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130795014462427556602363 196192521693641334903545)
        ·
          refine ⟨147144391270231001177659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196192521693641334903545 147144391270231001177659)
          ·
            refine ⟨220716586905346501766489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147144391270231001177659 220716586905346501766489)
            ·
              refine ⟨165537440179009876324867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220716586905346501766489 165537440179009876324867)
              ·
                refine ⟨248306160268514814487301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165537440179009876324867 248306160268514814487301)
                ·
                  refine ⟨46557405050346527716369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248306160268514814487301 46557405050346527716369)
                  ·
                    refine ⟨34918053787759895787277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46557405050346527716369 34918053787759895787277)
                    ·
                      refine ⟨13094270170409960920229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 34918053787759895787277 13094270170409960920229)
                      ·
                        rfl

theorem cell23_25501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_25501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25501 prefixEnd_25501 := by exact prefixLift 25501
  have htrace : WordTrace (prefixWord ++ tailWord_25501) baseStart_25501 baseEnd_25501 := by
    simpa [prefixWord, tailWord_25501, baseEnd_25501] using wordTrace_append hprefix tailTrace_25501
  have hstable : (prefixWord ++ tailWord_25501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25501).length < 2 ^ (prefixWord ++ tailWord_25501).sum := by decide
  have hdescent : baseEnd_25501 < baseStart_25501 := by decide
  rcases family_descends (prefixWord ++ tailWord_25501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25508 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_25508 : Nat := 118140960795 + 25508 * 2 ^ 59
def prefixEnd_25508 : Nat := 4983230072969 + 3 ^ 40 * 25508 * 2
def baseEnd_25508 : Nat := 4365954844997144510899

theorem tailTrace_25508 : CollatzResearch.WordTrace tailWord_25508 prefixEnd_25508 4365954844997144510899 := by
  unfold tailWord_25508
  simp only [CollatzResearch.WordTrace]
  refine ⟨465176595798173632338589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 620235461064231509784785 465176595798173632338589)
  ·
    refine ⟨174441223424315112126971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 465176595798173632338589 174441223424315112126971)
    ·
      refine ⟨261661835136472668190457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174441223424315112126971 261661835136472668190457)
      ·
        refine ⟨196246376352354501142843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261661835136472668190457 196246376352354501142843)
        ·
          refine ⟨294369564528531751714265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196246376352354501142843 294369564528531751714265)
          ·
            refine ⟨220777173396398813785699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294369564528531751714265 220777173396398813785699)
            ·
              refine ⟨331165760094598220678549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220777173396398813785699 331165760094598220678549)
              ·
                refine ⟨15523395004434291594307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331165760094598220678549 15523395004434291594307)
                ·
                  refine ⟨23285092506651437391461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15523395004434291594307 23285092506651437391461)
                  ·
                    refine ⟨4365954844997144510899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23285092506651437391461 4365954844997144510899)
                    ·
                      rfl

theorem cell23_25508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_25508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25508 prefixEnd_25508 := by exact prefixLift 25508
  have htrace : WordTrace (prefixWord ++ tailWord_25508) baseStart_25508 baseEnd_25508 := by
    simpa [prefixWord, tailWord_25508, baseEnd_25508] using wordTrace_append hprefix tailTrace_25508
  have hstable : (prefixWord ++ tailWord_25508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25508).length < 2 ^ (prefixWord ++ tailWord_25508).sum := by decide
  have hdescent : baseEnd_25508 < baseStart_25508 := by decide
  rcases family_descends (prefixWord ++ tailWord_25508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25551 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 1, 5]
def baseStart_25551 : Nat := 118140960795 + 25551 * 2 ^ 59
def prefixEnd_25551 : Nat := 4983230072969 + 3 ^ 40 * 25551 * 2
def baseEnd_25551 : Nat := 4373314734378255098333

theorem tailTrace_25551 : CollatzResearch.WordTrace tailWord_25551 prefixEnd_25551 4373314734378255098333 := by
  unfold tailWord_25551
  simp only [CollatzResearch.WordTrace]
  refine ⟨931921530440565608492507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 621281020293710405661671 931921530440565608492507)
  ·
    refine ⟨1397882295660848412738761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 931921530440565608492507 1397882295660848412738761)
    ·
      refine ⟨1048411721745636309554071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397882295660848412738761 1048411721745636309554071)
      ·
        refine ⟨1572617582618454464331107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048411721745636309554071 1572617582618454464331107)
        ·
          refine ⟨2358926373927681696496661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572617582618454464331107 2358926373927681696496661)
          ·
            refine ⟨110574673777860079523281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2358926373927681696496661 110574673777860079523281)
            ·
              refine ⟨82931005333395059642461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110574673777860079523281 82931005333395059642461)
              ·
                refine ⟨31099127000023147365923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82931005333395059642461 31099127000023147365923)
                ·
                  refine ⟨46648690500034721048885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31099127000023147365923 46648690500034721048885)
                  ·
                    refine ⟨4373314734378255098333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46648690500034721048885 4373314734378255098333)
                    ·
                      rfl

theorem cell23_25551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_25551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25551 prefixEnd_25551 := by exact prefixLift 25551
  have htrace : WordTrace (prefixWord ++ tailWord_25551) baseStart_25551 baseEnd_25551 := by
    simpa [prefixWord, tailWord_25551, baseEnd_25551] using wordTrace_append hprefix tailTrace_25551
  have hstable : (prefixWord ++ tailWord_25551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25551).length < 2 ^ (prefixWord ++ tailWord_25551).sum := by decide
  have hdescent : baseEnd_25551 < baseStart_25551 := by decide
  rcases family_descends (prefixWord ++ tailWord_25551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25565 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_25565 : Nat := 118140960795 + 25565 * 2 ^ 59
def prefixEnd_25565 : Nat := 4983230072969 + 3 ^ 40 * 25565 * 2
def baseEnd_25565 : Nat := 13127132932297710519935

theorem tailTrace_25565 : CollatzResearch.WordTrace tailWord_25565 prefixEnd_25565 13127132932297710519935 := by
  unfold tailWord_25565
  simp only [CollatzResearch.WordTrace]
  refine ⟨932432152389845999502149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 621621434926563999668099 932432152389845999502149)
  ·
    refine ⟨174831028573096124906653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 932432152389845999502149 174831028573096124906653)
    ·
      refine ⟨65561635714911046839995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174831028573096124906653 65561635714911046839995)
      ·
        refine ⟨98342453572366570259993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65561635714911046839995 98342453572366570259993)
        ·
          refine ⟨73756840179274927694995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98342453572366570259993 73756840179274927694995)
          ·
            refine ⟨110635260268912391542493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73756840179274927694995 110635260268912391542493)
            ·
              refine ⟨41488222600842146828435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110635260268912391542493 41488222600842146828435)
              ·
                refine ⟨62232333901263220242653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41488222600842146828435 62232333901263220242653)
                ·
                  refine ⟨23337125212973707590995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62232333901263220242653 23337125212973707590995)
                  ·
                    refine ⟨35005687819460561386493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23337125212973707590995 35005687819460561386493)
                    ·
                      refine ⟨13127132932297710519935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 35005687819460561386493 13127132932297710519935)
                      ·
                        rfl

theorem cell23_25565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_25565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25565 prefixEnd_25565 := by exact prefixLift 25565
  have htrace : WordTrace (prefixWord ++ tailWord_25565) baseStart_25565 baseEnd_25565 := by
    simpa [prefixWord, tailWord_25565, baseEnd_25565] using wordTrace_append hprefix tailTrace_25565
  have hstable : (prefixWord ++ tailWord_25565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25565).length < 2 ^ (prefixWord ++ tailWord_25565).sum := by decide
  have hdescent : baseEnd_25565 < baseStart_25565 := by decide
  rcases family_descends (prefixWord ++ tailWord_25565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25571 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 4]
def baseStart_25571 : Nat := 118140960795 + 25571 * 2 ^ 59
def prefixEnd_25571 : Nat := 4983230072969 + 3 ^ 40 * 25571 * 2
def baseEnd_25571 : Nat := 13130213816224687044907

theorem tailTrace_25571 : CollatzResearch.WordTrace tailWord_25571 prefixEnd_25571 13130213816224687044907 := by
  unfold tailWord_25571
  simp only [CollatzResearch.WordTrace]
  refine ⟨932650990368109024220567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 621767326912072682813711 932650990368109024220567)
  ·
    refine ⟨1398976485552163536330851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 932650990368109024220567 1398976485552163536330851)
    ·
      refine ⟨2098464728328245304496277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398976485552163536330851 2098464728328245304496277)
      ·
        refine ⟨98365534140386498648263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2098464728328245304496277 98365534140386498648263)
        ·
          refine ⟨147548301210579747972395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98365534140386498648263 147548301210579747972395)
          ·
            refine ⟨221322451815869621958593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147548301210579747972395 221322451815869621958593)
            ·
              refine ⟨165991838861902216468945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221322451815869621958593 165991838861902216468945)
              ·
                refine ⟨124493879146426662351709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165991838861902216468945 124493879146426662351709)
                ·
                  refine ⟨46685204679909998381891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124493879146426662351709 46685204679909998381891)
                  ·
                    refine ⟨70027807019864997572837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46685204679909998381891 70027807019864997572837)
                    ·
                      refine ⟨13130213816224687044907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 70027807019864997572837 13130213816224687044907)
                      ·
                        rfl

theorem cell23_25571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_25571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25571 prefixEnd_25571 := by exact prefixLift 25571
  have htrace : WordTrace (prefixWord ++ tailWord_25571) baseStart_25571 baseEnd_25571 := by
    simpa [prefixWord, tailWord_25571, baseEnd_25571] using wordTrace_append hprefix tailTrace_25571
  have hstable : (prefixWord ++ tailWord_25571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25571).length < 2 ^ (prefixWord ++ tailWord_25571).sum := by decide
  have hdescent : baseEnd_25571 < baseStart_25571 := by decide
  rcases family_descends (prefixWord ++ tailWord_25571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25601 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_25601 : Nat := 118140960795 + 25601 * 2 ^ 59
def prefixEnd_25601 : Nat := 4983230072969 + 3 ^ 40 * 25601 * 2
def baseEnd_25601 : Nat := 13145618235859569669769

theorem tailTrace_25601 : CollatzResearch.WordTrace tailWord_25601 prefixEnd_25601 13145618235859569669769 := by
  unfold tailWord_25601
  simp only [CollatzResearch.WordTrace]
  refine ⟨933745180259424147812657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 622496786839616098541771 933745180259424147812657)
  ·
    refine ⟨700308885194568110859493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 933745180259424147812657 700308885194568110859493)
    ·
      refine ⟨131307915973981520786155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 700308885194568110859493 131307915973981520786155)
      ·
        refine ⟨196961873960972281179233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131307915973981520786155 196961873960972281179233)
        ·
          refine ⟨147721405470729210884425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196961873960972281179233 147721405470729210884425)
          ·
            refine ⟨110791054103046908163319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147721405470729210884425 110791054103046908163319)
            ·
              refine ⟨166186581154570362244979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110791054103046908163319 166186581154570362244979)
              ·
                refine ⟨249279871731855543367469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166186581154570362244979 249279871731855543367469)
                ·
                  refine ⟨93479951899445828762801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249279871731855543367469 93479951899445828762801)
                  ·
                    refine ⟨70109963924584371572101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93479951899445828762801 70109963924584371572101)
                    ·
                      refine ⟨13145618235859569669769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 70109963924584371572101 13145618235859569669769)
                      ·
                        rfl

theorem cell23_25601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_25601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25601 prefixEnd_25601 := by exact prefixLift 25601
  have htrace : WordTrace (prefixWord ++ tailWord_25601) baseStart_25601 baseEnd_25601 := by
    simpa [prefixWord, tailWord_25601, baseEnd_25601] using wordTrace_append hprefix tailTrace_25601
  have hstable : (prefixWord ++ tailWord_25601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25601).length < 2 ^ (prefixWord ++ tailWord_25601).sum := by decide
  have hdescent : baseEnd_25601 < baseStart_25601 := by decide
  rcases family_descends (prefixWord ++ tailWord_25601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25608 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_25608 : Nat := 118140960795 + 25608 * 2 ^ 59
def prefixEnd_25608 : Nat := 4983230072969 + 3 ^ 40 * 25608 * 2
def baseEnd_25608 : Nat := 13149212600441042282237

theorem tailTrace_25608 : CollatzResearch.WordTrace tailWord_25608 prefixEnd_25608 13149212600441042282237 := by
  unfold tailWord_25608
  simp only [CollatzResearch.WordTrace]
  refine ⟨467000245617032171658739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 622666994156042895544985 467000245617032171658739)
  ·
    refine ⟨700500368425548257488109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 467000245617032171658739 700500368425548257488109)
    ·
      refine ⟨262687638159580596558041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 700500368425548257488109 262687638159580596558041)
      ·
        refine ⟨197015728619685447418531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262687638159580596558041 197015728619685447418531)
        ·
          refine ⟨295523592929528171127797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197015728619685447418531 295523592929528171127797)
          ·
            refine ⟨27705336837143266043231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295523592929528171127797 27705336837143266043231)
            ·
              refine ⟨41558005255714899064847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27705336837143266043231 41558005255714899064847)
              ·
                refine ⟨62337007883572348597271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41558005255714899064847 62337007883572348597271)
                ·
                  refine ⟨93505511825358522895907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62337007883572348597271 93505511825358522895907)
                  ·
                    refine ⟨140258267738037784343861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93505511825358522895907 140258267738037784343861)
                    ·
                      refine ⟨13149212600441042282237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 140258267738037784343861 13149212600441042282237)
                      ·
                        rfl

theorem cell23_25608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_25608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25608 prefixEnd_25608 := by exact prefixLift 25608
  have htrace : WordTrace (prefixWord ++ tailWord_25608) baseStart_25608 baseEnd_25608 := by
    simpa [prefixWord, tailWord_25608, baseEnd_25608] using wordTrace_append hprefix tailTrace_25608
  have hstable : (prefixWord ++ tailWord_25608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25608).length < 2 ^ (prefixWord ++ tailWord_25608).sum := by decide
  have hdescent : baseEnd_25608 < baseStart_25608 := by decide
  rcases family_descends (prefixWord ++ tailWord_25608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25628 : List Nat := [2, 2, 3, 1, 4, 2, 1, 8]
def baseStart_25628 : Nat := 118140960795 + 25628 * 2 ^ 59
def prefixEnd_25628 : Nat := 4983230072969 + 3 ^ 40 * 25628 * 2
def baseEnd_25628 : Nat := 487388230130776445635

theorem tailTrace_25628 : CollatzResearch.WordTrace tailWord_25628 prefixEnd_25628 487388230130776445635 := by
  unfold tailWord_25628
  simp only [CollatzResearch.WordTrace]
  refine ⟨467364975580803879522769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 623153300774405172697025 467364975580803879522769)
  ·
    refine ⟨350523731685602909642077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 467364975580803879522769 350523731685602909642077)
    ·
      refine ⟨131446399382101091115779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350523731685602909642077 131446399382101091115779)
      ·
        refine ⟨197169599073151636673669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131446399382101091115779 197169599073151636673669)
        ·
          refine ⟨36969299826215931876313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197169599073151636673669 36969299826215931876313)
          ·
            refine ⟨27726974869661948907235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36969299826215931876313 27726974869661948907235)
            ·
              refine ⟨41590462304492923360853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27726974869661948907235 41590462304492923360853)
              ·
                refine ⟨487388230130776445635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 41590462304492923360853 487388230130776445635)
                ·
                  rfl

theorem cell23_25628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 8].length) (baseStart_25628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25628 prefixEnd_25628 := by exact prefixLift 25628
  have htrace : WordTrace (prefixWord ++ tailWord_25628) baseStart_25628 baseEnd_25628 := by
    simpa [prefixWord, tailWord_25628, baseEnd_25628] using wordTrace_append hprefix tailTrace_25628
  have hstable : (prefixWord ++ tailWord_25628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25628).length < 2 ^ (prefixWord ++ tailWord_25628).sum := by decide
  have hdescent : baseEnd_25628 < baseStart_25628 := by decide
  rcases family_descends (prefixWord ++ tailWord_25628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25648 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 3, 3, 2]
def baseStart_25648 : Nat := 118140960795 + 25648 * 2 ^ 59
def prefixEnd_25648 : Nat := 4983230072969 + 3 ^ 40 * 25648 * 2
def baseEnd_25648 : Nat := 13169751826620885782053

theorem tailTrace_25648 : CollatzResearch.WordTrace tailWord_25648 prefixEnd_25648 13169751826620885782053 := by
  unfold tailWord_25648
  simp only [CollatzResearch.WordTrace]
  refine ⟨467729705544575587386799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 623639607392767449849065 467729705544575587386799)
  ·
    refine ⟨701594558316863381080199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 467729705544575587386799 701594558316863381080199)
    ·
      refine ⟨1052391837475295071620299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701594558316863381080199 1052391837475295071620299)
      ·
        refine ⟨1578587756212942607430449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052391837475295071620299 1578587756212942607430449)
        ·
          refine ⟨1183940817159706955572837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1578587756212942607430449 1183940817159706955572837)
          ·
            refine ⟨221988903217445054169907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1183940817159706955572837 221988903217445054169907)
            ·
              refine ⟨332983354826167581254861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221988903217445054169907 332983354826167581254861)
              ·
                refine ⟨124868758059812842970573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332983354826167581254861 124868758059812842970573)
                ·
                  refine ⟨46825784272429816113965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124868758059812842970573 46825784272429816113965)
                  ·
                    refine ⟨17559669102161181042737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46825784272429816113965 17559669102161181042737)
                    ·
                      refine ⟨13169751826620885782053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17559669102161181042737 13169751826620885782053)
                      ·
                        rfl

theorem cell23_25648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 3, 2].length) (baseStart_25648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25648 prefixEnd_25648 := by exact prefixLift 25648
  have htrace : WordTrace (prefixWord ++ tailWord_25648) baseStart_25648 baseEnd_25648 := by
    simpa [prefixWord, tailWord_25648, baseEnd_25648] using wordTrace_append hprefix tailTrace_25648
  have hstable : (prefixWord ++ tailWord_25648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25648).length < 2 ^ (prefixWord ++ tailWord_25648).sum := by decide
  have hdescent : baseEnd_25648 < baseStart_25648 := by decide
  rcases family_descends (prefixWord ++ tailWord_25648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25671 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 2, 6]
def baseStart_25671 : Nat := 118140960795 + 25671 * 2 ^ 59
def prefixEnd_25671 : Nat := 4983230072969 + 3 ^ 40 * 25671 * 2
def baseEnd_25671 : Nat := 4393853960558098598149

theorem tailTrace_25671 : CollatzResearch.WordTrace tailWord_25671 prefixEnd_25671 4393853960558098598149 := by
  unfold tailWord_25671
  simp only [CollatzResearch.WordTrace]
  refine ⟨936298290005826102860867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 624198860003884068573911 936298290005826102860867)
  ·
    refine ⟨1404447435008739154291301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936298290005826102860867 1404447435008739154291301)
    ·
      refine ⟨263333894064138591429619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1404447435008739154291301 263333894064138591429619)
      ·
        refine ⟨395000841096207887144429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263333894064138591429619 395000841096207887144429)
        ·
          refine ⟨148125315411077957679161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395000841096207887144429 148125315411077957679161)
          ·
            refine ⟨111093986558308468259371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148125315411077957679161 111093986558308468259371)
            ·
              refine ⟨166640979837462702389057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111093986558308468259371 166640979837462702389057)
              ·
                refine ⟨124980734878097026791793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166640979837462702389057 124980734878097026791793)
                ·
                  refine ⟨93735551158572770093845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124980734878097026791793 93735551158572770093845)
                  ·
                    refine ⟨4393853960558098598149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93735551158572770093845 4393853960558098598149)
                    ·
                      rfl

theorem cell23_25671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_25671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25671 prefixEnd_25671 := by exact prefixLift 25671
  have htrace : WordTrace (prefixWord ++ tailWord_25671) baseStart_25671 baseEnd_25671 := by
    simpa [prefixWord, tailWord_25671, baseEnd_25671] using wordTrace_append hprefix tailTrace_25671
  have hstable : (prefixWord ++ tailWord_25671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25671).length < 2 ^ (prefixWord ++ tailWord_25671).sum := by decide
  have hdescent : baseEnd_25671 < baseStart_25671 := by decide
  rcases family_descends (prefixWord ++ tailWord_25671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25681 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_25681 : Nat := 118140960795 + 25681 * 2 ^ 59
def prefixEnd_25681 : Nat := 4983230072969 + 3 ^ 40 * 25681 * 2
def baseEnd_25681 : Nat := 13186696688219256669401

theorem tailTrace_25681 : CollatzResearch.WordTrace tailWord_25681 prefixEnd_25681 13186696688219256669401 := by
  unfold tailWord_25681
  simp only [CollatzResearch.WordTrace]
  refine ⟨936663019969597810724897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 624442013313065207149931 936663019969597810724897)
  ·
    refine ⟨702497264977198358043673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 936663019969597810724897 702497264977198358043673)
    ·
      refine ⟨526872948732898768532755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702497264977198358043673 526872948732898768532755)
      ·
        refine ⟨790309423099348152799133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526872948732898768532755 790309423099348152799133)
        ·
          refine ⟨296366033662255557299675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 790309423099348152799133 296366033662255557299675)
          ·
            refine ⟨444549050493383335949513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296366033662255557299675 444549050493383335949513)
            ·
              refine ⟨333411787870037501962135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444549050493383335949513 333411787870037501962135)
              ·
                refine ⟨500117681805056252943203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333411787870037501962135 500117681805056252943203)
                ·
                  refine ⟨750176522707584379414805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500117681805056252943203 750176522707584379414805)
                  ·
                    refine ⟨35164524501918017785069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 750176522707584379414805 35164524501918017785069)
                    ·
                      refine ⟨13186696688219256669401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 35164524501918017785069 13186696688219256669401)
                      ·
                        rfl

theorem cell23_25681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_25681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25681 prefixEnd_25681 := by exact prefixLift 25681
  have htrace : WordTrace (prefixWord ++ tailWord_25681) baseStart_25681 baseEnd_25681 := by
    simpa [prefixWord, tailWord_25681, baseEnd_25681] using wordTrace_append hprefix tailTrace_25681
  have hstable : (prefixWord ++ tailWord_25681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25681).length < 2 ^ (prefixWord ++ tailWord_25681).sum := by decide
  have hdescent : baseEnd_25681 < baseStart_25681 := by decide
  rcases family_descends (prefixWord ++ tailWord_25681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25701 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 7]
def baseStart_25701 : Nat := 118140960795 + 25701 * 2 ^ 59
def prefixEnd_25701 : Nat := 4983230072969 + 3 ^ 40 * 25701 * 2
def baseEnd_25701 : Nat := 1466329589034353157701

theorem tailTrace_25701 : CollatzResearch.WordTrace tailWord_25701 prefixEnd_25701 1466329589034353157701 := by
  unfold tailWord_25701
  simp only [CollatzResearch.WordTrace]
  refine ⟨937392479897141226452957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 624928319931427484301971 937392479897141226452957)
  ·
    refine ⟨351522179961427959919859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 937392479897141226452957 351522179961427959919859)
    ·
      refine ⟨527283269942141939879789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351522179961427959919859 527283269942141939879789)
      ·
        refine ⟨197731226228303227454921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527283269942141939879789 197731226228303227454921)
        ·
          refine ⟨148298419671227420591191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197731226228303227454921 148298419671227420591191)
          ·
            refine ⟨222447629506841130886787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148298419671227420591191 222447629506841130886787)
            ·
              refine ⟨333671444260261696330181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222447629506841130886787 333671444260261696330181)
              ·
                refine ⟨62563395798799068061909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333671444260261696330181 62563395798799068061909)
                ·
                  refine ⟨1466329589034353157701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62563395798799068061909 1466329589034353157701)
                  ·
                    rfl

theorem cell23_25701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_25701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25701 prefixEnd_25701 := by exact prefixLift 25701
  have htrace : WordTrace (prefixWord ++ tailWord_25701) baseStart_25701 baseEnd_25701 := by
    simpa [prefixWord, tailWord_25701, baseEnd_25701] using wordTrace_append hprefix tailTrace_25701
  have hstable : (prefixWord ++ tailWord_25701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25701).length < 2 ^ (prefixWord ++ tailWord_25701).sum := by decide
  have hdescent : baseEnd_25701 < baseStart_25701 := by decide
  rcases family_descends (prefixWord ++ tailWord_25701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25746 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_25746 : Nat := 118140960795 + 25746 * 2 ^ 59
def prefixEnd_25746 : Nat := 4983230072969 + 3 ^ 40 * 25746 * 2
def baseEnd_25746 : Nat := 13220072930761502356603

theorem tailTrace_25746 : CollatzResearch.WordTrace tailWord_25746 prefixEnd_25746 13220072930761502356603 := by
  unfold tailWord_25746
  simp only [CollatzResearch.WordTrace]
  refine ⟨234758441183528477960273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 626022509822742607894061 234758441183528477960273)
  ·
    refine ⟨176068830887646358470205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234758441183528477960273 176068830887646358470205)
    ·
      refine ⟨66025811582867384426327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176068830887646358470205 66025811582867384426327)
      ·
        refine ⟨99038717374301076639491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66025811582867384426327 99038717374301076639491)
        ·
          refine ⟨148558076061451614959237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99038717374301076639491 148558076061451614959237)
          ·
            refine ⟨27854639261522177804857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148558076061451614959237 27854639261522177804857)
            ·
              refine ⟨20890979446141633353643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27854639261522177804857 20890979446141633353643)
              ·
                refine ⟨31336469169212450030465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20890979446141633353643 31336469169212450030465)
                ·
                  refine ⟨23502351876909337522849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31336469169212450030465 23502351876909337522849)
                  ·
                    refine ⟨17626763907682003142137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23502351876909337522849 17626763907682003142137)
                    ·
                      refine ⟨13220072930761502356603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17626763907682003142137 13220072930761502356603)
                      ·
                        rfl

theorem cell23_25746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_25746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25746 prefixEnd_25746 := by exact prefixLift 25746
  have htrace : WordTrace (prefixWord ++ tailWord_25746) baseStart_25746 baseEnd_25746 := by
    simpa [prefixWord, tailWord_25746, baseEnd_25746] using wordTrace_append hprefix tailTrace_25746
  have hstable : (prefixWord ++ tailWord_25746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25746).length < 2 ^ (prefixWord ++ tailWord_25746).sum := by decide
  have hdescent : baseEnd_25746 < baseStart_25746 := by decide
  rcases family_descends (prefixWord ++ tailWord_25746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25791 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 8]
def baseStart_25791 : Nat := 118140960795 + 25791 * 2 ^ 59
def prefixEnd_25791 : Nat := 4983230072969 + 3 ^ 40 * 25791 * 2
def baseEnd_25791 : Nat := 1471464395579314032655

theorem tailTrace_25791 : CollatzResearch.WordTrace tailWord_25791 prefixEnd_25791 1471464395579314032655 := by
  unfold tailWord_25791
  simp only [CollatzResearch.WordTrace]
  refine ⟨940675049571086597229227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 627116699714057731486151 940675049571086597229227)
  ·
    refine ⟨1411012574356629895843841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940675049571086597229227 1411012574356629895843841)
    ·
      refine ⟨1058259430767472421882881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1411012574356629895843841 1058259430767472421882881)
      ·
        refine ⟨793694573075604316412161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058259430767472421882881 793694573075604316412161)
        ·
          refine ⟨595270929806703237309121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793694573075604316412161 595270929806703237309121)
          ·
            refine ⟨446453197355027427981841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595270929806703237309121 446453197355027427981841)
            ·
              refine ⟨334839898016270570986381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446453197355027427981841 334839898016270570986381)
              ·
                refine ⟨125564961756101464119893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334839898016270570986381 125564961756101464119893)
                ·
                  refine ⟨1471464395579314032655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 125564961756101464119893 1471464395579314032655)
                  ·
                    rfl

theorem cell23_25791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 8].length) (baseStart_25791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25791 prefixEnd_25791 := by exact prefixLift 25791
  have htrace : WordTrace (prefixWord ++ tailWord_25791) baseStart_25791 baseEnd_25791 := by
    simpa [prefixWord, tailWord_25791, baseEnd_25791] using wordTrace_append hprefix tailTrace_25791
  have hstable : (prefixWord ++ tailWord_25791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25791).length < 2 ^ (prefixWord ++ tailWord_25791).sum := by decide
  have hdescent : baseEnd_25791 < baseStart_25791 := by decide
  rcases family_descends (prefixWord ++ tailWord_25791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_25811 : Nat := 118140960795 + 25811 * 2 ^ 59
def prefixEnd_25811 : Nat := 4983230072969 + 3 ^ 40 * 25811 * 2
def baseEnd_25811 : Nat := 13253449173303748043803

theorem tailTrace_25811 : CollatzResearch.WordTrace tailWord_25811 prefixEnd_25811 13253449173303748043803 := by
  unfold tailWord_25811
  simp only [CollatzResearch.WordTrace]
  refine ⟨941404509498630012957287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 627603006332420008638191 941404509498630012957287)
  ·
    refine ⟨1412106764247945019435931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 941404509498630012957287 1412106764247945019435931)
    ·
      refine ⟨2118160146371917529153897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412106764247945019435931 2118160146371917529153897)
      ·
        refine ⟨1588620109778938146865423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2118160146371917529153897 1588620109778938146865423)
        ·
          refine ⟨2382930164668407220298135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588620109778938146865423 2382930164668407220298135)
          ·
            refine ⟨3574395247002610830447203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382930164668407220298135 3574395247002610830447203)
            ·
              refine ⟨5361592870503916245670805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574395247002610830447203 5361592870503916245670805)
              ·
                refine ⟨251324665804871074015819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5361592870503916245670805 251324665804871074015819)
                ·
                  refine ⟨376986998707306611023729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251324665804871074015819 376986998707306611023729)
                  ·
                    refine ⟨282740249030479958267797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376986998707306611023729 282740249030479958267797)
                    ·
                      refine ⟨13253449173303748043803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 282740249030479958267797 13253449173303748043803)
                      ·
                        rfl

theorem cell23_25811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_25811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25811 prefixEnd_25811 := by exact prefixLift 25811
  have htrace : WordTrace (prefixWord ++ tailWord_25811) baseStart_25811 baseEnd_25811 := by
    simpa [prefixWord, tailWord_25811, baseEnd_25811] using wordTrace_append hprefix tailTrace_25811
  have hstable : (prefixWord ++ tailWord_25811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25811).length < 2 ^ (prefixWord ++ tailWord_25811).sum := by decide
  have hdescent : baseEnd_25811 < baseStart_25811 := by decide
  rcases family_descends (prefixWord ++ tailWord_25811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25829 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_25829 : Nat := 118140960795 + 25829 * 2 ^ 59
def prefixEnd_25829 : Nat := 4983230072969 + 3 ^ 40 * 25829 * 2
def baseEnd_25829 : Nat := 4420897275028225872907

theorem tailTrace_25829 : CollatzResearch.WordTrace tailWord_25829 prefixEnd_25829 4420897275028225872907 := by
  unfold tailWord_25829
  simp only [CollatzResearch.WordTrace]
  refine ⟨942061023433419087112541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 628040682288946058075027 942061023433419087112541)
  ·
    refine ⟨353272883787532157667203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 942061023433419087112541 353272883787532157667203)
    ·
      refine ⟨529909325681298236500805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353272883787532157667203 529909325681298236500805)
      ·
        refine ⟨99357998565243419343901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 529909325681298236500805 99357998565243419343901)
        ·
          refine ⟨37259249461966282253963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99357998565243419343901 37259249461966282253963)
          ·
            refine ⟨55888874192949423380945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37259249461966282253963 55888874192949423380945)
            ·
              refine ⟨41916655644712067535709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55888874192949423380945 41916655644712067535709)
              ·
                refine ⟨15718745866767025325891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41916655644712067535709 15718745866767025325891)
                ·
                  refine ⟨23578118800150537988837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15718745866767025325891 23578118800150537988837)
                  ·
                    refine ⟨4420897275028225872907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23578118800150537988837 4420897275028225872907)
                    ·
                      rfl

theorem cell23_25829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_25829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25829 prefixEnd_25829 := by exact prefixLift 25829
  have htrace : WordTrace (prefixWord ++ tailWord_25829) baseStart_25829 baseEnd_25829 := by
    simpa [prefixWord, tailWord_25829, baseEnd_25829] using wordTrace_append hprefix tailTrace_25829
  have hstable : (prefixWord ++ tailWord_25829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25829).length < 2 ^ (prefixWord ++ tailWord_25829).sum := by decide
  have hdescent : baseEnd_25829 < baseStart_25829 := by decide
  rcases family_descends (prefixWord ++ tailWord_25829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25842 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_25842 : Nat := 118140960795 + 25842 * 2 ^ 59
def prefixEnd_25842 : Nat := 4983230072969 + 3 ^ 40 * 25842 * 2
def baseEnd_25842 : Nat := 1474374119288125195129

theorem tailTrace_25842 : CollatzResearch.WordTrace tailWord_25842 prefixEnd_25842 1474374119288125195129 := by
  unfold tailWord_25842
  simp only [CollatzResearch.WordTrace]
  refine ⟨235633793096580576833945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 628356781590881538223853 235633793096580576833945)
  ·
    refine ⟨176725344822435432625459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235633793096580576833945 176725344822435432625459)
    ·
      refine ⟨265088017233653148938189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176725344822435432625459 265088017233653148938189)
      ·
        refine ⟨99408006462619930851821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265088017233653148938189 99408006462619930851821)
        ·
          refine ⟨37278002423482474069433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99408006462619930851821 37278002423482474069433)
          ·
            refine ⟨27958501817611855552075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37278002423482474069433 27958501817611855552075)
            ·
              refine ⟨41937752726417783328113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27958501817611855552075 41937752726417783328113)
              ·
                refine ⟨31453314544813337496085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41937752726417783328113 31453314544813337496085)
                ·
                  refine ⟨1474374119288125195129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31453314544813337496085 1474374119288125195129)
                  ·
                    rfl

theorem cell23_25842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_25842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25842 prefixEnd_25842 := by exact prefixLift 25842
  have htrace : WordTrace (prefixWord ++ tailWord_25842) baseStart_25842 baseEnd_25842 := by
    simpa [prefixWord, tailWord_25842, baseEnd_25842] using wordTrace_append hprefix tailTrace_25842
  have hstable : (prefixWord ++ tailWord_25842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25842).length < 2 ^ (prefixWord ++ tailWord_25842).sum := by decide
  have hdescent : baseEnd_25842 < baseStart_25842 := by decide
  rcases family_descends (prefixWord ++ tailWord_25842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25851 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 12]
def baseStart_25851 : Nat := 118140960795 + 25851 * 2 ^ 59
def prefixEnd_25851 : Nat := 4983230072969 + 3 ^ 40 * 25851 * 2
def baseEnd_25851 : Nat := 4424662799827863847873

theorem tailTrace_25851 : CollatzResearch.WordTrace tailWord_25851 prefixEnd_25851 4424662799827863847873 := by
  unfold tailWord_25851
  simp only [CollatzResearch.WordTrace]
  refine ⟨942863429353716844413407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 628575619569144562942271 942863429353716844413407)
  ·
    refine ⟨1414295144030575266620111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942863429353716844413407 1414295144030575266620111)
    ·
      refine ⟨2121442716045862899930167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414295144030575266620111 2121442716045862899930167)
      ·
        refine ⟨3182164074068794349895251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121442716045862899930167 3182164074068794349895251)
        ·
          refine ⟨4773246111103191524842877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182164074068794349895251 4773246111103191524842877)
          ·
            refine ⟨1789967291663696821816079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4773246111103191524842877 1789967291663696821816079)
            ·
              refine ⟨2684950937495545232724119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789967291663696821816079 2684950937495545232724119)
              ·
                refine ⟨4027426406243317849086179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684950937495545232724119 4027426406243317849086179)
                ·
                  refine ⟨6041139609364976773629269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027426406243317849086179 6041139609364976773629269)
                  ·
                    refine ⟨4424662799827863847873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 6041139609364976773629269 4424662799827863847873)
                    ·
                      rfl

theorem cell23_25851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_25851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25851 prefixEnd_25851 := by exact prefixLift 25851
  have htrace : WordTrace (prefixWord ++ tailWord_25851) baseStart_25851 baseEnd_25851 := by
    simpa [prefixWord, tailWord_25851, baseEnd_25851] using wordTrace_append hprefix tailTrace_25851
  have hstable : (prefixWord ++ tailWord_25851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25851).length < 2 ^ (prefixWord ++ tailWord_25851).sum := by decide
  have hdescent : baseEnd_25851 < baseStart_25851 := by decide
  rcases family_descends (prefixWord ++ tailWord_25851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25909 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_25909 : Nat := 118140960795 + 25909 * 2 ^ 59
def prefixEnd_25909 : Nat := 4983230072969 + 3 ^ 40 * 25909 * 2
def baseEnd_25909 : Nat := 13303770277444364618353

theorem tailTrace_25909 : CollatzResearch.WordTrace tailWord_25909 prefixEnd_25909 13303770277444364618353 := by
  unfold tailWord_25909
  simp only [CollatzResearch.WordTrace]
  refine ⟨944978863143592750024781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 629985908762395166683187 944978863143592750024781)
  ·
    refine ⟨354367073678847281259293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 944978863143592750024781 354367073678847281259293)
    ·
      refine ⟨132887652629567730472235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354367073678847281259293 132887652629567730472235)
      ·
        refine ⟨199331478944351595708353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132887652629567730472235 199331478944351595708353)
        ·
          refine ⟨149498609208263696781265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199331478944351595708353 149498609208263696781265)
          ·
            refine ⟨112123956906197772585949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149498609208263696781265 112123956906197772585949)
            ·
              refine ⟨42046483839824164719731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112123956906197772585949 42046483839824164719731)
              ·
                refine ⟨63069725759736247079597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42046483839824164719731 63069725759736247079597)
                ·
                  refine ⟨23651147159901092654849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63069725759736247079597 23651147159901092654849)
                  ·
                    refine ⟨17738360369925819491137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23651147159901092654849 17738360369925819491137)
                    ·
                      refine ⟨13303770277444364618353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17738360369925819491137 13303770277444364618353)
                      ·
                        rfl

theorem cell23_25909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_25909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25909 prefixEnd_25909 := by exact prefixLift 25909
  have htrace : WordTrace (prefixWord ++ tailWord_25909) baseStart_25909 baseEnd_25909 := by
    simpa [prefixWord, tailWord_25909, baseEnd_25909] using wordTrace_append hprefix tailTrace_25909
  have hstable : (prefixWord ++ tailWord_25909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25909).length < 2 ^ (prefixWord ++ tailWord_25909).sum := by decide
  have hdescent : baseEnd_25909 < baseStart_25909 := by decide
  rcases family_descends (prefixWord ++ tailWord_25909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25919 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 2, 4]
def baseStart_25919 : Nat := 118140960795 + 25919 * 2 ^ 59
def prefixEnd_25919 : Nat := 4983230072969 + 3 ^ 40 * 25919 * 2
def baseEnd_25919 : Nat := 4436301694663108497769

theorem tailTrace_25919 : CollatzResearch.WordTrace tailWord_25919 prefixEnd_25919 4436301694663108497769 := by
  unfold tailWord_25919
  simp only [CollatzResearch.WordTrace]
  refine ⟨945343593107364457888811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 630229062071576305259207 945343593107364457888811)
  ·
    refine ⟨1418015389661046686833217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 945343593107364457888811 1418015389661046686833217)
    ·
      refine ⟨1063511542245785015124913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1418015389661046686833217 1063511542245785015124913)
      ·
        refine ⟨797633656684338761343685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1063511542245785015124913 797633656684338761343685)
        ·
          refine ⟨149556310628313517751941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 797633656684338761343685 149556310628313517751941)
          ·
            refine ⟨28041808242808784578489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149556310628313517751941 28041808242808784578489)
            ·
              refine ⟨21031356182106588433867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28041808242808784578489 21031356182106588433867)
              ·
                refine ⟨31547034273159882650801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21031356182106588433867 31547034273159882650801)
                ·
                  refine ⟨23660275704869911988101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31547034273159882650801 23660275704869911988101)
                  ·
                    refine ⟨4436301694663108497769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23660275704869911988101 4436301694663108497769)
                    ·
                      rfl

theorem cell23_25919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 4].length) (baseStart_25919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25919 prefixEnd_25919 := by exact prefixLift 25919
  have htrace : WordTrace (prefixWord ++ tailWord_25919) baseStart_25919 baseEnd_25919 := by
    simpa [prefixWord, tailWord_25919, baseEnd_25919] using wordTrace_append hprefix tailTrace_25919
  have hstable : (prefixWord ++ tailWord_25919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25919).length < 2 ^ (prefixWord ++ tailWord_25919).sum := by decide
  have hdescent : baseEnd_25919 < baseStart_25919 := by decide
  rcases family_descends (prefixWord ++ tailWord_25919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25926 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_25926 : Nat := 118140960795 + 25926 * 2 ^ 59
def prefixEnd_25926 : Nat := 4983230072969 + 3 ^ 40 * 25926 * 2
def baseEnd_25926 : Nat := 13312499448570798105775

theorem tailTrace_25926 : CollatzResearch.WordTrace tailWord_25926 prefixEnd_25926 13312499448570798105775 := by
  unfold tailWord_25926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549965752562645418551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 630399269388003102262421 29549965752562645418551)
  ·
    refine ⟨44324948628843968127827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29549965752562645418551 44324948628843968127827)
    ·
      refine ⟨66487422943265952191741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44324948628843968127827 66487422943265952191741)
      ·
        refine ⟨24932783603724732071903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66487422943265952191741 24932783603724732071903)
        ·
          refine ⟨37399175405587098107855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24932783603724732071903 37399175405587098107855)
          ·
            refine ⟨56098763108380647161783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37399175405587098107855 56098763108380647161783)
            ·
              refine ⟨84148144662570970742675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56098763108380647161783 84148144662570970742675)
              ·
                refine ⟨126222216993856456114013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84148144662570970742675 126222216993856456114013)
                ·
                  refine ⟨47333331372696171042755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126222216993856456114013 47333331372696171042755)
                  ·
                    refine ⟨70999997059044256564133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47333331372696171042755 70999997059044256564133)
                    ·
                      refine ⟨13312499448570798105775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 70999997059044256564133 13312499448570798105775)
                      ·
                        rfl

theorem cell23_25926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_25926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25926 prefixEnd_25926 := by exact prefixLift 25926
  have htrace : WordTrace (prefixWord ++ tailWord_25926) baseStart_25926 baseEnd_25926 := by
    simpa [prefixWord, tailWord_25926, baseEnd_25926] using wordTrace_append hprefix tailTrace_25926
  have hstable : (prefixWord ++ tailWord_25926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25926).length < 2 ^ (prefixWord ++ tailWord_25926).sum := by decide
  have hdescent : baseEnd_25926 < baseStart_25926 := by decide
  rcases family_descends (prefixWord ++ tailWord_25926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25949 : List Nat := [1, 4, 5, 1, 2, 10]
def baseStart_25949 : Nat := 118140960795 + 25949 * 2 ^ 59
def prefixEnd_25949 : Nat := 4983230072969 + 3 ^ 40 * 25949 * 2
def baseEnd_25949 : Nat := 54832549397630486083

theorem tailTrace_25949 : CollatzResearch.WordTrace tailWord_25949 prefixEnd_25949 54832549397630486083 := by
  unfold tailWord_25949
  simp only [CollatzResearch.WordTrace]
  refine ⟨946437782998679581480901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 630958521999119720987267 946437782998679581480901)
  ·
    refine ⟨177457084312252421527669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 946437782998679581480901 177457084312252421527669)
    ·
      refine ⟨16636601654273664518219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177457084312252421527669 16636601654273664518219)
      ·
        refine ⟨24954902481410496777329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16636601654273664518219 24954902481410496777329)
        ·
          refine ⟨18716176861057872582997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24954902481410496777329 18716176861057872582997)
          ·
            refine ⟨54832549397630486083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 18716176861057872582997 54832549397630486083)
            ·
              rfl

theorem cell23_25949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 10].length) (baseStart_25949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25949 prefixEnd_25949 := by exact prefixLift 25949
  have htrace : WordTrace (prefixWord ++ tailWord_25949) baseStart_25949 baseEnd_25949 := by
    simpa [prefixWord, tailWord_25949, baseEnd_25949] using wordTrace_append hprefix tailTrace_25949
  have hstable : (prefixWord ++ tailWord_25949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25949).length < 2 ^ (prefixWord ++ tailWord_25949).sum := by decide
  have hdescent : baseEnd_25949 < baseStart_25949 := by decide
  rcases family_descends (prefixWord ++ tailWord_25949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25960 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_25960 : Nat := 118140960795 + 25960 * 2 ^ 59
def prefixEnd_25960 : Nat := 4983230072969 + 3 ^ 40 * 25960 * 2
def baseEnd_25960 : Nat := 13329957790823665080619

theorem tailTrace_25960 : CollatzResearch.WordTrace tailWord_25960 prefixEnd_25960 13329957790823665080619 := by
  unfold tailWord_25960
  simp only [CollatzResearch.WordTrace]
  refine ⟨473419492979414230065667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 631225990639218973420889 473419492979414230065667)
  ·
    refine ⟨710129239469121345098501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473419492979414230065667 710129239469121345098501)
    ·
      refine ⟨133149232400460252205969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 710129239469121345098501 133149232400460252205969)
      ·
        refine ⟨99861924300345189154477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133149232400460252205969 99861924300345189154477)
        ·
          refine ⟨37448221612629445932929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99861924300345189154477 37448221612629445932929)
          ·
            refine ⟨28086166209472084449697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37448221612629445932929 28086166209472084449697)
            ·
              refine ⟨21064624657104063337273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28086166209472084449697 21064624657104063337273)
              ·
                refine ⟨15798468492828047502955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21064624657104063337273 15798468492828047502955)
                ·
                  refine ⟨23697702739242071254433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15798468492828047502955 23697702739242071254433)
                  ·
                    refine ⟨17773277054431553440825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23697702739242071254433 17773277054431553440825)
                    ·
                      refine ⟨13329957790823665080619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17773277054431553440825 13329957790823665080619)
                      ·
                        rfl

theorem cell23_25960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_25960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25960 prefixEnd_25960 := by exact prefixLift 25960
  have htrace : WordTrace (prefixWord ++ tailWord_25960) baseStart_25960 baseEnd_25960 := by
    simpa [prefixWord, tailWord_25960, baseEnd_25960] using wordTrace_append hprefix tailTrace_25960
  have hstable : (prefixWord ++ tailWord_25960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25960).length < 2 ^ (prefixWord ++ tailWord_25960).sum := by decide
  have hdescent : baseEnd_25960 < baseStart_25960 := by decide
  rcases family_descends (prefixWord ++ tailWord_25960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25965 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_25965 : Nat := 118140960795 + 25965 * 2 ^ 59
def prefixEnd_25965 : Nat := 4983230072969 + 3 ^ 40 * 25965 * 2
def baseEnd_25965 : Nat := 13332525194096145518095

theorem tailTrace_25965 : CollatzResearch.WordTrace tailWord_25965 prefixEnd_25965 13332525194096145518095 := by
  unfold tailWord_25965
  simp only [CollatzResearch.WordTrace]
  refine ⟨947021350940714314063349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 631347567293809542708899 947021350940714314063349)
  ·
    refine ⟨88783251650691966943439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 947021350940714314063349 88783251650691966943439)
    ·
      refine ⟨133174877476037950415159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88783251650691966943439 133174877476037950415159)
      ·
        refine ⟨199762316214056925622739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133174877476037950415159 199762316214056925622739)
        ·
          refine ⟨299643474321085388434109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199762316214056925622739 299643474321085388434109)
          ·
            refine ⟨112366302870407020662791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299643474321085388434109 112366302870407020662791)
            ·
              refine ⟨168549454305610530994187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112366302870407020662791 168549454305610530994187)
              ·
                refine ⟨252824181458415796491281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168549454305610530994187 252824181458415796491281)
                ·
                  refine ⟨189618136093811847368461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252824181458415796491281 189618136093811847368461)
                  ·
                    refine ⟨71106801035179442763173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189618136093811847368461 71106801035179442763173)
                    ·
                      refine ⟨13332525194096145518095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 71106801035179442763173 13332525194096145518095)
                      ·
                        rfl

theorem cell23_25965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_25965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25965 prefixEnd_25965 := by exact prefixLift 25965
  have htrace : WordTrace (prefixWord ++ tailWord_25965) baseStart_25965 baseEnd_25965 := by
    simpa [prefixWord, tailWord_25965, baseEnd_25965] using wordTrace_append hprefix tailTrace_25965
  have hstable : (prefixWord ++ tailWord_25965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25965).length < 2 ^ (prefixWord ++ tailWord_25965).sum := by decide
  have hdescent : baseEnd_25965 < baseStart_25965 := by decide
  rcases family_descends (prefixWord ++ tailWord_25965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25978 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_25978 : Nat := 118140960795 + 25978 * 2 ^ 59
def prefixEnd_25978 : Nat := 4983230072969 + 3 ^ 40 * 25978 * 2
def baseEnd_25978 : Nat := 13339200442604594655535

theorem tailTrace_25978 : CollatzResearch.WordTrace tailWord_25978 prefixEnd_25978 13339200442604594655535 := by
  unfold tailWord_25978
  simp only [CollatzResearch.WordTrace]
  refine ⟨236873874973404383571647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 631663666595745022857725 236873874973404383571647)
  ·
    refine ⟨355310812460106575357471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236873874973404383571647 355310812460106575357471)
    ·
      refine ⟨532966218690159863036207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355310812460106575357471 532966218690159863036207)
      ·
        refine ⟨799449328035239794554311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532966218690159863036207 799449328035239794554311)
        ·
          refine ⟨1199173992052859691831467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799449328035239794554311 1199173992052859691831467)
          ·
            refine ⟨1798760988079289537747201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199173992052859691831467 1798760988079289537747201)
            ·
              refine ⟨1349070741059467153310401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798760988079289537747201 1349070741059467153310401)
              ·
                refine ⟨1011803055794600364982801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349070741059467153310401 1011803055794600364982801)
                ·
                  refine ⟨758852291845950273737101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011803055794600364982801 758852291845950273737101)
                  ·
                    refine ⟨284569609442231352651413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758852291845950273737101 284569609442231352651413)
                    ·
                      refine ⟨13339200442604594655535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 284569609442231352651413 13339200442604594655535)
                      ·
                        rfl

theorem cell23_25978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_25978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25978 prefixEnd_25978 := by exact prefixLift 25978
  have htrace : WordTrace (prefixWord ++ tailWord_25978) baseStart_25978 baseEnd_25978 := by
    simpa [prefixWord, tailWord_25978, baseEnd_25978] using wordTrace_append hprefix tailTrace_25978
  have hstable : (prefixWord ++ tailWord_25978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25978).length < 2 ^ (prefixWord ++ tailWord_25978).sum := by decide
  have hdescent : baseEnd_25978 < baseStart_25978 := by decide
  rcases family_descends (prefixWord ++ tailWord_25978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25986 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_25986 : Nat := 118140960795 + 25986 * 2 ^ 59
def prefixEnd_25986 : Nat := 4983230072969 + 3 ^ 40 * 25986 * 2
def baseEnd_25986 : Nat := 13343308287840563355499

theorem tailTrace_25986 : CollatzResearch.WordTrace tailWord_25986 prefixEnd_25986 13343308287840563355499 := by
  unfold tailWord_25986
  simp only [CollatzResearch.WordTrace]
  refine ⟨236946820966158725144453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 631858189243089933718541 236946820966158725144453)
  ·
    refine ⟨44427528931154760964585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236946820966158725144453 44427528931154760964585)
    ·
      refine ⟨33320646698366070723439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44427528931154760964585 33320646698366070723439)
      ·
        refine ⟨49980970047549106085159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33320646698366070723439 49980970047549106085159)
        ·
          refine ⟨74971455071323659127739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49980970047549106085159 74971455071323659127739)
          ·
            refine ⟨112457182606985488691609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74971455071323659127739 112457182606985488691609)
            ·
              refine ⟨84342886955239116518707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112457182606985488691609 84342886955239116518707)
              ·
                refine ⟨126514330432858674778061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84342886955239116518707 126514330432858674778061)
                ·
                  refine ⟨47442873912322003041773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126514330432858674778061 47442873912322003041773)
                  ·
                    refine ⟨17791077717120751140665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47442873912322003041773 17791077717120751140665)
                    ·
                      refine ⟨13343308287840563355499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17791077717120751140665 13343308287840563355499)
                      ·
                        rfl

theorem cell23_25986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_25986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_25986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_25986 prefixEnd_25986 := by exact prefixLift 25986
  have htrace : WordTrace (prefixWord ++ tailWord_25986) baseStart_25986 baseEnd_25986 := by
    simpa [prefixWord, tailWord_25986, baseEnd_25986] using wordTrace_append hprefix tailTrace_25986
  have hstable : (prefixWord ++ tailWord_25986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25986).length < 2 ^ (prefixWord ++ tailWord_25986).sum := by decide
  have hdescent : baseEnd_25986 < baseStart_25986 := by decide
  rcases family_descends (prefixWord ++ tailWord_25986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26052 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_26052 : Nat := 118140960795 + 26052 * 2 ^ 59
def prefixEnd_26052 : Nat := 4983230072969 + 3 ^ 40 * 26052 * 2
def baseEnd_26052 : Nat := 4459066003679101710065

theorem tailTrace_26052 : CollatzResearch.WordTrace tailWord_26052 prefixEnd_26052 4459066003679101710065 := by
  unfold tailWord_26052
  simp only [CollatzResearch.WordTrace]
  refine ⟨475097250812764086240205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 633463001083685448320273 475097250812764086240205)
  ·
    refine ⟨178161469054786532340077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 475097250812764086240205 178161469054786532340077)
    ·
      refine ⟨66810550895544949627529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178161469054786532340077 66810550895544949627529)
      ·
        refine ⟨50107913171658712220647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66810550895544949627529 50107913171658712220647)
        ·
          refine ⟨75161869757488068330971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50107913171658712220647 75161869757488068330971)
          ·
            refine ⟨112742804636232102496457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75161869757488068330971 112742804636232102496457)
            ·
              refine ⟨84557103477174076872343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112742804636232102496457 84557103477174076872343)
              ·
                refine ⟨126835655215761115308515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84557103477174076872343 126835655215761115308515)
                ·
                  refine ⟨190253482823641672962773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126835655215761115308515 190253482823641672962773)
                  ·
                    refine ⟨4459066003679101710065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 190253482823641672962773 4459066003679101710065)
                    ·
                      rfl

theorem cell23_26052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_26052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26052 prefixEnd_26052 := by exact prefixLift 26052
  have htrace : WordTrace (prefixWord ++ tailWord_26052) baseStart_26052 baseEnd_26052 := by
    simpa [prefixWord, tailWord_26052, baseEnd_26052] using wordTrace_append hprefix tailTrace_26052
  have hstable : (prefixWord ++ tailWord_26052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26052).length < 2 ^ (prefixWord ++ tailWord_26052).sum := by decide
  have hdescent : baseEnd_26052 < baseStart_26052 := by decide
  rcases family_descends (prefixWord ++ tailWord_26052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26055 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_26055 : Nat := 118140960795 + 26055 * 2 ^ 59
def prefixEnd_26055 : Nat := 4983230072969 + 3 ^ 40 * 26055 * 2
def baseEnd_26055 : Nat := 13378738453000793392681

theorem tailTrace_26055 : CollatzResearch.WordTrace tailWord_26055 prefixEnd_26055 13378738453000793392681 := by
  unfold tailWord_26055
  simp only [CollatzResearch.WordTrace]
  refine ⟨950303920614659684839619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 633535947076439789893079 950303920614659684839619)
  ·
    refine ⟨1425455880921989527259429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 950303920614659684839619 1425455880921989527259429)
    ·
      refine ⟨267272977672873036361143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1425455880921989527259429 267272977672873036361143)
      ·
        refine ⟨400909466509309554541715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267272977672873036361143 400909466509309554541715)
        ·
          refine ⟨601364199763964331812573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400909466509309554541715 601364199763964331812573)
          ·
            refine ⟨225511574911486624429715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601364199763964331812573 225511574911486624429715)
            ·
              refine ⟨338267362367229936644573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225511574911486624429715 338267362367229936644573)
              ·
                refine ⟨126850260887711226241715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338267362367229936644573 126850260887711226241715)
                ·
                  refine ⟨190275391331566839362573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126850260887711226241715 190275391331566839362573)
                  ·
                    refine ⟨71353271749337564760965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190275391331566839362573 71353271749337564760965)
                    ·
                      refine ⟨13378738453000793392681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 71353271749337564760965 13378738453000793392681)
                      ·
                        rfl

theorem cell23_26055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_26055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26055 prefixEnd_26055 := by exact prefixLift 26055
  have htrace : WordTrace (prefixWord ++ tailWord_26055) baseStart_26055 baseEnd_26055 := by
    simpa [prefixWord, tailWord_26055, baseEnd_26055] using wordTrace_append hprefix tailTrace_26055
  have hstable : (prefixWord ++ tailWord_26055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26055).length < 2 ^ (prefixWord ++ tailWord_26055).sum := by decide
  have hdescent : baseEnd_26055 < baseStart_26055 := by decide
  rcases family_descends (prefixWord ++ tailWord_26055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26072 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 4, 4, 2]
def baseStart_26072 : Nat := 118140960795 + 26072 * 2 ^ 59
def prefixEnd_26072 : Nat := 4983230072969 + 3 ^ 40 * 26072 * 2
def baseEnd_26072 : Nat := 13387467624127226880103

theorem tailTrace_26072 : CollatzResearch.WordTrace tailWord_26072 prefixEnd_26072 13387467624127226880103 := by
  unfold tailWord_26072
  simp only [CollatzResearch.WordTrace]
  refine ⟨475461980776535794104235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 633949307702047725472313 475461980776535794104235)
  ·
    refine ⟨713192971164803691156353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 475461980776535794104235 713192971164803691156353)
    ·
      refine ⟨534894728373602768367265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 713192971164803691156353 534894728373602768367265)
      ·
        refine ⟨401171046280202076275449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534894728373602768367265 401171046280202076275449)
        ·
          refine ⟨300878284710151557206587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401171046280202076275449 300878284710151557206587)
          ·
            refine ⟨451317427065227335809881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300878284710151557206587 451317427065227335809881)
            ·
              refine ⟨338488070298920501857411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451317427065227335809881 338488070298920501857411)
              ·
                refine ⟨507732105448380752786117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338488070298920501857411 507732105448380752786117)
                ·
                  refine ⟨95199769771571391147397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507732105448380752786117 95199769771571391147397)
                  ·
                    refine ⟨17849956832169635840137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95199769771571391147397 17849956832169635840137)
                    ·
                      refine ⟨13387467624127226880103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17849956832169635840137 13387467624127226880103)
                      ·
                        rfl

theorem cell23_26072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_26072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26072 prefixEnd_26072 := by exact prefixLift 26072
  have htrace : WordTrace (prefixWord ++ tailWord_26072) baseStart_26072 baseEnd_26072 := by
    simpa [prefixWord, tailWord_26072, baseEnd_26072] using wordTrace_append hprefix tailTrace_26072
  have hstable : (prefixWord ++ tailWord_26072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26072).length < 2 ^ (prefixWord ++ tailWord_26072).sum := by decide
  have hdescent : baseEnd_26072 < baseStart_26072 := by decide
  rcases family_descends (prefixWord ++ tailWord_26072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26109 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_26109 : Nat := 118140960795 + 26109 * 2 ^ 59
def prefixEnd_26109 : Nat := 4983230072969 + 3 ^ 40 * 26109 * 2
def baseEnd_26109 : Nat := 13406466408343582117433

theorem tailTrace_26109 : CollatzResearch.WordTrace tailWord_26109 prefixEnd_26109 13406466408343582117433 := by
  unfold tailWord_26109
  simp only [CollatzResearch.WordTrace]
  refine ⟨952273462419026907305381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 634848974946017938203587 952273462419026907305381)
  ·
    refine ⟨178551274203567545119759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 952273462419026907305381 178551274203567545119759)
    ·
      refine ⟨267826911305351317679639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178551274203567545119759 267826911305351317679639)
      ·
        refine ⟨401740366958026976519459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267826911305351317679639 401740366958026976519459)
        ·
          refine ⟨602610550437040464779189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401740366958026976519459 602610550437040464779189)
          ·
            refine ⟨56494739103472543573049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 602610550437040464779189 56494739103472543573049)
            ·
              refine ⟨42371054327604407679787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56494739103472543573049 42371054327604407679787)
              ·
                refine ⟨63556581491406611519681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42371054327604407679787 63556581491406611519681)
                ·
                  refine ⟨47667436118554958639761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63556581491406611519681 47667436118554958639761)
                  ·
                    refine ⟨35750577088916218979821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47667436118554958639761 35750577088916218979821)
                    ·
                      refine ⟨13406466408343582117433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 35750577088916218979821 13406466408343582117433)
                      ·
                        rfl

theorem cell23_26109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_26109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26109 prefixEnd_26109 := by exact prefixLift 26109
  have htrace : WordTrace (prefixWord ++ tailWord_26109) baseStart_26109 baseEnd_26109 := by
    simpa [prefixWord, tailWord_26109, baseEnd_26109] using wordTrace_append hprefix tailTrace_26109
  have hstable : (prefixWord ++ tailWord_26109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26109).length < 2 ^ (prefixWord ++ tailWord_26109).sum := by decide
  have hdescent : baseEnd_26109 < baseStart_26109 := by decide
  rcases family_descends (prefixWord ++ tailWord_26109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26133 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_26133 : Nat := 118140960795 + 26133 * 2 ^ 59
def prefixEnd_26133 : Nat := 4983230072969 + 3 ^ 40 * 26133 * 2
def baseEnd_26133 : Nat := 4472929981350496072441

theorem tailTrace_26133 : CollatzResearch.WordTrace tailWord_26133 prefixEnd_26133 4472929981350496072441 := by
  unfold tailWord_26133
  simp only [CollatzResearch.WordTrace]
  refine ⟨953148814332079006179053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 635432542888052670786035 953148814332079006179053)
  ·
    refine ⟨357430805374529627317145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 953148814332079006179053 357430805374529627317145)
    ·
      refine ⟨268073104030897220487859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357430805374529627317145 268073104030897220487859)
      ·
        refine ⟨402109656046345830731789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268073104030897220487859 402109656046345830731789)
        ·
          refine ⟨150791121017379686524421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402109656046345830731789 150791121017379686524421)
          ·
            refine ⟨28273335190758691223329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150791121017379686524421 28273335190758691223329)
            ·
              refine ⟨21205001393069018417497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28273335190758691223329 21205001393069018417497)
              ·
                refine ⟨15903751044801763813123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21205001393069018417497 15903751044801763813123)
                ·
                  refine ⟨23855626567202645719685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15903751044801763813123 23855626567202645719685)
                  ·
                    refine ⟨4472929981350496072441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23855626567202645719685 4472929981350496072441)
                    ·
                      rfl

theorem cell23_26133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_26133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26133 prefixEnd_26133 := by exact prefixLift 26133
  have htrace : WordTrace (prefixWord ++ tailWord_26133) baseStart_26133 baseEnd_26133 := by
    simpa [prefixWord, tailWord_26133, baseEnd_26133] using wordTrace_append hprefix tailTrace_26133
  have hstable : (prefixWord ++ tailWord_26133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26133).length < 2 ^ (prefixWord ++ tailWord_26133).sum := by decide
  have hdescent : baseEnd_26133 < baseStart_26133 := by decide
  rcases family_descends (prefixWord ++ tailWord_26133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26216 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_26216 : Nat := 118140960795 + 26216 * 2 ^ 59
def prefixEnd_26216 : Nat := 4983230072969 + 3 ^ 40 * 26216 * 2
def baseEnd_26216 : Nat := 13461408838374663479441

theorem tailTrace_26216 : CollatzResearch.WordTrace tailWord_26216 prefixEnd_26216 13461408838374663479441 := by
  unfold tailWord_26216
  simp only [CollatzResearch.WordTrace]
  refine ⟨478088036515692090725251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 637450715354256120967001 478088036515692090725251)
  ·
    refine ⟨717132054773538136087877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478088036515692090725251 717132054773538136087877)
    ·
      refine ⟨134462260270038400516477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 717132054773538136087877 134462260270038400516477)
      ·
        refine ⟨50423347601264400193679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134462260270038400516477 50423347601264400193679)
        ·
          refine ⟨75635021401896600290519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50423347601264400193679 75635021401896600290519)
          ·
            refine ⟨113452532102844900435779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75635021401896600290519 113452532102844900435779)
            ·
              refine ⟨170178798154267350653669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113452532102844900435779 170178798154267350653669)
              ·
                refine ⟨31908524653925128247563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170178798154267350653669 31908524653925128247563)
                ·
                  refine ⟨47862786980887692371345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31908524653925128247563 47862786980887692371345)
                  ·
                    refine ⟨35897090235665769278509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47862786980887692371345 35897090235665769278509)
                    ·
                      refine ⟨13461408838374663479441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 35897090235665769278509 13461408838374663479441)
                      ·
                        rfl

theorem cell23_26216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_26216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26216 prefixEnd_26216 := by exact prefixLift 26216
  have htrace : WordTrace (prefixWord ++ tailWord_26216) baseStart_26216 baseEnd_26216 := by
    simpa [prefixWord, tailWord_26216, baseEnd_26216] using wordTrace_append hprefix tailTrace_26216
  have hstable : (prefixWord ++ tailWord_26216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26216).length < 2 ^ (prefixWord ++ tailWord_26216).sum := by decide
  have hdescent : baseEnd_26216 < baseStart_26216 := by decide
  rcases family_descends (prefixWord ++ tailWord_26216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26252 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_26252 : Nat := 118140960795 + 26252 * 2 ^ 59
def prefixEnd_26252 : Nat := 4983230072969 + 3 ^ 40 * 26252 * 2
def baseEnd_26252 : Nat := 13479894141936522629275

theorem tailTrace_26252 : CollatzResearch.WordTrace tailWord_26252 prefixEnd_26252 13479894141936522629275 := by
  unfold tailWord_26252
  simp only [CollatzResearch.WordTrace]
  refine ⟨478744550450481164880505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 638326067267308219840673 478744550450481164880505)
  ·
    refine ⟨359058412837860873660379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478744550450481164880505 359058412837860873660379)
    ·
      refine ⟨538587619256791310490569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359058412837860873660379 538587619256791310490569)
      ·
        refine ⟨403940714442593482867927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538587619256791310490569 403940714442593482867927)
        ·
          refine ⟨605911071663890224301891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403940714442593482867927 605911071663890224301891)
          ·
            refine ⟨908866607495835336452837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605911071663890224301891 908866607495835336452837)
            ·
              refine ⟨170412488905469125584907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 908866607495835336452837 170412488905469125584907)
              ·
                refine ⟨255618733358203688377361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170412488905469125584907 255618733358203688377361)
                ·
                  refine ⟨191714050018652766283021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255618733358203688377361 191714050018652766283021)
                  ·
                    refine ⟨71892768756994787356133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191714050018652766283021 71892768756994787356133)
                    ·
                      refine ⟨13479894141936522629275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 71892768756994787356133 13479894141936522629275)
                      ·
                        rfl

theorem cell23_26252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_26252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26252 prefixEnd_26252 := by exact prefixLift 26252
  have htrace : WordTrace (prefixWord ++ tailWord_26252) baseStart_26252 baseEnd_26252 := by
    simpa [prefixWord, tailWord_26252, baseEnd_26252] using wordTrace_append hprefix tailTrace_26252
  have hstable : (prefixWord ++ tailWord_26252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26252).length < 2 ^ (prefixWord ++ tailWord_26252).sum := by decide
  have hdescent : baseEnd_26252 < baseStart_26252 := by decide
  rcases family_descends (prefixWord ++ tailWord_26252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26263 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 2, 1, 3]
def baseStart_26263 : Nat := 118140960795 + 26263 * 2 ^ 59
def prefixEnd_26263 : Nat := 4983230072969 + 3 ^ 40 * 26263 * 2
def baseEnd_26263 : Nat := 13485542429135979591725

theorem tailTrace_26263 : CollatzResearch.WordTrace tailWord_26263 prefixEnd_26263 13485542429135979591725 := by
  unfold tailWord_26263
  simp only [CollatzResearch.WordTrace]
  refine ⟨957890303861111208411443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 638593535907407472274295 957890303861111208411443)
  ·
    refine ⟨1436835455791666812617165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 957890303861111208411443 1436835455791666812617165)
    ·
      refine ⟨538813295921875054731437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1436835455791666812617165 538813295921875054731437)
      ·
        refine ⟨202054985970703145524289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538813295921875054731437 202054985970703145524289)
        ·
          refine ⟨151541239478027359143217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202054985970703145524289 151541239478027359143217)
          ·
            refine ⟨113655929608520519357413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151541239478027359143217 113655929608520519357413)
            ·
              refine ⟨21310486801597597379515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113655929608520519357413 21310486801597597379515)
              ·
                refine ⟨31965730202396396069273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21310486801597597379515 31965730202396396069273)
                ·
                  refine ⟨23974297651797297051955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31965730202396396069273 23974297651797297051955)
                  ·
                    refine ⟨35961446477695945577933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23974297651797297051955 35961446477695945577933)
                    ·
                      refine ⟨13485542429135979591725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 35961446477695945577933 13485542429135979591725)
                      ·
                        rfl

theorem cell23_26263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_26263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26263 prefixEnd_26263 := by exact prefixLift 26263
  have htrace : WordTrace (prefixWord ++ tailWord_26263) baseStart_26263 baseEnd_26263 := by
    simpa [prefixWord, tailWord_26263, baseEnd_26263] using wordTrace_append hprefix tailTrace_26263
  have hstable : (prefixWord ++ tailWord_26263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26263).length < 2 ^ (prefixWord ++ tailWord_26263).sum := by decide
  have hdescent : baseEnd_26263 < baseStart_26263 := by decide
  rcases family_descends (prefixWord ++ tailWord_26263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26273 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_26273 : Nat := 118140960795 + 26273 * 2 ^ 59
def prefixEnd_26273 : Nat := 4983230072969 + 3 ^ 40 * 26273 * 2
def baseEnd_26273 : Nat := 13490677235680940466679

theorem tailTrace_26273 : CollatzResearch.WordTrace tailWord_26273 prefixEnd_26273 13490677235680940466679 := by
  unfold tailWord_26273
  simp only [CollatzResearch.WordTrace]
  refine ⟨958255033824882916275473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 638836689216588610850315 958255033824882916275473)
  ·
    refine ⟨718691275368662187206605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 958255033824882916275473 718691275368662187206605)
    ·
      refine ⟨269509228263248320202477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 718691275368662187206605 269509228263248320202477)
      ·
        refine ⟨101065960598718120075929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269509228263248320202477 101065960598718120075929)
        ·
          refine ⟨75799470449038590056947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101065960598718120075929 75799470449038590056947)
          ·
            refine ⟨113699205673557885085421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75799470449038590056947 113699205673557885085421)
            ·
              refine ⟨42637202127584206907033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113699205673557885085421 42637202127584206907033)
              ·
                refine ⟨31977901595688155180275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42637202127584206907033 31977901595688155180275)
                ·
                  refine ⟨47966852393532232770413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31977901595688155180275 47966852393532232770413)
                  ·
                    refine ⟨17987569647574587288905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47966852393532232770413 17987569647574587288905)
                    ·
                      refine ⟨13490677235680940466679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 17987569647574587288905 13490677235680940466679)
                      ·
                        rfl

theorem cell23_26273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_26273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26273 prefixEnd_26273 := by exact prefixLift 26273
  have htrace : WordTrace (prefixWord ++ tailWord_26273) baseStart_26273 baseEnd_26273 := by
    simpa [prefixWord, tailWord_26273, baseEnd_26273] using wordTrace_append hprefix tailTrace_26273
  have hstable : (prefixWord ++ tailWord_26273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26273).length < 2 ^ (prefixWord ++ tailWord_26273).sum := by decide
  have hdescent : baseEnd_26273 < baseStart_26273 := by decide
  rcases family_descends (prefixWord ++ tailWord_26273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26280 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_26280 : Nat := 118140960795 + 26280 * 2 ^ 59
def prefixEnd_26280 : Nat := 4983230072969 + 3 ^ 40 * 26280 * 2
def baseEnd_26280 : Nat := 13494271600262413079147

theorem tailTrace_26280 : CollatzResearch.WordTrace tailWord_26280 prefixEnd_26280 13494271600262413079147 := by
  unfold tailWord_26280
  simp only [CollatzResearch.WordTrace]
  refine ⟨479255172399761555890147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 639006896533015407853529 479255172399761555890147)
  ·
    refine ⟨718882758599642333835221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 479255172399761555890147 718882758599642333835221)
    ·
      refine ⟨16848814654679117199263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 718882758599642333835221 16848814654679117199263)
      ·
        refine ⟨25273221982018675798895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16848814654679117199263 25273221982018675798895)
        ·
          refine ⟨37909832973028013698343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25273221982018675798895 37909832973028013698343)
          ·
            refine ⟨56864749459542020547515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37909832973028013698343 56864749459542020547515)
            ·
              refine ⟨85297124189313030821273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56864749459542020547515 85297124189313030821273)
              ·
                refine ⟨63972843141984773115955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85297124189313030821273 63972843141984773115955)
                ·
                  refine ⟨95959264712977159673933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63972843141984773115955 95959264712977159673933)
                  ·
                    refine ⟨35984724267366434877725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95959264712977159673933 35984724267366434877725)
                    ·
                      refine ⟨13494271600262413079147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 35984724267366434877725 13494271600262413079147)
                      ·
                        rfl

theorem cell23_26280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_26280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26280 prefixEnd_26280 := by exact prefixLift 26280
  have htrace : WordTrace (prefixWord ++ tailWord_26280) baseStart_26280 baseEnd_26280 := by
    simpa [prefixWord, tailWord_26280, baseEnd_26280] using wordTrace_append hprefix tailTrace_26280
  have hstable : (prefixWord ++ tailWord_26280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26280).length < 2 ^ (prefixWord ++ tailWord_26280).sum := by decide
  have hdescent : baseEnd_26280 < baseStart_26280 := by decide
  rcases family_descends (prefixWord ++ tailWord_26280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26303 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 2, 2, 2]
def baseStart_26303 : Nat := 118140960795 + 26303 * 2 ^ 59
def prefixEnd_26303 : Nat := 4983230072969 + 3 ^ 40 * 26303 * 2
def baseEnd_26303 : Nat := 13506081655315823091541

theorem tailTrace_26303 : CollatzResearch.WordTrace tailWord_26303 prefixEnd_26303 13506081655315823091541 := by
  unfold tailWord_26303
  simp only [CollatzResearch.WordTrace]
  refine ⟨959349223716198039867563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 639566149144132026578375 959349223716198039867563)
  ·
    refine ⟨1439023835574297059801345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959349223716198039867563 1439023835574297059801345)
    ·
      refine ⟨1079267876680722794851009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1439023835574297059801345 1079267876680722794851009)
      ·
        refine ⟨809450907510542096138257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1079267876680722794851009 809450907510542096138257)
        ·
          refine ⟨607088180632906572103693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809450907510542096138257 607088180632906572103693)
          ·
            refine ⟨227658067737339964538885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607088180632906572103693 227658067737339964538885)
            ·
              refine ⟨42685887700751243351041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227658067737339964538885 42685887700751243351041)
              ·
                refine ⟨32014415775563432513281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42685887700751243351041 32014415775563432513281)
                ·
                  refine ⟨24010811831672574384961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32014415775563432513281 24010811831672574384961)
                  ·
                    refine ⟨18008108873754430788721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24010811831672574384961 18008108873754430788721)
                    ·
                      refine ⟨13506081655315823091541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18008108873754430788721 13506081655315823091541)
                      ·
                        rfl

theorem cell23_26303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_26303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26303 prefixEnd_26303 := by exact prefixLift 26303
  have htrace : WordTrace (prefixWord ++ tailWord_26303) baseStart_26303 baseEnd_26303 := by
    simpa [prefixWord, tailWord_26303, baseEnd_26303] using wordTrace_append hprefix tailTrace_26303
  have hstable : (prefixWord ++ tailWord_26303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26303).length < 2 ^ (prefixWord ++ tailWord_26303).sum := by decide
  have hdescent : baseEnd_26303 < baseStart_26303 := by decide
  rcases family_descends (prefixWord ++ tailWord_26303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26309 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 5]
def baseStart_26309 : Nat := 118140960795 + 26309 * 2 ^ 59
def prefixEnd_26309 : Nat := 4983230072969 + 3 ^ 40 * 26309 * 2
def baseEnd_26309 : Nat := 1501018059915866624057

theorem tailTrace_26309 : CollatzResearch.WordTrace tailWord_26309 prefixEnd_26309 1501018059915866624057 := by
  unfold tailWord_26309
  simp only [CollatzResearch.WordTrace]
  refine ⟨959568061694461064585981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 639712041129640709723987 959568061694461064585981)
  ·
    refine ⟨359838023135422899219743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 959568061694461064585981 359838023135422899219743)
    ·
      refine ⟨539757034703134348829615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359838023135422899219743 539757034703134348829615)
      ·
        refine ⟨809635552054701523244423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539757034703134348829615 809635552054701523244423)
        ·
          refine ⟨1214453328082052284866635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809635552054701523244423 1214453328082052284866635)
          ·
            refine ⟨1821679992123078427299953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214453328082052284866635 1821679992123078427299953)
            ·
              refine ⟨1366259994092308820474965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821679992123078427299953 1366259994092308820474965)
              ·
                refine ⟨16010859305769243989941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1366259994092308820474965 16010859305769243989941)
                ·
                  refine ⟨1501018059915866624057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16010859305769243989941 1501018059915866624057)
                  ·
                    rfl

theorem cell23_26309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_26309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26309 prefixEnd_26309 := by exact prefixLift 26309
  have htrace : WordTrace (prefixWord ++ tailWord_26309) baseStart_26309 baseEnd_26309 := by
    simpa [prefixWord, tailWord_26309, baseEnd_26309] using wordTrace_append hprefix tailTrace_26309
  have hstable : (prefixWord ++ tailWord_26309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26309).length < 2 ^ (prefixWord ++ tailWord_26309).sum := by decide
  have hdescent : baseEnd_26309 < baseStart_26309 := by decide
  rcases family_descends (prefixWord ++ tailWord_26309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26316 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_26316 : Nat := 118140960795 + 26316 * 2 ^ 59
def prefixEnd_26316 : Nat := 4983230072969 + 3 ^ 40 * 26316 * 2
def baseEnd_26316 : Nat := 13512756903824272228981

theorem tailTrace_26316 : CollatzResearch.WordTrace tailWord_26316 prefixEnd_26316 13512756903824272228981 := by
  unfold tailWord_26316
  simp only [CollatzResearch.WordTrace]
  refine ⟨479911686334550630045401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 639882248446067506727201 479911686334550630045401)
  ·
    refine ⟨359933764750912972534051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 479911686334550630045401 359933764750912972534051)
    ·
      refine ⟨539900647126369458801077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359933764750912972534051 539900647126369458801077)
      ·
        refine ⟨50615685668097136762601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 539900647126369458801077 50615685668097136762601)
        ·
          refine ⟨37961764251072852571951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50615685668097136762601 37961764251072852571951)
          ·
            refine ⟨56942646376609278857927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37961764251072852571951 56942646376609278857927)
            ·
              refine ⟨85413969564913918286891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56942646376609278857927 85413969564913918286891)
              ·
                refine ⟨128120954347370877430337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85413969564913918286891 128120954347370877430337)
                ·
                  refine ⟨96090715760528158072753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128120954347370877430337 96090715760528158072753)
                  ·
                    refine ⟨72068036820396118554565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96090715760528158072753 72068036820396118554565)
                    ·
                      refine ⟨13512756903824272228981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 72068036820396118554565 13512756903824272228981)
                      ·
                        rfl

theorem cell23_26316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_26316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26316 prefixEnd_26316 := by exact prefixLift 26316
  have htrace : WordTrace (prefixWord ++ tailWord_26316) baseStart_26316 baseEnd_26316 := by
    simpa [prefixWord, tailWord_26316, baseEnd_26316] using wordTrace_append hprefix tailTrace_26316
  have hstable : (prefixWord ++ tailWord_26316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26316).length < 2 ^ (prefixWord ++ tailWord_26316).sum := by decide
  have hdescent : baseEnd_26316 < baseStart_26316 := by decide
  rcases family_descends (prefixWord ++ tailWord_26316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26359 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_26359 : Nat := 118140960795 + 26359 * 2 ^ 59
def prefixEnd_26359 : Nat := 4983230072969 + 3 ^ 40 * 26359 * 2
def baseEnd_26359 : Nat := 13534836571967603991283

theorem tailTrace_26359 : CollatzResearch.WordTrace tailWord_26359 prefixEnd_26359 13534836571967603991283 := by
  unfold tailWord_26359
  simp only [CollatzResearch.WordTrace]
  refine ⟨961391711513319603906131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 640927807675546402604087 961391711513319603906131)
  ·
    refine ⟨1442087567269979405859197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961391711513319603906131 1442087567269979405859197)
    ·
      refine ⟨540782837726242277197199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1442087567269979405859197 540782837726242277197199)
      ·
        refine ⟨811174256589363415795799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540782837726242277197199 811174256589363415795799)
        ·
          refine ⟨1216761384884045123693699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811174256589363415795799 1216761384884045123693699)
          ·
            refine ⟨1825142077326067685540549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216761384884045123693699 1825142077326067685540549)
            ·
              refine ⟨342214139498637691038853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1825142077326067685540549 342214139498637691038853)
              ·
                refine ⟨64165151155994567069785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342214139498637691038853 64165151155994567069785)
                ·
                  refine ⟨48123863366995925302339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64165151155994567069785 48123863366995925302339)
                  ·
                    refine ⟨72185795050493887953509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48123863366995925302339 72185795050493887953509)
                    ·
                      refine ⟨13534836571967603991283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 72185795050493887953509 13534836571967603991283)
                      ·
                        rfl

theorem cell23_26359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_26359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26359 prefixEnd_26359 := by exact prefixLift 26359
  have htrace : WordTrace (prefixWord ++ tailWord_26359) baseStart_26359 baseEnd_26359 := by
    simpa [prefixWord, tailWord_26359, baseEnd_26359] using wordTrace_append hprefix tailTrace_26359
  have hstable : (prefixWord ++ tailWord_26359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26359).length < 2 ^ (prefixWord ++ tailWord_26359).sum := by decide
  have hdescent : baseEnd_26359 < baseStart_26359 := by decide
  rcases family_descends (prefixWord ++ tailWord_26359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26376 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_26376 : Nat := 118140960795 + 26376 * 2 ^ 59
def prefixEnd_26376 : Nat := 4983230072969 + 3 ^ 40 * 26376 * 2
def baseEnd_26376 : Nat := 13543565743094037478705

theorem tailTrace_26376 : CollatzResearch.WordTrace tailWord_26376 prefixEnd_26376 13543565743094037478705 := by
  unfold tailWord_26376
  simp only [CollatzResearch.WordTrace]
  refine ⟨481005876225865753637491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 641341168301154338183321 481005876225865753637491)
  ·
    refine ⟨721508814338798630456237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481005876225865753637491 721508814338798630456237)
    ·
      refine ⟨270565805377049486421089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 721508814338798630456237 270565805377049486421089)
      ·
        refine ⟨202924354032787114815817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270565805377049486421089 202924354032787114815817)
        ·
          refine ⟨152193265524590336111863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202924354032787114815817 152193265524590336111863)
          ·
            refine ⟨228289898286885504167795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152193265524590336111863 228289898286885504167795)
            ·
              refine ⟨342434847430328256251693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228289898286885504167795 342434847430328256251693)
              ·
                refine ⟨128413067786373096094385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342434847430328256251693 128413067786373096094385)
                ·
                  refine ⟨96309800839779822070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128413067786373096094385 96309800839779822070789)
                  ·
                    refine ⟨18058087657458716638273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96309800839779822070789 18058087657458716638273)
                    ·
                      refine ⟨13543565743094037478705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18058087657458716638273 13543565743094037478705)
                      ·
                        rfl

theorem cell23_26376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_26376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26376 prefixEnd_26376 := by exact prefixLift 26376
  have htrace : WordTrace (prefixWord ++ tailWord_26376) baseStart_26376 baseEnd_26376 := by
    simpa [prefixWord, tailWord_26376, baseEnd_26376] using wordTrace_append hprefix tailTrace_26376
  have hstable : (prefixWord ++ tailWord_26376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26376).length < 2 ^ (prefixWord ++ tailWord_26376).sum := by decide
  have hdescent : baseEnd_26376 < baseStart_26376 := by decide
  rcases family_descends (prefixWord ++ tailWord_26376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26379 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 3]
def baseStart_26379 : Nat := 118140960795 + 26379 * 2 ^ 59
def prefixEnd_26379 : Nat := 4983230072969 + 3 ^ 40 * 26379 * 2
def baseEnd_26379 : Nat := 13545106185057525741191

theorem tailTrace_26379 : CollatzResearch.WordTrace tailWord_26379 prefixEnd_26379 13545106185057525741191 := by
  unfold tailWord_26379
  simp only [CollatzResearch.WordTrace]
  refine ⟨962121171440863019634191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 641414114293908679756127 962121171440863019634191)
  ·
    refine ⟨1443181757161294529451287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962121171440863019634191 1443181757161294529451287)
    ·
      refine ⟨2164772635741941794176931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443181757161294529451287 2164772635741941794176931)
      ·
        refine ⟨3247158953612912691265397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164772635741941794176931 3247158953612912691265397)
        ·
          refine ⟨304421151901210564806131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3247158953612912691265397 304421151901210564806131)
          ·
            refine ⟨456631727851815847209197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304421151901210564806131 456631727851815847209197)
            ·
              refine ⟨171236897944430942703449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456631727851815847209197 171236897944430942703449)
              ·
                refine ⟨128427673458323207027587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171236897944430942703449 128427673458323207027587)
                ·
                  refine ⟨192641510187484810541381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128427673458323207027587 192641510187484810541381)
                  ·
                    refine ⟨36120283160153401976509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192641510187484810541381 36120283160153401976509)
                    ·
                      refine ⟨13545106185057525741191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 36120283160153401976509 13545106185057525741191)
                      ·
                        rfl

theorem cell23_26379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 3].length) (baseStart_26379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26379 prefixEnd_26379 := by exact prefixLift 26379
  have htrace : WordTrace (prefixWord ++ tailWord_26379) baseStart_26379 baseEnd_26379 := by
    simpa [prefixWord, tailWord_26379, baseEnd_26379] using wordTrace_append hprefix tailTrace_26379
  have hstable : (prefixWord ++ tailWord_26379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26379).length < 2 ^ (prefixWord ++ tailWord_26379).sum := by decide
  have hdescent : baseEnd_26379 < baseStart_26379 := by decide
  rcases family_descends (prefixWord ++ tailWord_26379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26396 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_26396 : Nat := 118140960795 + 26396 * 2 ^ 59
def prefixEnd_26396 : Nat := 4983230072969 + 3 ^ 40 * 26396 * 2
def baseEnd_26396 : Nat := 13553835356183959228613

theorem tailTrace_26396 : CollatzResearch.WordTrace tailWord_26396 prefixEnd_26396 13553835356183959228613 := by
  unfold tailWord_26396
  simp only [CollatzResearch.WordTrace]
  refine ⟨481370606189637461501521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 641827474919516615335361 481370606189637461501521)
  ·
    refine ⟨361027954642228096126141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 481370606189637461501521 361027954642228096126141)
    ·
      refine ⟨135385482990835536047303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361027954642228096126141 135385482990835536047303)
      ·
        refine ⟨203078224486253304070955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135385482990835536047303 203078224486253304070955)
        ·
          refine ⟨304617336729379956106433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203078224486253304070955 304617336729379956106433)
          ·
            refine ⟨228463002547034967079825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304617336729379956106433 228463002547034967079825)
            ·
              refine ⟨171347251910276225309869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228463002547034967079825 171347251910276225309869)
              ·
                refine ⟨64255219466353584491201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171347251910276225309869 64255219466353584491201)
                ·
                  refine ⟨48191414599765188368401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64255219466353584491201 48191414599765188368401)
                  ·
                    refine ⟨36143560949823891276301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48191414599765188368401 36143560949823891276301)
                    ·
                      refine ⟨13553835356183959228613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 36143560949823891276301 13553835356183959228613)
                      ·
                        rfl

theorem cell23_26396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_26396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26396 prefixEnd_26396 := by exact prefixLift 26396
  have htrace : WordTrace (prefixWord ++ tailWord_26396) baseStart_26396 baseEnd_26396 := by
    simpa [prefixWord, tailWord_26396, baseEnd_26396] using wordTrace_append hprefix tailTrace_26396
  have hstable : (prefixWord ++ tailWord_26396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26396).length < 2 ^ (prefixWord ++ tailWord_26396).sum := by decide
  have hdescent : baseEnd_26396 < baseStart_26396 := by decide
  rcases family_descends (prefixWord ++ tailWord_26396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26403 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 1, 4]
def baseStart_26403 : Nat := 118140960795 + 26403 * 2 ^ 59
def prefixEnd_26403 : Nat := 4983230072969 + 3 ^ 40 * 26403 * 2
def baseEnd_26403 : Nat := 4519143240255143947027

theorem tailTrace_26403 : CollatzResearch.WordTrace tailWord_26403 prefixEnd_26403 4519143240255143947027 := by
  unfold tailWord_26403
  simp only [CollatzResearch.WordTrace]
  refine ⟨962996523353915118507863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 641997682235943412338575 962996523353915118507863)
  ·
    refine ⟨1444494785030872677761795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962996523353915118507863 1444494785030872677761795)
    ·
      refine ⟨2166742177546309016642693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444494785030872677761795 2166742177546309016642693)
      ·
        refine ⟨406264158289932940620505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2166742177546309016642693 406264158289932940620505)
        ·
          refine ⟨304698118717449705465379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406264158289932940620505 304698118717449705465379)
          ·
            refine ⟨457047178076174558198069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304698118717449705465379 457047178076174558198069)
            ·
              refine ⟨42848172944641364831069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457047178076174558198069 42848172944641364831069)
              ·
                refine ⟨16068064854240511811651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42848172944641364831069 16068064854240511811651)
                ·
                  refine ⟨24102097281360767717477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16068064854240511811651 24102097281360767717477)
                  ·
                    refine ⟨4519143240255143947027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24102097281360767717477 4519143240255143947027)
                    ·
                      rfl

theorem cell23_26403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 4].length) (baseStart_26403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26403 prefixEnd_26403 := by exact prefixLift 26403
  have htrace : WordTrace (prefixWord ++ tailWord_26403) baseStart_26403 baseEnd_26403 := by
    simpa [prefixWord, tailWord_26403, baseEnd_26403] using wordTrace_append hprefix tailTrace_26403
  have hstable : (prefixWord ++ tailWord_26403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26403).length < 2 ^ (prefixWord ++ tailWord_26403).sum := by decide
  have hdescent : baseEnd_26403 < baseStart_26403 := by decide
  rcases family_descends (prefixWord ++ tailWord_26403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26420 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_26420 : Nat := 118140960795 + 26420 * 2 ^ 59
def prefixEnd_26420 : Nat := 4983230072969 + 3 ^ 40 * 26420 * 2
def baseEnd_26420 : Nat := 4522052963963955109501

theorem tailTrace_26420 : CollatzResearch.WordTrace tailWord_26420 prefixEnd_26420 4522052963963955109501 := by
  unfold tailWord_26420
  simp only [CollatzResearch.WordTrace]
  refine ⟨481808282146163510938357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 642411042861551347917809 481808282146163510938357)
  ·
    refine ⟨45169526451202829150471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 481808282146163510938357 45169526451202829150471)
    ·
      refine ⟨67754289676804243725707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45169526451202829150471 67754289676804243725707)
      ·
        refine ⟨101631434515206365588561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67754289676804243725707 101631434515206365588561)
        ·
          refine ⟨76223575886404774191421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101631434515206365588561 76223575886404774191421)
          ·
            refine ⟨28583840957401790321783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76223575886404774191421 28583840957401790321783)
            ·
              refine ⟨42875761436102685482675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28583840957401790321783 42875761436102685482675)
              ·
                refine ⟨64313642154154028224013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42875761436102685482675 64313642154154028224013)
                ·
                  refine ⟨24117615807807760584005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64313642154154028224013 24117615807807760584005)
                  ·
                    refine ⟨4522052963963955109501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24117615807807760584005 4522052963963955109501)
                    ·
                      rfl

theorem cell23_26420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_26420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26420 prefixEnd_26420 := by exact prefixLift 26420
  have htrace : WordTrace (prefixWord ++ tailWord_26420) baseStart_26420 baseEnd_26420 := by
    simpa [prefixWord, tailWord_26420, baseEnd_26420] using wordTrace_append hprefix tailTrace_26420
  have hstable : (prefixWord ++ tailWord_26420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26420).length < 2 ^ (prefixWord ++ tailWord_26420).sum := by decide
  have hdescent : baseEnd_26420 < baseStart_26420 := by decide
  rcases family_descends (prefixWord ++ tailWord_26420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26453 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_26453 : Nat := 118140960795 + 26453 * 2 ^ 59
def prefixEnd_26453 : Nat := 4983230072969 + 3 ^ 40 * 26453 * 2
def baseEnd_26453 : Nat := 13583103753490236215851

theorem tailTrace_26453 : CollatzResearch.WordTrace tailWord_26453 prefixEnd_26453 13583103753490236215851 := by
  unfold tailWord_26453
  simp only [CollatzResearch.WordTrace]
  refine ⟨964820173172773657828013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 643213448781849105218675 964820173172773657828013)
  ·
    refine ⟨361807564939790121685505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 964820173172773657828013 361807564939790121685505)
    ·
      refine ⟨271355673704842591264129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361807564939790121685505 271355673704842591264129)
      ·
        refine ⟨203516755278631943448097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271355673704842591264129 203516755278631943448097)
        ·
          refine ⟨152637566458973957586073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203516755278631943448097 152637566458973957586073)
          ·
            refine ⟨114478174844230468189555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152637566458973957586073 114478174844230468189555)
            ·
              refine ⟨171717262266345702284333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114478174844230468189555 171717262266345702284333)
              ·
                refine ⟨64393973349879638356625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171717262266345702284333 64393973349879638356625)
                ·
                  refine ⟨48295480012409728767469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64393973349879638356625 48295480012409728767469)
                  ·
                    refine ⟨18110805004653648287801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48295480012409728767469 18110805004653648287801)
                    ·
                      refine ⟨13583103753490236215851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18110805004653648287801 13583103753490236215851)
                      ·
                        rfl

theorem cell23_26453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_26453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26453 prefixEnd_26453 := by exact prefixLift 26453
  have htrace : WordTrace (prefixWord ++ tailWord_26453) baseStart_26453 baseEnd_26453 := by
    simpa [prefixWord, tailWord_26453, baseEnd_26453] using wordTrace_append hprefix tailTrace_26453
  have hstable : (prefixWord ++ tailWord_26453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26453).length < 2 ^ (prefixWord ++ tailWord_26453).sum := by decide
  have hdescent : baseEnd_26453 < baseStart_26453 := by decide
  rcases family_descends (prefixWord ++ tailWord_26453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26463 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 1, 5]
def baseStart_26463 : Nat := 118140960795 + 26463 * 2 ^ 59
def prefixEnd_26463 : Nat := 4983230072969 + 3 ^ 40 * 26463 * 2
def baseEnd_26463 : Nat := 4529412853345065696935

theorem tailTrace_26463 : CollatzResearch.WordTrace tailWord_26463 prefixEnd_26463 4529412853345065696935 := by
  unfold tailWord_26463
  simp only [CollatzResearch.WordTrace]
  refine ⟨965184903136545365692043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 643456602091030243794695 965184903136545365692043)
  ·
    refine ⟨1447777354704818048538065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 965184903136545365692043 1447777354704818048538065)
    ·
      refine ⟨1085833016028613536403549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1447777354704818048538065 1085833016028613536403549)
      ·
        refine ⟨407187381010730076151331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1085833016028613536403549 407187381010730076151331)
        ·
          refine ⟨610781071516095114226997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407187381010730076151331 610781071516095114226997)
          ·
            refine ⟨57260725454633916958781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 610781071516095114226997 57260725454633916958781)
            ·
              refine ⟨21472772045487718859543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57260725454633916958781 21472772045487718859543)
              ·
                refine ⟨32209158068231578289315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21472772045487718859543 32209158068231578289315)
                ·
                  refine ⟨48313737102347367433973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32209158068231578289315 48313737102347367433973)
                  ·
                    refine ⟨4529412853345065696935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48313737102347367433973 4529412853345065696935)
                    ·
                      rfl

theorem cell23_26463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 5].length) (baseStart_26463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26463 prefixEnd_26463 := by exact prefixLift 26463
  have htrace : WordTrace (prefixWord ++ tailWord_26463) baseStart_26463 baseEnd_26463 := by
    simpa [prefixWord, tailWord_26463, baseEnd_26463] using wordTrace_append hprefix tailTrace_26463
  have hstable : (prefixWord ++ tailWord_26463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26463).length < 2 ^ (prefixWord ++ tailWord_26463).sum := by decide
  have hdescent : baseEnd_26463 < baseStart_26463 := by decide
  rcases family_descends (prefixWord ++ tailWord_26463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26477 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_26477 : Nat := 118140960795 + 26477 * 2 ^ 59
def prefixEnd_26477 : Nat := 4983230072969 + 3 ^ 40 * 26477 * 2
def baseEnd_26477 : Nat := 13595427289198142315741

theorem tailTrace_26477 : CollatzResearch.WordTrace tailWord_26477 prefixEnd_26477 13595427289198142315741 := by
  unfold tailWord_26477
  simp only [CollatzResearch.WordTrace]
  refine ⟨965695525085825756701685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 643797016723883837801123 965695525085825756701685)
  ·
    refine ⟨90533955476796164690783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 965695525085825756701685 90533955476796164690783)
    ·
      refine ⟨135800933215194247036175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90533955476796164690783 135800933215194247036175)
      ·
        refine ⟨203701399822791370554263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135800933215194247036175 203701399822791370554263)
        ·
          refine ⟨305552099734187055831395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203701399822791370554263 305552099734187055831395)
          ·
            refine ⟨458328149601280583747093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305552099734187055831395 458328149601280583747093)
            ·
              refine ⟨21484132012560027363145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 458328149601280583747093 21484132012560027363145)
              ·
                refine ⟨16113099009420020522359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21484132012560027363145 16113099009420020522359)
                ·
                  refine ⟨24169648514130030783539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16113099009420020522359 24169648514130030783539)
                  ·
                    refine ⟨36254472771195046175309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24169648514130030783539 36254472771195046175309)
                    ·
                      refine ⟨13595427289198142315741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 36254472771195046175309 13595427289198142315741)
                      ·
                        rfl

theorem cell23_26477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_26477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26477 prefixEnd_26477 := by exact prefixLift 26477
  have htrace : WordTrace (prefixWord ++ tailWord_26477) baseStart_26477 baseEnd_26477 := by
    simpa [prefixWord, tailWord_26477, baseEnd_26477] using wordTrace_append hprefix tailTrace_26477
  have hstable : (prefixWord ++ tailWord_26477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26477).length < 2 ^ (prefixWord ++ tailWord_26477).sum := by decide
  have hdescent : baseEnd_26477 < baseStart_26477 := by decide
  rcases family_descends (prefixWord ++ tailWord_26477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26483 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 3, 2, 2]
def baseStart_26483 : Nat := 118140960795 + 26483 * 2 ^ 59
def prefixEnd_26483 : Nat := 4983230072969 + 3 ^ 40 * 26483 * 2
def baseEnd_26483 : Nat := 13598508173125118840713

theorem tailTrace_26483 : CollatzResearch.WordTrace tailWord_26483 prefixEnd_26483 13598508173125118840713 := by
  unfold tailWord_26483
  simp only [CollatzResearch.WordTrace]
  refine ⟨965914363064088781420103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 643942908709392520946735 965914363064088781420103)
  ·
    refine ⟨1448871544596133172130155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 965914363064088781420103 1448871544596133172130155)
    ·
      refine ⟨2173307316894199758195233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448871544596133172130155 2173307316894199758195233)
      ·
        refine ⟨1629980487670649818646425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2173307316894199758195233 1629980487670649818646425)
        ·
          refine ⟨1222485365752987363984819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629980487670649818646425 1222485365752987363984819)
          ·
            refine ⟨1833728048629481045977229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222485365752987363984819 1833728048629481045977229)
            ·
              refine ⟨687648018236055392241461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1833728048629481045977229 687648018236055392241461)
              ·
                refine ⟨64467001709630193022637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 687648018236055392241461 64467001709630193022637)
                ·
                  refine ⟨24175125641111322383489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64467001709630193022637 24175125641111322383489)
                  ·
                    refine ⟨18131344230833491787617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24175125641111322383489 18131344230833491787617)
                    ·
                      refine ⟨13598508173125118840713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18131344230833491787617 13598508173125118840713)
                      ·
                        rfl

theorem cell23_26483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 2, 2].length) (baseStart_26483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26483 prefixEnd_26483 := by exact prefixLift 26483
  have htrace : WordTrace (prefixWord ++ tailWord_26483) baseStart_26483 baseEnd_26483 := by
    simpa [prefixWord, tailWord_26483, baseEnd_26483] using wordTrace_append hprefix tailTrace_26483
  have hstable : (prefixWord ++ tailWord_26483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26483).length < 2 ^ (prefixWord ++ tailWord_26483).sum := by decide
  have hdescent : baseEnd_26483 < baseStart_26483 := by decide
  rcases family_descends (prefixWord ++ tailWord_26483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26496 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_26496 : Nat := 118140960795 + 26496 * 2 ^ 59
def prefixEnd_26496 : Nat := 4983230072969 + 3 ^ 40 * 26496 * 2
def baseEnd_26496 : Nat := 13605183421633567978153

theorem tailTrace_26496 : CollatzResearch.WordTrace tailWord_26496 prefixEnd_26496 13605183421633567978153 := by
  unfold tailWord_26496
  simp only [CollatzResearch.WordTrace]
  refine ⟨483194256008496000821671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 644259008011328001095561 483194256008496000821671)
  ·
    refine ⟨724791384012744001232507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 483194256008496000821671 724791384012744001232507)
    ·
      refine ⟨1087187076019116001848761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724791384012744001232507 1087187076019116001848761)
      ·
        refine ⟨815390307014337001386571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1087187076019116001848761 815390307014337001386571)
        ·
          refine ⟨1223085460521505502079857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815390307014337001386571 1223085460521505502079857)
          ·
            refine ⟨917314095391129126559893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223085460521505502079857 917314095391129126559893)
            ·
              refine ⟨42999098221459177807495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 917314095391129126559893 42999098221459177807495)
              ·
                refine ⟨64498647332188766711243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42999098221459177807495 64498647332188766711243)
                ·
                  refine ⟨96747970998283150066865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64498647332188766711243 96747970998283150066865)
                  ·
                    refine ⟨72560978248712362550149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96747970998283150066865 72560978248712362550149)
                    ·
                      refine ⟨13605183421633567978153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 72560978248712362550149 13605183421633567978153)
                      ·
                        rfl

theorem cell23_26496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_26496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26496 prefixEnd_26496 := by exact prefixLift 26496
  have htrace : WordTrace (prefixWord ++ tailWord_26496) baseStart_26496 baseEnd_26496 := by
    simpa [prefixWord, tailWord_26496, baseEnd_26496] using wordTrace_append hprefix tailTrace_26496
  have hstable : (prefixWord ++ tailWord_26496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26496).length < 2 ^ (prefixWord ++ tailWord_26496).sum := by decide
  have hdescent : baseEnd_26496 < baseStart_26496 := by decide
  rcases family_descends (prefixWord ++ tailWord_26496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26517 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_26517 : Nat := 118140960795 + 26517 * 2 ^ 59
def prefixEnd_26517 : Nat := 4983230072969 + 3 ^ 40 * 26517 * 2
def baseEnd_26517 : Nat := 13615966515377985815557

theorem tailTrace_26517 : CollatzResearch.WordTrace tailWord_26517 prefixEnd_26517 13615966515377985815557 := by
  unfold tailWord_26517
  simp only [CollatzResearch.WordTrace]
  refine ⟨967154444940912588157805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 644769629960608392105203 967154444940912588157805)
  ·
    refine ⟨362682916852842220559177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 967154444940912588157805 362682916852842220559177)
    ·
      refine ⟨272012187639631665419383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362682916852842220559177 272012187639631665419383)
      ·
        refine ⟨408018281459447498129075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272012187639631665419383 408018281459447498129075)
        ·
          refine ⟨612027422189171247193613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408018281459447498129075 612027422189171247193613)
          ·
            refine ⟨229510283320939217697605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612027422189171247193613 229510283320939217697605)
            ·
              refine ⟨43033178122676103318301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229510283320939217697605 43033178122676103318301)
              ·
                refine ⟨16137441796003538744363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43033178122676103318301 16137441796003538744363)
                ·
                  refine ⟨24206162694005308116545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16137441796003538744363 24206162694005308116545)
                  ·
                    refine ⟨18154622020503981087409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24206162694005308116545 18154622020503981087409)
                    ·
                      refine ⟨13615966515377985815557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18154622020503981087409 13615966515377985815557)
                      ·
                        rfl

theorem cell23_26517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_26517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26517 prefixEnd_26517 := by exact prefixLift 26517
  have htrace : WordTrace (prefixWord ++ tailWord_26517) baseStart_26517 baseEnd_26517 := by
    simpa [prefixWord, tailWord_26517, baseEnd_26517] using wordTrace_append hprefix tailTrace_26517
  have hstable : (prefixWord ++ tailWord_26517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26517).length < 2 ^ (prefixWord ++ tailWord_26517).sum := by decide
  have hdescent : baseEnd_26517 < baseStart_26517 := by decide
  rcases family_descends (prefixWord ++ tailWord_26517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26527 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 2, 4]
def baseStart_26527 : Nat := 118140960795 + 26527 * 2 ^ 59
def prefixEnd_26527 : Nat := 4983230072969 + 3 ^ 40 * 26527 * 2
def baseEnd_26527 : Nat := 4540367107307648896837

theorem tailTrace_26527 : CollatzResearch.WordTrace tailWord_26527 prefixEnd_26527 4540367107307648896837 := by
  unfold tailWord_26527
  simp only [CollatzResearch.WordTrace]
  refine ⟨967519174904684296021835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 645012783269789530681223 967519174904684296021835)
  ·
    refine ⟨1451278762357026444032753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967519174904684296021835 1451278762357026444032753)
    ·
      refine ⟨1088459071767769833024565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1451278762357026444032753 1088459071767769833024565)
      ·
        refine ⟨102043037978228421846053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1088459071767769833024565 102043037978228421846053)
        ·
          refine ⟨19133069620917829096135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102043037978228421846053 19133069620917829096135)
          ·
            refine ⟨28699604431376743644203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19133069620917829096135 28699604431376743644203)
            ·
              refine ⟨43049406647065115466305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28699604431376743644203 43049406647065115466305)
              ·
                refine ⟨32287054985298836599729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43049406647065115466305 32287054985298836599729)
                ·
                  refine ⟨24215291238974127449797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32287054985298836599729 24215291238974127449797)
                  ·
                    refine ⟨4540367107307648896837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24215291238974127449797 4540367107307648896837)
                    ·
                      rfl

theorem cell23_26527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 4].length) (baseStart_26527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26527 prefixEnd_26527 := by exact prefixLift 26527
  have htrace : WordTrace (prefixWord ++ tailWord_26527) baseStart_26527 baseEnd_26527 := by
    simpa [prefixWord, tailWord_26527, baseEnd_26527] using wordTrace_append hprefix tailTrace_26527
  have hstable : (prefixWord ++ tailWord_26527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26527).length < 2 ^ (prefixWord ++ tailWord_26527).sum := by decide
  have hdescent : baseEnd_26527 < baseStart_26527 := by decide
  rcases family_descends (prefixWord ++ tailWord_26527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26560 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 1, 3, 2]
def baseStart_26560 : Nat := 118140960795 + 26560 * 2 ^ 59
def prefixEnd_26560 : Nat := 4983230072969 + 3 ^ 40 * 26560 * 2
def baseEnd_26560 : Nat := 13638046183521317577859

theorem tailTrace_26560 : CollatzResearch.WordTrace tailWord_26560 prefixEnd_26560 13638046183521317577859 := by
  unfold tailWord_26560
  simp only [CollatzResearch.WordTrace]
  refine ⟨484361391892565465986567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 645815189190087287982089 484361391892565465986567)
  ·
    refine ⟨726542087838848198979851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484361391892565465986567 726542087838848198979851)
    ·
      refine ⟨1089813131758272298469777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726542087838848198979851 1089813131758272298469777)
      ·
        refine ⟨817359848818704223852333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089813131758272298469777 817359848818704223852333)
        ·
          refine ⟨306509943307014083944625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 817359848818704223852333 306509943307014083944625)
          ·
            refine ⟨229882457480260562958469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306509943307014083944625 229882457480260562958469)
            ·
              refine ⟨43102960777548855554713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229882457480260562958469 43102960777548855554713)
              ·
                refine ⟨32327220583161641666035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43102960777548855554713 32327220583161641666035)
                ·
                  refine ⟨48490830874742462499053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32327220583161641666035 48490830874742462499053)
                  ·
                    refine ⟨18184061578028423437145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48490830874742462499053 18184061578028423437145)
                    ·
                      refine ⟨13638046183521317577859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18184061578028423437145 13638046183521317577859)
                      ·
                        rfl

theorem cell23_26560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_26560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26560 prefixEnd_26560 := by exact prefixLift 26560
  have htrace : WordTrace (prefixWord ++ tailWord_26560) baseStart_26560 baseEnd_26560 := by
    simpa [prefixWord, tailWord_26560, baseEnd_26560] using wordTrace_append hprefix tailTrace_26560
  have hstable : (prefixWord ++ tailWord_26560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26560).length < 2 ^ (prefixWord ++ tailWord_26560).sum := by decide
  have hdescent : baseEnd_26560 < baseStart_26560 := by decide
  rcases family_descends (prefixWord ++ tailWord_26560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26636 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_26636 : Nat := 118140960795 + 26636 * 2 ^ 59
def prefixEnd_26636 : Nat := 4983230072969 + 3 ^ 40 * 26636 * 2
def baseEnd_26636 : Nat := 13677070713263020227509

theorem tailTrace_26636 : CollatzResearch.WordTrace tailWord_26636 prefixEnd_26636 13677070713263020227509 := by
  unfold tailWord_26636
  simp only [CollatzResearch.WordTrace]
  refine ⟨485747365754897955869881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 647663154339863941159841 485747365754897955869881)
  ·
    refine ⟨364310524316173466902411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 485747365754897955869881 364310524316173466902411)
    ·
      refine ⟨546465786474260200353617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364310524316173466902411 546465786474260200353617)
      ·
        refine ⟨409849339855695150265213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546465786474260200353617 409849339855695150265213)
        ·
          refine ⟨153693502445885681349455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409849339855695150265213 153693502445885681349455)
          ·
            refine ⟨230540253668828522024183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153693502445885681349455 230540253668828522024183)
            ·
              refine ⟨345810380503242783036275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230540253668828522024183 345810380503242783036275)
              ·
                refine ⟨518715570754864174554413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345810380503242783036275 518715570754864174554413)
                ·
                  refine ⟨194518339033074065457905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518715570754864174554413 194518339033074065457905)
                  ·
                    refine ⟨145888754274805549093429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194518339033074065457905 145888754274805549093429)
                    ·
                      refine ⟨13677070713263020227509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 145888754274805549093429 13677070713263020227509)
                      ·
                        rfl

theorem cell23_26636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_26636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26636 prefixEnd_26636 := by exact prefixLift 26636
  have htrace : WordTrace (prefixWord ++ tailWord_26636) baseStart_26636 baseEnd_26636 := by
    simpa [prefixWord, tailWord_26636, baseEnd_26636] using wordTrace_append hprefix tailTrace_26636
  have hstable : (prefixWord ++ tailWord_26636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26636).length < 2 ^ (prefixWord ++ tailWord_26636).sum := by decide
  have hdescent : baseEnd_26636 < baseStart_26636 := by decide
  rcases family_descends (prefixWord ++ tailWord_26636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26653 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_26653 : Nat := 118140960795 + 26653 * 2 ^ 59
def prefixEnd_26653 : Nat := 4983230072969 + 3 ^ 40 * 26653 * 2
def baseEnd_26653 : Nat := 13685799884389453714931

theorem tailTrace_26653 : CollatzResearch.WordTrace tailWord_26653 prefixEnd_26653 13685799884389453714931 := by
  unfold tailWord_26653
  simp only [CollatzResearch.WordTrace]
  refine ⟨972114772448207815108613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 648076514965471876739075 972114772448207815108613)
  ·
    refine ⟨182271519834038965332865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 972114772448207815108613 182271519834038965332865)
    ·
      refine ⟨136703639875529223999649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182271519834038965332865 136703639875529223999649)
      ·
        refine ⟨102527729906646917999737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136703639875529223999649 102527729906646917999737)
        ·
          refine ⟨76895797429985188499803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102527729906646917999737 76895797429985188499803)
          ·
            refine ⟨115343696144977782749705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76895797429985188499803 115343696144977782749705)
            ·
              refine ⟨86507772108733337062279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115343696144977782749705 86507772108733337062279)
              ·
                refine ⟨129761658163100005593419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86507772108733337062279 129761658163100005593419)
                ·
                  refine ⟨194642487244650008390129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129761658163100005593419 194642487244650008390129)
                  ·
                    refine ⟨145981865433487506292597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194642487244650008390129 145981865433487506292597)
                    ·
                      refine ⟨13685799884389453714931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 145981865433487506292597 13685799884389453714931)
                      ·
                        rfl

theorem cell23_26653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_26653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26653 prefixEnd_26653 := by exact prefixLift 26653
  have htrace : WordTrace (prefixWord ++ tailWord_26653) baseStart_26653 baseEnd_26653 := by
    simpa [prefixWord, tailWord_26653, baseEnd_26653] using wordTrace_append hprefix tailTrace_26653
  have hstable : (prefixWord ++ tailWord_26653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26653).length < 2 ^ (prefixWord ++ tailWord_26653).sum := by decide
  have hdescent : baseEnd_26653 < baseStart_26653 := by decide
  rcases family_descends (prefixWord ++ tailWord_26653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26673 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 5, 4]
def baseStart_26673 : Nat := 118140960795 + 26673 * 2 ^ 59
def prefixEnd_26673 : Nat := 4983230072969 + 3 ^ 40 * 26673 * 2
def baseEnd_26673 : Nat := 4565356499159791821613

theorem tailTrace_26673 : CollatzResearch.WordTrace tailWord_26673 prefixEnd_26673 4565356499159791821613 := by
  unfold tailWord_26673
  simp only [CollatzResearch.WordTrace]
  refine ⟨972844232375751230836673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 648562821583834153891115 972844232375751230836673)
  ·
    refine ⟨729633174281813423127505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 972844232375751230836673 729633174281813423127505)
    ·
      refine ⟨547224880711360067345629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 729633174281813423127505 547224880711360067345629)
      ·
        refine ⟨205209330266760025254611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547224880711360067345629 205209330266760025254611)
        ·
          refine ⟨307813995400140037881917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205209330266760025254611 307813995400140037881917)
          ·
            refine ⟨115430248275052514205719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307813995400140037881917 115430248275052514205719)
            ·
              refine ⟨173145372412578771308579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115430248275052514205719 173145372412578771308579)
              ·
                refine ⟨259718058618868156962869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173145372412578771308579 259718058618868156962869)
                ·
                  refine ⟨24348567995518889715269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259718058618868156962869 24348567995518889715269)
                  ·
                    refine ⟨4565356499159791821613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24348567995518889715269 4565356499159791821613)
                    ·
                      rfl

theorem cell23_26673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_26673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26673 prefixEnd_26673 := by exact prefixLift 26673
  have htrace : WordTrace (prefixWord ++ tailWord_26673) baseStart_26673 baseEnd_26673 := by
    simpa [prefixWord, tailWord_26673, baseEnd_26673] using wordTrace_append hprefix tailTrace_26673
  have hstable : (prefixWord ++ tailWord_26673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26673).length < 2 ^ (prefixWord ++ tailWord_26673).sum := by decide
  have hdescent : baseEnd_26673 < baseStart_26673 := by decide
  rcases family_descends (prefixWord ++ tailWord_26673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26720 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 6]
def baseStart_26720 : Nat := 118140960795 + 26720 * 2 ^ 59
def prefixEnd_26720 : Nat := 4983230072969 + 3 ^ 40 * 26720 * 2
def baseEnd_26720 : Nat := 1524467009804521286347

theorem tailTrace_26720 : CollatzResearch.WordTrace tailWord_26720 prefixEnd_26720 1524467009804521286347 := by
  unfold tailWord_26720
  simp only [CollatzResearch.WordTrace]
  refine ⟨487279231602739128898807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 649705642136985505198409 487279231602739128898807)
  ·
    refine ⟨730918847404108693348211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487279231602739128898807 730918847404108693348211)
    ·
      refine ⟨1096378271106163040022317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730918847404108693348211 1096378271106163040022317)
      ·
        refine ⟨411141851664811140008369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1096378271106163040022317 411141851664811140008369)
        ·
          refine ⟨308356388748608355006277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411141851664811140008369 308356388748608355006277)
          ·
            refine ⟨57816822890364066563677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308356388748608355006277 57816822890364066563677)
            ·
              refine ⟨21681308583886524961379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57816822890364066563677 21681308583886524961379)
              ·
                refine ⟨32521962875829787442069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21681308583886524961379 32521962875829787442069)
                ·
                  refine ⟨1524467009804521286347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32521962875829787442069 1524467009804521286347)
                  ·
                    rfl

theorem cell23_26720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 6].length) (baseStart_26720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26720 prefixEnd_26720 := by exact prefixLift 26720
  have htrace : WordTrace (prefixWord ++ tailWord_26720) baseStart_26720 baseEnd_26720 := by
    simpa [prefixWord, tailWord_26720, baseEnd_26720] using wordTrace_append hprefix tailTrace_26720
  have hstable : (prefixWord ++ tailWord_26720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26720).length < 2 ^ (prefixWord ++ tailWord_26720).sum := by decide
  have hdescent : baseEnd_26720 < baseStart_26720 := by decide
  rcases family_descends (prefixWord ++ tailWord_26720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26757 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 2, 3, 2]
def baseStart_26757 : Nat := 118140960795 + 26757 * 2 ^ 59
def prefixEnd_26757 : Nat := 4983230072969 + 3 ^ 40 * 26757 * 2
def baseEnd_26757 : Nat := 13739201872457046814453

theorem tailTrace_26757 : CollatzResearch.WordTrace tailWord_26757 prefixEnd_26757 13739201872457046814453 := by
  unfold tailWord_26757
  simp only [CollatzResearch.WordTrace]
  refine ⟨975907964071433576894525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 650605309380955717929683 975907964071433576894525)
  ·
    refine ⟨365965486526787591335447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 975907964071433576894525 365965486526787591335447)
    ·
      refine ⟨548948229790181387003171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365965486526787591335447 548948229790181387003171)
      ·
        refine ⟨823422344685272080504757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548948229790181387003171 823422344685272080504757)
        ·
          refine ⟨77195844814244257547321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 823422344685272080504757 77195844814244257547321)
          ·
            refine ⟨57896883610683193160491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77195844814244257547321 57896883610683193160491)
            ·
              refine ⟨86845325416024789740737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57896883610683193160491 86845325416024789740737)
              ·
                refine ⟨65133994062018592305553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86845325416024789740737 65133994062018592305553)
                ·
                  refine ⟨48850495546513944229165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65133994062018592305553 48850495546513944229165)
                  ·
                    refine ⟨18318935829942729085937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48850495546513944229165 18318935829942729085937)
                    ·
                      refine ⟨13739201872457046814453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18318935829942729085937 13739201872457046814453)
                      ·
                        rfl

theorem cell23_26757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_26757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26757 prefixEnd_26757 := by exact prefixLift 26757
  have htrace : WordTrace (prefixWord ++ tailWord_26757) baseStart_26757 baseEnd_26757 := by
    simpa [prefixWord, tailWord_26757, baseEnd_26757] using wordTrace_append hprefix tailTrace_26757
  have hstable : (prefixWord ++ tailWord_26757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26757).length < 2 ^ (prefixWord ++ tailWord_26757).sum := by decide
  have hdescent : baseEnd_26757 < baseStart_26757 := by decide
  rcases family_descends (prefixWord ++ tailWord_26757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26770 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_26770 : Nat := 118140960795 + 26770 * 2 ^ 59
def prefixEnd_26770 : Nat := 4983230072969 + 3 ^ 40 * 26770 * 2
def baseEnd_26770 : Nat := 13745877120965495951893

theorem tailTrace_26770 : CollatzResearch.WordTrace tailWord_26770 prefixEnd_26770 13745877120965495951893 := by
  unfold tailWord_26770
  simp only [CollatzResearch.WordTrace]
  refine ⟨244095528256084199279441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 650921408682891198078509 244095528256084199279441)
  ·
    refine ⟨183071646192063149459581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244095528256084199279441 183071646192063149459581)
    ·
      refine ⟨68651867322023681047343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183071646192063149459581 68651867322023681047343)
      ·
        refine ⟨102977800983035521571015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68651867322023681047343 102977800983035521571015)
        ·
          refine ⟨154466701474553282356523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102977800983035521571015 154466701474553282356523)
          ·
            refine ⟨231700052211829923534785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154466701474553282356523 231700052211829923534785)
            ·
              refine ⟨173775039158872442651089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231700052211829923534785 173775039158872442651089)
              ·
                refine ⟨130331279369154331988317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173775039158872442651089 130331279369154331988317)
                ·
                  refine ⟨48874229763432874495619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130331279369154331988317 48874229763432874495619)
                  ·
                    refine ⟨73311344645149311743429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48874229763432874495619 73311344645149311743429)
                    ·
                      refine ⟨13745877120965495951893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 73311344645149311743429 13745877120965495951893)
                      ·
                        rfl

theorem cell23_26770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_26770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26770 prefixEnd_26770 := by exact prefixLift 26770
  have htrace : WordTrace (prefixWord ++ tailWord_26770) baseStart_26770 baseEnd_26770 := by
    simpa [prefixWord, tailWord_26770, baseEnd_26770] using wordTrace_append hprefix tailTrace_26770
  have hstable : (prefixWord ++ tailWord_26770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26770).length < 2 ^ (prefixWord ++ tailWord_26770).sum := by decide
  have hdescent : baseEnd_26770 < baseStart_26770 := by decide
  rcases family_descends (prefixWord ++ tailWord_26770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26773 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_26773 : Nat := 118140960795 + 26773 * 2 ^ 59
def prefixEnd_26773 : Nat := 4983230072969 + 3 ^ 40 * 26773 * 2
def baseEnd_26773 : Nat := 13747417562928984214379

theorem tailTrace_26773 : CollatzResearch.WordTrace tailWord_26773 prefixEnd_26773 13747417562928984214379 := by
  unfold tailWord_26773
  simp only [CollatzResearch.WordTrace]
  refine ⟨976491532013468309476973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 650994354675645539651315 976491532013468309476973)
  ·
    refine ⟨366184324505050616053865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 976491532013468309476973 366184324505050616053865)
    ·
      refine ⟨274638243378787962040399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366184324505050616053865 274638243378787962040399)
      ·
        refine ⟨411957365068181943060599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274638243378787962040399 411957365068181943060599)
        ·
          refine ⟨617936047602272914590899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411957365068181943060599 617936047602272914590899)
          ·
            refine ⟨926904071403409371886349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617936047602272914590899 926904071403409371886349)
            ·
              refine ⟨347589026776278514457381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926904071403409371886349 347589026776278514457381)
              ·
                refine ⟨65172942520552221460759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347589026776278514457381 65172942520552221460759)
                ·
                  refine ⟨97759413780828332191139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65172942520552221460759 97759413780828332191139)
                  ·
                    refine ⟨146639120671242498286709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97759413780828332191139 146639120671242498286709)
                    ·
                      refine ⟨13747417562928984214379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 146639120671242498286709 13747417562928984214379)
                      ·
                        rfl

theorem cell23_26773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_26773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26773 prefixEnd_26773 := by exact prefixLift 26773
  have htrace : WordTrace (prefixWord ++ tailWord_26773) baseStart_26773 baseEnd_26773 := by
    simpa [prefixWord, tailWord_26773, baseEnd_26773] using wordTrace_append hprefix tailTrace_26773
  have hstable : (prefixWord ++ tailWord_26773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26773).length < 2 ^ (prefixWord ++ tailWord_26773).sum := by decide
  have hdescent : baseEnd_26773 < baseStart_26773 := by decide
  rcases family_descends (prefixWord ++ tailWord_26773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26814 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_26814 : Nat := 118140960795 + 26814 * 2 ^ 59
def prefixEnd_26814 : Nat := 4983230072969 + 3 ^ 40 * 26814 * 2
def baseEnd_26814 : Nat := 4589490089921107933897

theorem tailTrace_26814 : CollatzResearch.WordTrace tailWord_26814 prefixEnd_26814 4589490089921107933897 := by
  unfold tailWord_26814
  simp only [CollatzResearch.WordTrace]
  refine ⟨122248365608116538964937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 651991283243288207812997 122248365608116538964937)
  ·
    refine ⟨91686274206087404223703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122248365608116538964937 91686274206087404223703)
    ·
      refine ⟨137529411309131106335555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91686274206087404223703 137529411309131106335555)
      ·
        refine ⟨206294116963696659503333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137529411309131106335555 206294116963696659503333)
        ·
          refine ⟨38680146930693123656875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206294116963696659503333 38680146930693123656875)
          ·
            refine ⟨58020220396039685485313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38680146930693123656875 58020220396039685485313)
            ·
              refine ⟨43515165297029764113985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58020220396039685485313 43515165297029764113985)
              ·
                refine ⟨32636373972772323085489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43515165297029764113985 32636373972772323085489)
                ·
                  refine ⟨24477280479579242314117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32636373972772323085489 24477280479579242314117)
                  ·
                    refine ⟨4589490089921107933897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24477280479579242314117 4589490089921107933897)
                    ·
                      rfl

theorem cell23_26814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_26814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26814 prefixEnd_26814 := by exact prefixLift 26814
  have htrace : WordTrace (prefixWord ++ tailWord_26814) baseStart_26814 baseEnd_26814 := by
    simpa [prefixWord, tailWord_26814, baseEnd_26814] using wordTrace_append hprefix tailTrace_26814
  have hstable : (prefixWord ++ tailWord_26814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26814).length < 2 ^ (prefixWord ++ tailWord_26814).sum := by decide
  have hdescent : baseEnd_26814 < baseStart_26814 := by decide
  rcases family_descends (prefixWord ++ tailWord_26814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26821 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 1, 2, 2]
def baseStart_26821 : Nat := 118140960795 + 26821 * 2 ^ 59
def prefixEnd_26821 : Nat := 4983230072969 + 3 ^ 40 * 26821 * 2
def baseEnd_26821 : Nat := 13772064634344796414159

theorem tailTrace_26821 : CollatzResearch.WordTrace tailWord_26821 prefixEnd_26821 13772064634344796414159 := by
  unfold tailWord_26821
  simp only [CollatzResearch.WordTrace]
  refine ⟨978242235839572507224317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 652161490559715004816211 978242235839572507224317)
  ·
    refine ⟨366840838439839690209119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 978242235839572507224317 366840838439839690209119)
    ·
      refine ⟨550261257659759535313679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366840838439839690209119 550261257659759535313679)
      ·
        refine ⟨825391886489639302970519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550261257659759535313679 825391886489639302970519)
        ·
          refine ⟨1238087829734458954455779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825391886489639302970519 1238087829734458954455779)
          ·
            refine ⟨1857131744601688431683669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238087829734458954455779 1857131744601688431683669)
            ·
              refine ⟨21763262632051036308793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1857131744601688431683669 21763262632051036308793)
              ·
                refine ⟨16322446974038277231595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21763262632051036308793 16322446974038277231595)
                ·
                  refine ⟨24483670461057415847393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16322446974038277231595 24483670461057415847393)
                  ·
                    refine ⟨18362752845793061885545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24483670461057415847393 18362752845793061885545)
                    ·
                      refine ⟨13772064634344796414159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18362752845793061885545 13772064634344796414159)
                      ·
                        rfl

theorem cell23_26821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_26821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26821 prefixEnd_26821 := by exact prefixLift 26821
  have htrace : WordTrace (prefixWord ++ tailWord_26821) baseStart_26821 baseEnd_26821 := by
    simpa [prefixWord, tailWord_26821, baseEnd_26821] using wordTrace_append hprefix tailTrace_26821
  have hstable : (prefixWord ++ tailWord_26821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26821).length < 2 ^ (prefixWord ++ tailWord_26821).sum := by decide
  have hdescent : baseEnd_26821 < baseStart_26821 := by decide
  rcases family_descends (prefixWord ++ tailWord_26821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26844 : List Nat := [2, 2, 5, 2, 1, 1, 3, 7]
def baseStart_26844 : Nat := 118140960795 + 26844 * 2 ^ 59
def prefixEnd_26844 : Nat := 4983230072969 + 3 ^ 40 * 26844 * 2
def baseEnd_26844 : Nat := 510513877385118756539

theorem tailTrace_26844 : CollatzResearch.WordTrace tailWord_26844 prefixEnd_26844 510513877385118756539 := by
  unfold tailWord_26844
  simp only [CollatzResearch.WordTrace]
  refine ⟨489540557378123717655793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 652720743170831623541057 489540557378123717655793)
  ·
    refine ⟨367155418033592788241845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 489540557378123717655793 367155418033592788241845)
    ·
      refine ⟨34420820440649323897673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 367155418033592788241845 34420820440649323897673)
      ·
        refine ⟨25815615330486992923255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34420820440649323897673 25815615330486992923255)
        ·
          refine ⟨38723422995730489384883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25815615330486992923255 38723422995730489384883)
          ·
            refine ⟨58085134493595734077325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38723422995730489384883 58085134493595734077325)
            ·
              refine ⟨21781925435098400278997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58085134493595734077325 21781925435098400278997)
              ·
                refine ⟨510513877385118756539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21781925435098400278997 510513877385118756539)
                ·
                  rfl

theorem cell23_26844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 7].length) (baseStart_26844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26844 prefixEnd_26844 := by exact prefixLift 26844
  have htrace : WordTrace (prefixWord ++ tailWord_26844) baseStart_26844 baseEnd_26844 := by
    simpa [prefixWord, tailWord_26844, baseEnd_26844] using wordTrace_append hprefix tailTrace_26844
  have hstable : (prefixWord ++ tailWord_26844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26844).length < 2 ^ (prefixWord ++ tailWord_26844).sum := by decide
  have hdescent : baseEnd_26844 < baseStart_26844 := by decide
  rcases family_descends (prefixWord ++ tailWord_26844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26847 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 1, 3, 2]
def baseStart_26847 : Nat := 118140960795 + 26847 * 2 ^ 59
def prefixEnd_26847 : Nat := 4983230072969 + 3 ^ 40 * 26847 * 2
def baseEnd_26847 : Nat := 13785415131361694689039

theorem tailTrace_26847 : CollatzResearch.WordTrace tailWord_26847 prefixEnd_26847 13785415131361694689039 := by
  unfold tailWord_26847
  simp only [CollatzResearch.WordTrace]
  refine ⟨979190533745378947670795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 652793689163585965113863 979190533745378947670795)
  ·
    refine ⟨1468785800618068421506193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 979190533745378947670795 1468785800618068421506193)
    ·
      refine ⟨1101589350463551316129645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1468785800618068421506193 1101589350463551316129645)
      ·
        refine ⟨413096006423831743548617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1101589350463551316129645 413096006423831743548617)
        ·
          refine ⟨309822004817873807661463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413096006423831743548617 309822004817873807661463)
          ·
            refine ⟨464733007226810711492195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309822004817873807661463 464733007226810711492195)
            ·
              refine ⟨697099510840216067238293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464733007226810711492195 697099510840216067238293)
              ·
                refine ⟨32676539570635128151795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 697099510840216067238293 32676539570635128151795)
                ·
                  refine ⟨49014809355952692227693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32676539570635128151795 49014809355952692227693)
                  ·
                    refine ⟨18380553508482259585385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49014809355952692227693 18380553508482259585385)
                    ·
                      refine ⟨13785415131361694689039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18380553508482259585385 13785415131361694689039)
                      ·
                        rfl

theorem cell23_26847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_26847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26847 prefixEnd_26847 := by exact prefixLift 26847
  have htrace : WordTrace (prefixWord ++ tailWord_26847) baseStart_26847 baseEnd_26847 := by
    simpa [prefixWord, tailWord_26847, baseEnd_26847] using wordTrace_append hprefix tailTrace_26847
  have hstable : (prefixWord ++ tailWord_26847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26847).length < 2 ^ (prefixWord ++ tailWord_26847).sum := by decide
  have hdescent : baseEnd_26847 < baseStart_26847 := by decide
  rcases family_descends (prefixWord ++ tailWord_26847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26870 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_26870 : Nat := 118140960795 + 26870 * 2 ^ 59
def prefixEnd_26870 : Nat := 4983230072969 + 3 ^ 40 * 26870 * 2
def baseEnd_26870 : Nat := 4599075062138368233811

theorem tailTrace_26870 : CollatzResearch.WordTrace tailWord_26870 prefixEnd_26870 4599075062138368233811 := by
  unfold tailWord_26870
  simp only [CollatzResearch.WordTrace]
  refine ⟨61251838291378367234879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 653352941774702583838709 61251838291378367234879)
  ·
    refine ⟨91877757437067550852319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61251838291378367234879 91877757437067550852319)
    ·
      refine ⟨137816636155601326278479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91877757437067550852319 137816636155601326278479)
      ·
        refine ⟨206724954233401989417719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137816636155601326278479 206724954233401989417719)
        ·
          refine ⟨310087431350102984126579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206724954233401989417719 310087431350102984126579)
          ·
            refine ⟨465131147025154476189869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310087431350102984126579 465131147025154476189869)
            ·
              refine ⟨174424180134432928571201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465131147025154476189869 174424180134432928571201)
              ·
                refine ⟨130818135100824696428401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174424180134432928571201 130818135100824696428401)
                ·
                  refine ⟨98113601325618522321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130818135100824696428401 98113601325618522321301)
                  ·
                    refine ⟨4599075062138368233811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98113601325618522321301 4599075062138368233811)
                    ·
                      rfl

theorem cell23_26870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_26870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26870 prefixEnd_26870 := by exact prefixLift 26870
  have htrace : WordTrace (prefixWord ++ tailWord_26870) baseStart_26870 baseEnd_26870 := by
    simpa [prefixWord, tailWord_26870, baseEnd_26870] using wordTrace_append hprefix tailTrace_26870
  have hstable : (prefixWord ++ tailWord_26870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26870).length < 2 ^ (prefixWord ++ tailWord_26870).sum := by decide
  have hdescent : baseEnd_26870 < baseStart_26870 := by decide
  rcases family_descends (prefixWord ++ tailWord_26870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26890 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_26890 : Nat := 118140960795 + 26890 * 2 ^ 59
def prefixEnd_26890 : Nat := 4983230072969 + 3 ^ 40 * 26890 * 2
def baseEnd_26890 : Nat := 13807494799505026451341

theorem tailTrace_26890 : CollatzResearch.WordTrace tailWord_26890 prefixEnd_26890 13807494799505026451341 := by
  unfold tailWord_26890
  simp only [CollatzResearch.WordTrace]
  refine ⟨245189718147399322871531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 653839248393064860990749 245189718147399322871531)
  ·
    refine ⟨367784577221098984307297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245189718147399322871531 367784577221098984307297)
    ·
      refine ⟨275838432915824238230473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367784577221098984307297 275838432915824238230473)
      ·
        refine ⟨206878824686868178672855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275838432915824238230473 206878824686868178672855)
        ·
          refine ⟨310318237030302268009283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206878824686868178672855 310318237030302268009283)
          ·
            refine ⟨465477355545453402013925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310318237030302268009283 465477355545453402013925)
            ·
              refine ⟨87277004164772512877611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465477355545453402013925 87277004164772512877611)
              ·
                refine ⟨130915506247158769316417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87277004164772512877611 130915506247158769316417)
                ·
                  refine ⟨98186629685369076987313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130915506247158769316417 98186629685369076987313)
                  ·
                    refine ⟨73639972264026807740485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98186629685369076987313 73639972264026807740485)
                    ·
                      refine ⟨13807494799505026451341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 73639972264026807740485 13807494799505026451341)
                      ·
                        rfl

theorem cell23_26890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_26890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26890 prefixEnd_26890 := by exact prefixLift 26890
  have htrace : WordTrace (prefixWord ++ tailWord_26890) baseStart_26890 baseEnd_26890 := by
    simpa [prefixWord, tailWord_26890, baseEnd_26890] using wordTrace_append hprefix tailTrace_26890
  have hstable : (prefixWord ++ tailWord_26890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26890).length < 2 ^ (prefixWord ++ tailWord_26890).sum := by decide
  have hdescent : baseEnd_26890 < baseStart_26890 := by decide
  rcases family_descends (prefixWord ++ tailWord_26890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26940 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_26940 : Nat := 118140960795 + 26940 * 2 ^ 59
def prefixEnd_26940 : Nat := 4983230072969 + 3 ^ 40 * 26940 * 2
def baseEnd_26940 : Nat := 13833168832229830826111

theorem tailTrace_26940 : CollatzResearch.WordTrace tailWord_26940 prefixEnd_26940 13833168832229830826111 := by
  unfold tailWord_26940
  simp only [CollatzResearch.WordTrace]
  refine ⟨491291261204227915403137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 655055014938970553870849 491291261204227915403137)
  ·
    refine ⟨368468445903170936552353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 491291261204227915403137 368468445903170936552353)
    ·
      refine ⟨276351334427378202414265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368468445903170936552353 276351334427378202414265)
      ·
        refine ⟨207263500820533651810699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276351334427378202414265 207263500820533651810699)
        ·
          refine ⟨310895251230800477716049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207263500820533651810699 310895251230800477716049)
          ·
            refine ⟨233171438423100358287037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310895251230800477716049 233171438423100358287037)
            ·
              refine ⟨87439289408662634357639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233171438423100358287037 87439289408662634357639)
              ·
                refine ⟨131158934112993951536459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87439289408662634357639 131158934112993951536459)
                ·
                  refine ⟨196738401169490927304689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131158934112993951536459 196738401169490927304689)
                  ·
                    refine ⟨147553800877118195478517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196738401169490927304689 147553800877118195478517)
                    ·
                      refine ⟨13833168832229830826111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 147553800877118195478517 13833168832229830826111)
                      ·
                        rfl

theorem cell23_26940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_26940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26940 prefixEnd_26940 := by exact prefixLift 26940
  have htrace : WordTrace (prefixWord ++ tailWord_26940) baseStart_26940 baseEnd_26940 := by
    simpa [prefixWord, tailWord_26940, baseEnd_26940] using wordTrace_append hprefix tailTrace_26940
  have hstable : (prefixWord ++ tailWord_26940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26940).length < 2 ^ (prefixWord ++ tailWord_26940).sum := by decide
  have hdescent : baseEnd_26940 < baseStart_26940 := by decide
  rcases family_descends (prefixWord ++ tailWord_26940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26945 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_26945 : Nat := 118140960795 + 26945 * 2 ^ 59
def prefixEnd_26945 : Nat := 4983230072969 + 3 ^ 40 * 26945 * 2
def baseEnd_26945 : Nat := 13835736235502311263589

theorem tailTrace_26945 : CollatzResearch.WordTrace tailWord_26945 prefixEnd_26945 13835736235502311263589 := by
  unfold tailWord_26945
  simp only [CollatzResearch.WordTrace]
  refine ⟨982764887390341684738289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 655176591593561123158859 982764887390341684738289)
  ·
    refine ⟨737073665542756263553717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 982764887390341684738289 737073665542756263553717)
    ·
      refine ⟨69100656144633399708161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 737073665542756263553717 69100656144633399708161)
      ·
        refine ⟨51825492108475049781121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69100656144633399708161 51825492108475049781121)
        ·
          refine ⟨38869119081356287335841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51825492108475049781121 38869119081356287335841)
          ·
            refine ⟨29151839311017215501881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38869119081356287335841 29151839311017215501881)
            ·
              refine ⟨21863879483262911626411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29151839311017215501881 21863879483262911626411)
              ·
                refine ⟨32795819224894367439617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21863879483262911626411 32795819224894367439617)
                ·
                  refine ⟨24596864418670775579713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32795819224894367439617 24596864418670775579713)
                  ·
                    refine ⟨18447648314003081684785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24596864418670775579713 18447648314003081684785)
                    ·
                      refine ⟨13835736235502311263589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18447648314003081684785 13835736235502311263589)
                      ·
                        rfl

theorem cell23_26945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_26945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26945 prefixEnd_26945 := by exact prefixLift 26945
  have htrace : WordTrace (prefixWord ++ tailWord_26945) baseStart_26945 baseEnd_26945 := by
    simpa [prefixWord, tailWord_26945, baseEnd_26945] using wordTrace_append hprefix tailTrace_26945
  have hstable : (prefixWord ++ tailWord_26945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26945).length < 2 ^ (prefixWord ++ tailWord_26945).sum := by decide
  have hdescent : baseEnd_26945 < baseStart_26945 := by decide
  rcases family_descends (prefixWord ++ tailWord_26945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26967 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_26967 : Nat := 118140960795 + 26967 * 2 ^ 59
def prefixEnd_26967 : Nat := 4983230072969 + 3 ^ 40 * 26967 * 2
def baseEnd_26967 : Nat := 13847032809901225188487

theorem tailTrace_26967 : CollatzResearch.WordTrace tailWord_26967 prefixEnd_26967 13847032809901225188487 := by
  unfold tailWord_26967
  simp only [CollatzResearch.WordTrace]
  refine ⟨983567293310639442039155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 655711528873759628026103 983567293310639442039155)
  ·
    refine ⟨1475350939965959163058733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 983567293310639442039155 1475350939965959163058733)
    ·
      refine ⟨553256602487234686147025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1475350939965959163058733 553256602487234686147025)
      ·
        refine ⟨414942451865426014610269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553256602487234686147025 414942451865426014610269)
        ·
          refine ⟨155603419449534755478851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414942451865426014610269 155603419449534755478851)
          ·
            refine ⟨233405129174302133218277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155603419449534755478851 233405129174302133218277)
            ·
              refine ⟨43763461720181649978427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233405129174302133218277 43763461720181649978427)
              ·
                refine ⟨65645192580272474967641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43763461720181649978427 65645192580272474967641)
                ·
                  refine ⟨49233894435204356225731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65645192580272474967641 49233894435204356225731)
                  ·
                    refine ⟨73850841652806534338597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49233894435204356225731 73850841652806534338597)
                    ·
                      refine ⟨13847032809901225188487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 73850841652806534338597 13847032809901225188487)
                      ·
                        rfl

theorem cell23_26967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_26967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26967 prefixEnd_26967 := by exact prefixLift 26967
  have htrace : WordTrace (prefixWord ++ tailWord_26967) baseStart_26967 baseEnd_26967 := by
    simpa [prefixWord, tailWord_26967, baseEnd_26967] using wordTrace_append hprefix tailTrace_26967
  have hstable : (prefixWord ++ tailWord_26967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26967).length < 2 ^ (prefixWord ++ tailWord_26967).sum := by decide
  have hdescent : baseEnd_26967 < baseStart_26967 := by decide
  rcases family_descends (prefixWord ++ tailWord_26967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26980 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_26980 : Nat := 118140960795 + 26980 * 2 ^ 59
def prefixEnd_26980 : Nat := 4983230072969 + 3 ^ 40 * 26980 * 2
def baseEnd_26980 : Nat := 13853708058409674325927

theorem tailTrace_26980 : CollatzResearch.WordTrace tailWord_26980 prefixEnd_26980 13853708058409674325927 := by
  unfold tailWord_26980
  simp only [CollatzResearch.WordTrace]
  refine ⟨492020721131771331131197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 656027628175695108174929 492020721131771331131197)
  ·
    refine ⟨184507770424414249174199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 492020721131771331131197 184507770424414249174199)
    ·
      refine ⟨276761655636621373761299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184507770424414249174199 276761655636621373761299)
      ·
        refine ⟨415142483454932060641949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276761655636621373761299 415142483454932060641949)
        ·
          refine ⟨155678431295599522740731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415142483454932060641949 155678431295599522740731)
          ·
            refine ⟨233517646943399284111097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155678431295599522740731 233517646943399284111097)
            ·
              refine ⟨175138235207549463083323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233517646943399284111097 175138235207549463083323)
              ·
                refine ⟨262707352811324194624985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175138235207549463083323 262707352811324194624985)
                ·
                  refine ⟨197030514608493145968739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262707352811324194624985 197030514608493145968739)
                  ·
                    refine ⟨295545771912739718953109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197030514608493145968739 295545771912739718953109)
                    ·
                      refine ⟨13853708058409674325927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 295545771912739718953109 13853708058409674325927)
                      ·
                        rfl

theorem cell23_26980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_26980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_26980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_26980 prefixEnd_26980 := by exact prefixLift 26980
  have htrace : WordTrace (prefixWord ++ tailWord_26980) baseStart_26980 baseEnd_26980 := by
    simpa [prefixWord, tailWord_26980, baseEnd_26980] using wordTrace_append hprefix tailTrace_26980
  have hstable : (prefixWord ++ tailWord_26980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26980).length < 2 ^ (prefixWord ++ tailWord_26980).sum := by decide
  have hdescent : baseEnd_26980 < baseStart_26980 := by decide
  rcases family_descends (prefixWord ++ tailWord_26980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27018 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_27018 : Nat := 118140960795 + 27018 * 2 ^ 59
def prefixEnd_27018 : Nat := 4983230072969 + 3 ^ 40 * 27018 * 2
def baseEnd_27018 : Nat := 13873220323280525650753

theorem tailTrace_27018 : CollatzResearch.WordTrace tailWord_27018 prefixEnd_27018 13873220323280525650753 := by
  unfold tailWord_27018
  simp only [CollatzResearch.WordTrace]
  refine ⟨246356854031468788036427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 656951610750583434763805 246356854031468788036427)
  ·
    refine ⟨369535281047203182054641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246356854031468788036427 369535281047203182054641)
    ·
      refine ⟨277151460785402386540981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369535281047203182054641 277151460785402386540981)
      ·
        refine ⟨25982949448631473738217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277151460785402386540981 25982949448631473738217)
        ·
          refine ⟨19487212086473605303663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25982949448631473738217 19487212086473605303663)
          ·
            refine ⟨29230818129710407955495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19487212086473605303663 29230818129710407955495)
            ·
              refine ⟨43846227194565611933243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29230818129710407955495 43846227194565611933243)
              ·
                refine ⟨65769340791848417899865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43846227194565611933243 65769340791848417899865)
                ·
                  refine ⟨49327005593886313424899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65769340791848417899865 49327005593886313424899)
                  ·
                    refine ⟨73990508390829470137349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49327005593886313424899 73990508390829470137349)
                    ·
                      refine ⟨13873220323280525650753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 73990508390829470137349 13873220323280525650753)
                      ·
                        rfl

theorem cell23_27018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_27018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27018 prefixEnd_27018 := by exact prefixLift 27018
  have htrace : WordTrace (prefixWord ++ tailWord_27018) baseStart_27018 baseEnd_27018 := by
    simpa [prefixWord, tailWord_27018, baseEnd_27018] using wordTrace_append hprefix tailTrace_27018
  have hstable : (prefixWord ++ tailWord_27018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27018).length < 2 ^ (prefixWord ++ tailWord_27018).sum := by decide
  have hdescent : baseEnd_27018 < baseStart_27018 := by decide
  rcases family_descends (prefixWord ++ tailWord_27018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27028 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_27028 : Nat := 118140960795 + 27028 * 2 ^ 59
def prefixEnd_27028 : Nat := 4983230072969 + 3 ^ 40 * 27028 * 2
def baseEnd_27028 : Nat := 4626118376608495508569

theorem tailTrace_27028 : CollatzResearch.WordTrace tailWord_27028 prefixEnd_27028 4626118376608495508569 := by
  unfold tailWord_27028
  simp only [CollatzResearch.WordTrace]
  refine ⟨492896073044823430004869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 657194764059764573339825 492896073044823430004869)
  ·
    refine ⟨92418013695904393125913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 492896073044823430004869 92418013695904393125913)
    ·
      refine ⟨69313510271928294844435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92418013695904393125913 69313510271928294844435)
      ·
        refine ⟨103970265407892442266653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69313510271928294844435 103970265407892442266653)
        ·
          refine ⟨38988849527959665849995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103970265407892442266653 38988849527959665849995)
          ·
            refine ⟨58483274291939498774993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38988849527959665849995 58483274291939498774993)
            ·
              refine ⟨43862455718954624081245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58483274291939498774993 43862455718954624081245)
              ·
                refine ⟨16448420894607984030467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43862455718954624081245 16448420894607984030467)
                ·
                  refine ⟨24672631341911976045701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16448420894607984030467 24672631341911976045701)
                  ·
                    refine ⟨4626118376608495508569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24672631341911976045701 4626118376608495508569)
                    ·
                      rfl

theorem cell23_27028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_27028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27028 prefixEnd_27028 := by exact prefixLift 27028
  have htrace : WordTrace (prefixWord ++ tailWord_27028) baseStart_27028 baseEnd_27028 := by
    simpa [prefixWord, tailWord_27028, baseEnd_27028] using wordTrace_append hprefix tailTrace_27028
  have hstable : (prefixWord ++ tailWord_27028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27028).length < 2 ^ (prefixWord ++ tailWord_27028).sum := by decide
  have hdescent : baseEnd_27028 < baseStart_27028 := by decide
  rcases family_descends (prefixWord ++ tailWord_27028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27041 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 6]
def baseStart_27041 : Nat := 118140960795 + 27041 * 2 ^ 59
def prefixEnd_27041 : Nat := 4983230072969 + 3 ^ 40 * 27041 * 2
def baseEnd_27041 : Nat := 1542781153148215073683

theorem tailTrace_27041 : CollatzResearch.WordTrace tailWord_27041 prefixEnd_27041 1542781153148215073683 := by
  unfold tailWord_27041
  simp only [CollatzResearch.WordTrace]
  refine ⟨986266295042550080232977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 657510863361700053488651 986266295042550080232977)
  ·
    refine ⟨739699721281912560174733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 986266295042550080232977 739699721281912560174733)
    ·
      refine ⟨277387395480717210065525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 739699721281912560174733 277387395480717210065525)
      ·
        refine ⟨26005068326317238443643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277387395480717210065525 26005068326317238443643)
        ·
          refine ⟨39007602489475857665465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26005068326317238443643 39007602489475857665465)
          ·
            refine ⟨29255701867106893249099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39007602489475857665465 29255701867106893249099)
            ·
              refine ⟨43883552800660339873649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29255701867106893249099 43883552800660339873649)
              ·
                refine ⟨32912664600495254905237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43883552800660339873649 32912664600495254905237)
                ·
                  refine ⟨1542781153148215073683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32912664600495254905237 1542781153148215073683)
                  ·
                    rfl

theorem cell23_27041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 6].length) (baseStart_27041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27041 prefixEnd_27041 := by exact prefixLift 27041
  have htrace : WordTrace (prefixWord ++ tailWord_27041) baseStart_27041 baseEnd_27041 := by
    simpa [prefixWord, tailWord_27041, baseEnd_27041] using wordTrace_append hprefix tailTrace_27041
  have hstable : (prefixWord ++ tailWord_27041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27041).length < 2 ^ (prefixWord ++ tailWord_27041).sum := by decide
  have hdescent : baseEnd_27041 < baseStart_27041 := by decide
  rcases family_descends (prefixWord ++ tailWord_27041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27044 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_27044 : Nat := 118140960795 + 27044 * 2 ^ 59
def prefixEnd_27044 : Nat := 4983230072969 + 3 ^ 40 * 27044 * 2
def baseEnd_27044 : Nat := 13886570820297423925633

theorem tailTrace_27044 : CollatzResearch.WordTrace tailWord_27044 prefixEnd_27044 13886570820297423925633 := by
  unfold tailWord_27044
  simp only [CollatzResearch.WordTrace]
  refine ⟨493187857015840796296093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 657583809354454395061457 493187857015840796296093)
  ·
    refine ⟨184945446380940298611035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 493187857015840796296093 184945446380940298611035)
    ·
      refine ⟨277418169571410447916553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184945446380940298611035 277418169571410447916553)
      ·
        refine ⟨208063627178557835937415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277418169571410447916553 208063627178557835937415)
        ·
          refine ⟨312095440767836753906123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208063627178557835937415 312095440767836753906123)
          ·
            refine ⟨468143161151755130859185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312095440767836753906123 468143161151755130859185)
            ·
              refine ⟨351107370863816348144389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468143161151755130859185 351107370863816348144389)
              ·
                refine ⟨65832632036965565277073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351107370863816348144389 65832632036965565277073)
                ·
                  refine ⟨49374474027724173957805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65832632036965565277073 49374474027724173957805)
                  ·
                    refine ⟨18515427760396565234177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49374474027724173957805 18515427760396565234177)
                    ·
                      refine ⟨13886570820297423925633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18515427760396565234177 13886570820297423925633)
                      ·
                        rfl

theorem cell23_27044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_27044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27044 prefixEnd_27044 := by exact prefixLift 27044
  have htrace : WordTrace (prefixWord ++ tailWord_27044) baseStart_27044 baseEnd_27044 := by
    simpa [prefixWord, tailWord_27044, baseEnd_27044] using wordTrace_append hprefix tailTrace_27044
  have hstable : (prefixWord ++ tailWord_27044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27044).length < 2 ^ (prefixWord ++ tailWord_27044).sum := by decide
  have hdescent : baseEnd_27044 < baseStart_27044 := by decide
  rcases family_descends (prefixWord ++ tailWord_27044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27118 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_27118 : Nat := 118140960795 + 27118 * 2 ^ 59
def prefixEnd_27118 : Nat := 4983230072969 + 3 ^ 40 * 27118 * 2
def baseEnd_27118 : Nat := 4641522796243378133431

theorem tailTrace_27118 : CollatzResearch.WordTrace tailWord_27118 prefixEnd_27118 4641522796243378133431 := by
  unfold tailWord_27118
  simp only [CollatzResearch.WordTrace]
  refine ⟨123634339470449028848251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 659383143842394820524005 123634339470449028848251)
  ·
    refine ⟨185451509205673543272377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123634339470449028848251 185451509205673543272377)
    ·
      refine ⟨139088631904255157454283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185451509205673543272377 139088631904255157454283)
      ·
        refine ⟨208632947856382736181425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139088631904255157454283 208632947856382736181425)
        ·
          refine ⟨156474710892287052136069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208632947856382736181425 156474710892287052136069)
          ·
            refine ⟨29339008292303822275513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156474710892287052136069 29339008292303822275513)
            ·
              refine ⟨22004256219227866706635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29339008292303822275513 22004256219227866706635)
              ·
                refine ⟨33006384328841800059953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22004256219227866706635 33006384328841800059953)
                ·
                  refine ⟨24754788246631350044965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33006384328841800059953 24754788246631350044965)
                  ·
                    refine ⟨4641522796243378133431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24754788246631350044965 4641522796243378133431)
                    ·
                      rfl

theorem cell23_27118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_27118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27118 prefixEnd_27118 := by exact prefixLift 27118
  have htrace : WordTrace (prefixWord ++ tailWord_27118) baseStart_27118 baseEnd_27118 := by
    simpa [prefixWord, tailWord_27118, baseEnd_27118] using wordTrace_append hprefix tailTrace_27118
  have hstable : (prefixWord ++ tailWord_27118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27118).length < 2 ^ (prefixWord ++ tailWord_27118).sum := by decide
  have hdescent : baseEnd_27118 < baseStart_27118 := by decide
  rcases family_descends (prefixWord ++ tailWord_27118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27125 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_27125 : Nat := 118140960795 + 27125 * 2 ^ 59
def prefixEnd_27125 : Nat := 4983230072969 + 3 ^ 40 * 27125 * 2
def baseEnd_27125 : Nat := 13928162753311607012761

theorem tailTrace_27125 : CollatzResearch.WordTrace tailWord_27125 prefixEnd_27125 13928162753311607012761 := by
  unfold tailWord_27125
  simp only [CollatzResearch.WordTrace]
  refine ⟨989330026738232426290829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 659553351158821617527219 989330026738232426290829)
  ·
    refine ⟨370998760026837159859061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 989330026738232426290829 370998760026837159859061)
    ·
      refine ⟨34781133752515983736787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 370998760026837159859061 34781133752515983736787)
      ·
        refine ⟨52171700628773975605181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34781133752515983736787 52171700628773975605181)
        ·
          refine ⟨19564387735790240851943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52171700628773975605181 19564387735790240851943)
          ·
            refine ⟨29346581603685361277915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19564387735790240851943 29346581603685361277915)
            ·
              refine ⟨44019872405528041916873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29346581603685361277915 44019872405528041916873)
              ·
                refine ⟨33014904304146031437655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44019872405528041916873 33014904304146031437655)
                ·
                  refine ⟨49522356456219047156483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33014904304146031437655 49522356456219047156483)
                  ·
                    refine ⟨74283534684328570734725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49522356456219047156483 74283534684328570734725)
                    ·
                      refine ⟨13928162753311607012761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 74283534684328570734725 13928162753311607012761)
                      ·
                        rfl

theorem cell23_27125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_27125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27125 prefixEnd_27125 := by exact prefixLift 27125
  have htrace : WordTrace (prefixWord ++ tailWord_27125) baseStart_27125 baseEnd_27125 := by
    simpa [prefixWord, tailWord_27125, baseEnd_27125] using wordTrace_append hprefix tailTrace_27125
  have hstable : (prefixWord ++ tailWord_27125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27125).length < 2 ^ (prefixWord ++ tailWord_27125).sum := by decide
  have hdescent : baseEnd_27125 < baseStart_27125 := by decide
  rcases family_descends (prefixWord ++ tailWord_27125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27142 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_27142 : Nat := 118140960795 + 27142 * 2 ^ 59
def prefixEnd_27142 : Nat := 4983230072969 + 3 ^ 40 * 27142 * 2
def baseEnd_27142 : Nat := 13936891924438040500183

theorem tailTrace_27142 : CollatzResearch.WordTrace tailWord_27142 prefixEnd_27142 13936891924438040500183 := by
  unfold tailWord_27142
  simp only [CollatzResearch.WordTrace]
  refine ⟨30935939614895135301865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 659966711784429553106453 30935939614895135301865)
  ·
    refine ⟨23201954711171351476399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30935939614895135301865 23201954711171351476399)
    ·
      refine ⟨34802932066757027214599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23201954711171351476399 34802932066757027214599)
      ·
        refine ⟨52204398100135540821899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34802932066757027214599 52204398100135540821899)
        ·
          refine ⟨78306597150203311232849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52204398100135540821899 78306597150203311232849)
          ·
            refine ⟨58729947862652483424637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78306597150203311232849 58729947862652483424637)
            ·
              refine ⟨22023730448494681284239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58729947862652483424637 22023730448494681284239)
              ·
                refine ⟨33035595672742021926359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22023730448494681284239 33035595672742021926359)
                ·
                  refine ⟨49553393509113032889539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33035595672742021926359 49553393509113032889539)
                  ·
                    refine ⟨74330090263669549334309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49553393509113032889539 74330090263669549334309)
                    ·
                      refine ⟨13936891924438040500183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 74330090263669549334309 13936891924438040500183)
                      ·
                        rfl

theorem cell23_27142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_27142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27142 prefixEnd_27142 := by exact prefixLift 27142
  have htrace : WordTrace (prefixWord ++ tailWord_27142) baseStart_27142 baseEnd_27142 := by
    simpa [prefixWord, tailWord_27142, baseEnd_27142] using wordTrace_append hprefix tailTrace_27142
  have hstable : (prefixWord ++ tailWord_27142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27142).length < 2 ^ (prefixWord ++ tailWord_27142).sum := by decide
  have hdescent : baseEnd_27142 < baseStart_27142 := by decide
  rcases family_descends (prefixWord ++ tailWord_27142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27157 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_27157 : Nat := 118140960795 + 27157 * 2 ^ 59
def prefixEnd_27157 : Nat := 4983230072969 + 3 ^ 40 * 27157 * 2
def baseEnd_27157 : Nat := 4648198044751827270871

theorem tailTrace_27157 : CollatzResearch.WordTrace tailWord_27157 prefixEnd_27157 4648198044751827270871 := by
  unfold tailWord_27157
  simp only [CollatzResearch.WordTrace]
  refine ⟨990497162622301891455725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 660331441748201260970483 990497162622301891455725)
  ·
    refine ⟨371436435983363209295897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 990497162622301891455725 371436435983363209295897)
    ·
      refine ⟨278577326987522406971923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371436435983363209295897 278577326987522406971923)
      ·
        refine ⟨417865990481283610457885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278577326987522406971923 417865990481283610457885)
        ·
          refine ⟨156699746430481353921707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417865990481283610457885 156699746430481353921707)
          ·
            refine ⟨235049619645722030882561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156699746430481353921707 235049619645722030882561)
            ·
              refine ⟨176287214734291523161921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235049619645722030882561 176287214734291523161921)
              ·
                refine ⟨132215411050718642371441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176287214734291523161921 132215411050718642371441)
                ·
                  refine ⟨99161558288038981778581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132215411050718642371441 99161558288038981778581)
                  ·
                    refine ⟨4648198044751827270871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99161558288038981778581 4648198044751827270871)
                    ·
                      rfl

theorem cell23_27157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_27157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27157 prefixEnd_27157 := by exact prefixLift 27157
  have htrace : WordTrace (prefixWord ++ tailWord_27157) baseStart_27157 baseEnd_27157 := by
    simpa [prefixWord, tailWord_27157, baseEnd_27157] using wordTrace_append hprefix tailTrace_27157
  have hstable : (prefixWord ++ tailWord_27157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27157).length < 2 ^ (prefixWord ++ tailWord_27157).sum := by decide
  have hdescent : baseEnd_27157 < baseStart_27157 := by decide
  rcases family_descends (prefixWord ++ tailWord_27157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27159 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 1, 2, 2]
def baseStart_27159 : Nat := 118140960795 + 27159 * 2 ^ 59
def prefixEnd_27159 : Nat := 4983230072969 + 3 ^ 40 * 27159 * 2
def baseEnd_27159 : Nat := 13945621095564473987605

theorem tailTrace_27159 : CollatzResearch.WordTrace tailWord_27159 prefixEnd_27159 13945621095564473987605 := by
  unfold tailWord_27159
  simp only [CollatzResearch.WordTrace]
  refine ⟨990570108615056233028531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 660380072410037488685687 990570108615056233028531)
  ·
    refine ⟨1485855162922584349542797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990570108615056233028531 1485855162922584349542797)
    ·
      refine ⟨557195686095969131078549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1485855162922584349542797 557195686095969131078549)
      ·
        refine ⟨26118547785748553019307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 557195686095969131078549 26118547785748553019307)
        ·
          refine ⟨39177821678622829528961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26118547785748553019307 39177821678622829528961)
          ·
            refine ⟨29383366258967122146721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39177821678622829528961 29383366258967122146721)
            ·
              refine ⟨22037524694225341610041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29383366258967122146721 22037524694225341610041)
              ·
                refine ⟨16528143520669006207531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22037524694225341610041 16528143520669006207531)
                ·
                  refine ⟨24792215281003509311297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16528143520669006207531 24792215281003509311297)
                  ·
                    refine ⟨18594161460752631983473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24792215281003509311297 18594161460752631983473)
                    ·
                      refine ⟨13945621095564473987605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18594161460752631983473 13945621095564473987605)
                      ·
                        rfl

theorem cell23_27159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_27159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27159 prefixEnd_27159 := by exact prefixLift 27159
  have htrace : WordTrace (prefixWord ++ tailWord_27159) baseStart_27159 baseEnd_27159 := by
    simpa [prefixWord, tailWord_27159, baseEnd_27159] using wordTrace_append hprefix tailTrace_27159
  have hstable : (prefixWord ++ tailWord_27159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27159).length < 2 ^ (prefixWord ++ tailWord_27159).sum := by decide
  have hdescent : baseEnd_27159 < baseStart_27159 := by decide
  rcases family_descends (prefixWord ++ tailWord_27159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27187 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 7]
def baseStart_27187 : Nat := 118140960795 + 27187 * 2 ^ 59
def prefixEnd_27187 : Nat := 4983230072969 + 3 ^ 40 * 27187 * 2
def baseEnd_27187 : Nat := 1551110950432262715275

theorem tailTrace_27187 : CollatzResearch.WordTrace tailWord_27187 prefixEnd_27187 1551110950432262715275 := by
  unfold tailWord_27187
  simp only [CollatzResearch.WordTrace]
  refine ⟨991591352513617015047815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 661060901675744676698543 991591352513617015047815)
  ·
    refine ⟨1487387028770425522571723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991591352513617015047815 1487387028770425522571723)
    ·
      refine ⟨2231080543155638283857585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487387028770425522571723 2231080543155638283857585)
      ·
        refine ⟨1673310407366728712893189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2231080543155638283857585 1673310407366728712893189)
        ·
          refine ⟨313745701381261633667473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1673310407366728712893189 313745701381261633667473)
          ·
            refine ⟨235309276035946225250605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313745701381261633667473 235309276035946225250605)
            ·
              refine ⟨88240978513479834468977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235309276035946225250605 88240978513479834468977)
              ·
                refine ⟨66180733885109875851733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88240978513479834468977 66180733885109875851733)
                ·
                  refine ⟨1551110950432262715275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 66180733885109875851733 1551110950432262715275)
                  ·
                    rfl

theorem cell23_27187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 7].length) (baseStart_27187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27187 prefixEnd_27187 := by exact prefixLift 27187
  have htrace : WordTrace (prefixWord ++ tailWord_27187) baseStart_27187 baseEnd_27187 := by
    simpa [prefixWord, tailWord_27187, baseEnd_27187] using wordTrace_append hprefix tailTrace_27187
  have hstable : (prefixWord ++ tailWord_27187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27187).length < 2 ^ (prefixWord ++ tailWord_27187).sum := by decide
  have hdescent : baseEnd_27187 < baseStart_27187 := by decide
  rcases family_descends (prefixWord ++ tailWord_27187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27214 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_27214 : Nat := 118140960795 + 27214 * 2 ^ 59
def prefixEnd_27214 : Nat := 4983230072969 + 3 ^ 40 * 27214 * 2
def baseEnd_27214 : Nat := 13973862531561758799851

theorem tailTrace_27214 : CollatzResearch.WordTrace tailWord_27214 prefixEnd_27214 13973862531561758799851 := by
  unfold tailWord_27214
  simp only [CollatzResearch.WordTrace]
  refine ⟨124072015426975078285087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 661717415610533750853797 124072015426975078285087)
  ·
    refine ⟨186108023140462617427631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124072015426975078285087 186108023140462617427631)
    ·
      refine ⟨279162034710693926141447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186108023140462617427631 279162034710693926141447)
      ·
        refine ⟨418743052066040889212171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279162034710693926141447 418743052066040889212171)
        ·
          refine ⟨628114578099061333818257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418743052066040889212171 628114578099061333818257)
          ·
            refine ⟨471085933574296000363693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628114578099061333818257 471085933574296000363693)
            ·
              refine ⟨176657225090361000136385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471085933574296000363693 176657225090361000136385)
              ·
                refine ⟨132492918817770750102289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176657225090361000136385 132492918817770750102289)
                ·
                  refine ⟨99369689113328062576717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132492918817770750102289 99369689113328062576717)
                  ·
                    refine ⟨37263633417498023466269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99369689113328062576717 37263633417498023466269)
                    ·
                      refine ⟨13973862531561758799851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 37263633417498023466269 13973862531561758799851)
                      ·
                        rfl

theorem cell23_27214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_27214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27214 prefixEnd_27214 := by exact prefixLift 27214
  have htrace : WordTrace (prefixWord ++ tailWord_27214) baseStart_27214 baseEnd_27214 := by
    simpa [prefixWord, tailWord_27214, baseEnd_27214] using wordTrace_append hprefix tailTrace_27214
  have hstable : (prefixWord ++ tailWord_27214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27214).length < 2 ^ (prefixWord ++ tailWord_27214).sum := by decide
  have hdescent : baseEnd_27214 < baseStart_27214 := by decide
  rcases family_descends (prefixWord ++ tailWord_27214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27224 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 7, 2]
def baseStart_27224 : Nat := 118140960795 + 27224 * 2 ^ 59
def prefixEnd_27224 : Nat := 4983230072969 + 3 ^ 40 * 27224 * 2
def baseEnd_27224 : Nat := 13978997338106719674805

theorem tailTrace_27224 : CollatzResearch.WordTrace tailWord_27224 prefixEnd_27224 13978997338106719674805 := by
  unfold tailWord_27224
  simp only [CollatzResearch.WordTrace]
  refine ⟨496470426689786167072363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 661960568919714889429817 496470426689786167072363)
  ·
    refine ⟨744705640034679250608545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 496470426689786167072363 744705640034679250608545)
    ·
      refine ⟨558529230026009437956409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 744705640034679250608545 558529230026009437956409)
      ·
        refine ⟨418896922519507078467307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558529230026009437956409 418896922519507078467307)
        ·
          refine ⟨628345383779260617700961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418896922519507078467307 628345383779260617700961)
          ·
            refine ⟨471259037834445463275721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628345383779260617700961 471259037834445463275721)
            ·
              refine ⟨353444278375834097456791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471259037834445463275721 353444278375834097456791)
              ·
                refine ⟨530166417563751146185187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353444278375834097456791 530166417563751146185187)
                ·
                  refine ⟨795249626345626719277781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530166417563751146185187 795249626345626719277781)
                  ·
                    refine ⟨18638663117475626233073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 795249626345626719277781 18638663117475626233073)
                    ·
                      refine ⟨13978997338106719674805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18638663117475626233073 13978997338106719674805)
                      ·
                        rfl

theorem cell23_27224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_27224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27224 prefixEnd_27224 := by exact prefixLift 27224
  have htrace : WordTrace (prefixWord ++ tailWord_27224) baseStart_27224 baseEnd_27224 := by
    simpa [prefixWord, tailWord_27224, baseEnd_27224] using wordTrace_append hprefix tailTrace_27224
  have hstable : (prefixWord ++ tailWord_27224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27224).length < 2 ^ (prefixWord ++ tailWord_27224).sum := by decide
  have hdescent : baseEnd_27224 < baseStart_27224 := by decide
  rcases family_descends (prefixWord ++ tailWord_27224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27267 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_27267 : Nat := 118140960795 + 27267 * 2 ^ 59
def prefixEnd_27267 : Nat := 4983230072969 + 3 ^ 40 * 27267 * 2
def baseEnd_27267 : Nat := 14001077006250051437107

theorem tailTrace_27267 : CollatzResearch.WordTrace tailWord_27267 prefixEnd_27267 14001077006250051437107 := by
  unfold tailWord_27267
  simp only [CollatzResearch.WordTrace]
  refine ⟨994509192223790677960055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 663006128149193785306703 994509192223790677960055)
  ·
    refine ⟨1491763788335686016940083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994509192223790677960055 1491763788335686016940083)
    ·
      refine ⟨2237645682503529025410125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491763788335686016940083 2237645682503529025410125)
      ·
        refine ⟨839117130938823384528797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2237645682503529025410125 839117130938823384528797)
        ·
          refine ⟨314668924102058769198299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839117130938823384528797 314668924102058769198299)
          ·
            refine ⟨472003386153088153797449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314668924102058769198299 472003386153088153797449)
            ·
              refine ⟨354002539614816115348087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472003386153088153797449 354002539614816115348087)
              ·
                refine ⟨531003809422224173022131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354002539614816115348087 531003809422224173022131)
                ·
                  refine ⟨796505714133336259533197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531003809422224173022131 796505714133336259533197)
                  ·
                    refine ⟨298689642800001097324949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796505714133336259533197 298689642800001097324949)
                    ·
                      refine ⟨14001077006250051437107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 298689642800001097324949 14001077006250051437107)
                      ·
                        rfl

theorem cell23_27267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_27267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27267 prefixEnd_27267 := by exact prefixLift 27267
  have htrace : WordTrace (prefixWord ++ tailWord_27267) baseStart_27267 baseEnd_27267 := by
    simpa [prefixWord, tailWord_27267, baseEnd_27267] using wordTrace_append hprefix tailTrace_27267
  have hstable : (prefixWord ++ tailWord_27267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27267).length < 2 ^ (prefixWord ++ tailWord_27267).sum := by decide
  have hdescent : baseEnd_27267 < baseStart_27267 := by decide
  rcases family_descends (prefixWord ++ tailWord_27267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27332 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_27332 : Nat := 118140960795 + 27332 * 2 ^ 59
def prefixEnd_27332 : Nat := 4983230072969 + 3 ^ 40 * 27332 * 2
def baseEnd_27332 : Nat := 4678151082930765708103

theorem tailTrace_27332 : CollatzResearch.WordTrace tailWord_27332 prefixEnd_27332 4678151082930765708103 := by
  unfold tailWord_27332
  simp only [CollatzResearch.WordTrace]
  refine ⟨498439968494153389538125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 664586624658871186050833 498439968494153389538125)
  ·
    refine ⟨186914988185307521076797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 498439968494153389538125 186914988185307521076797)
    ·
      refine ⟨70093120569490320403799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186914988185307521076797 70093120569490320403799)
      ·
        refine ⟨105139680854235480605699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70093120569490320403799 105139680854235480605699)
        ·
          refine ⟨157709521281353220908549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105139680854235480605699 157709521281353220908549)
          ·
            refine ⟨29570535240253728920353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157709521281353220908549 29570535240253728920353)
            ·
              refine ⟨22177901430190296690265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29570535240253728920353 22177901430190296690265)
              ·
                refine ⟨16633426072642722517699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22177901430190296690265 16633426072642722517699)
                ·
                  refine ⟨24950139108964083776549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16633426072642722517699 24950139108964083776549)
                  ·
                    refine ⟨4678151082930765708103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24950139108964083776549 4678151082930765708103)
                    ·
                      rfl

theorem cell23_27332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_27332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27332 prefixEnd_27332 := by exact prefixLift 27332
  have htrace : WordTrace (prefixWord ++ tailWord_27332) baseStart_27332 baseEnd_27332 := by
    simpa [prefixWord, tailWord_27332, baseEnd_27332] using wordTrace_append hprefix tailTrace_27332
  have hstable : (prefixWord ++ tailWord_27332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27332).length < 2 ^ (prefixWord ++ tailWord_27332).sum := by decide
  have hdescent : baseEnd_27332 < baseStart_27332 := by decide
  rcases family_descends (prefixWord ++ tailWord_27332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27361 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_27361 : Nat := 118140960795 + 27361 * 2 ^ 59
def prefixEnd_27361 : Nat := 4983230072969 + 3 ^ 40 * 27361 * 2
def baseEnd_27361 : Nat := 14049344187772683661675

theorem tailTrace_27361 : CollatzResearch.WordTrace tailWord_27361 prefixEnd_27361 14049344187772683661675 := by
  unfold tailWord_27361
  simp only [CollatzResearch.WordTrace]
  refine ⟨997937653883244731881937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 665291769255496487921291 997937653883244731881937)
  ·
    refine ⟨748453240412433548911453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 997937653883244731881937 748453240412433548911453)
    ·
      refine ⟨280669965154662580841795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 748453240412433548911453 280669965154662580841795)
      ·
        refine ⟨421004947731993871262693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280669965154662580841795 421004947731993871262693)
        ·
          refine ⟨78938427699748850861755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421004947731993871262693 78938427699748850861755)
          ·
            refine ⟨118407641549623276292633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78938427699748850861755 118407641549623276292633)
            ·
              refine ⟨88805731162217457219475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118407641549623276292633 88805731162217457219475)
              ·
                refine ⟨133208596743326185829213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88805731162217457219475 133208596743326185829213)
                ·
                  refine ⟨49953223778747319685955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133208596743326185829213 49953223778747319685955)
                  ·
                    refine ⟨74929835668120979528933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49953223778747319685955 74929835668120979528933)
                    ·
                      refine ⟨14049344187772683661675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 74929835668120979528933 14049344187772683661675)
                      ·
                        rfl

theorem cell23_27361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_27361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27361 prefixEnd_27361 := by exact prefixLift 27361
  have htrace : WordTrace (prefixWord ++ tailWord_27361) baseStart_27361 baseEnd_27361 := by
    simpa [prefixWord, tailWord_27361, baseEnd_27361] using wordTrace_append hprefix tailTrace_27361
  have hstable : (prefixWord ++ tailWord_27361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27361).length < 2 ^ (prefixWord ++ tailWord_27361).sum := by decide
  have hdescent : baseEnd_27361 < baseStart_27361 := by decide
  rcases family_descends (prefixWord ++ tailWord_27361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27365 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 2, 3, 2]
def baseStart_27365 : Nat := 118140960795 + 27365 * 2 ^ 59
def prefixEnd_27365 : Nat := 4983230072969 + 3 ^ 40 * 27365 * 2
def baseEnd_27365 : Nat := 14051398110390668011657

theorem tailTrace_27365 : CollatzResearch.WordTrace tailWord_27365 prefixEnd_27365 14051398110390668011657 := by
  unfold tailWord_27365
  simp only [CollatzResearch.WordTrace]
  refine ⟨998083545868753415027549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 665389030579168943351699 998083545868753415027549)
  ·
    refine ⟨374281329700782530635331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 998083545868753415027549 374281329700782530635331)
    ·
      refine ⟨561421994551173795952997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374281329700782530635331 561421994551173795952997)
      ·
        refine ⟨105266623978345086741187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561421994551173795952997 105266623978345086741187)
        ·
          refine ⟨157899935967517630111781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105266623978345086741187 157899935967517630111781)
          ·
            refine ⟨29606237993909555645959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157899935967517630111781 29606237993909555645959)
            ·
              refine ⟨44409356990864333468939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29606237993909555645959 44409356990864333468939)
              ·
                refine ⟨66614035486296500203409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44409356990864333468939 66614035486296500203409)
                ·
                  refine ⟨49960526614722375152557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66614035486296500203409 49960526614722375152557)
                  ·
                    refine ⟨18735197480520890682209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49960526614722375152557 18735197480520890682209)
                    ·
                      refine ⟨14051398110390668011657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18735197480520890682209 14051398110390668011657)
                      ·
                        rfl

theorem cell23_27365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_27365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27365 prefixEnd_27365 := by exact prefixLift 27365
  have htrace : WordTrace (prefixWord ++ tailWord_27365) baseStart_27365 baseEnd_27365 := by
    simpa [prefixWord, tailWord_27365, baseEnd_27365] using wordTrace_append hprefix tailTrace_27365
  have hstable : (prefixWord ++ tailWord_27365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27365).length < 2 ^ (prefixWord ++ tailWord_27365).sum := by decide
  have hdescent : baseEnd_27365 < baseStart_27365 := by decide
  rcases family_descends (prefixWord ++ tailWord_27365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27378 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_27378 : Nat := 118140960795 + 27378 * 2 ^ 59
def prefixEnd_27378 : Nat := 4983230072969 + 3 ^ 40 * 27378 * 2
def baseEnd_27378 : Nat := 14058073358899117149097

theorem tailTrace_27378 : CollatzResearch.WordTrace tailWord_27378 prefixEnd_27378 14058073358899117149097 := by
  unfold tailWord_27378
  simp only [CollatzResearch.WordTrace]
  refine ⟨249639423705414158812697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 665705129881104423500525 249639423705414158812697)
  ·
    refine ⟨187229567779060619109523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249639423705414158812697 187229567779060619109523)
    ·
      refine ⟨280844351668590928664285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187229567779060619109523 280844351668590928664285)
      ·
        refine ⟨105316631875721598249107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280844351668590928664285 105316631875721598249107)
        ·
          refine ⟨157974947813582397373661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105316631875721598249107 157974947813582397373661)
          ·
            refine ⟨59240605430093399015123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157974947813582397373661 59240605430093399015123)
            ·
              refine ⟨88860908145140098522685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59240605430093399015123 88860908145140098522685)
              ·
                refine ⟨33322840554427536946007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88860908145140098522685 33322840554427536946007)
                ·
                  refine ⟨49984260831641305419011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33322840554427536946007 49984260831641305419011)
                  ·
                    refine ⟨74976391247461958128517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49984260831641305419011 74976391247461958128517)
                    ·
                      refine ⟨14058073358899117149097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 74976391247461958128517 14058073358899117149097)
                      ·
                        rfl

theorem cell23_27378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_27378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27378 prefixEnd_27378 := by exact prefixLift 27378
  have htrace : WordTrace (prefixWord ++ tailWord_27378) baseStart_27378 baseEnd_27378 := by
    simpa [prefixWord, tailWord_27378, baseEnd_27378] using wordTrace_append hprefix tailTrace_27378
  have hstable : (prefixWord ++ tailWord_27378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27378).length < 2 ^ (prefixWord ++ tailWord_27378).sum := by decide
  have hdescent : baseEnd_27378 < baseStart_27378 := by decide
  rcases family_descends (prefixWord ++ tailWord_27378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27388 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_27388 : Nat := 118140960795 + 27388 * 2 ^ 59
def prefixEnd_27388 : Nat := 4983230072969 + 3 ^ 40 * 27388 * 2
def baseEnd_27388 : Nat := 4687736055148026008017

theorem tailTrace_27388 : CollatzResearch.WordTrace tailWord_27388 prefixEnd_27388 4687736055148026008017 := by
  unfold tailWord_27388
  simp only [CollatzResearch.WordTrace]
  refine ⟨499461212392714171557409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 665948283190285562076545 499461212392714171557409)
  ·
    refine ⟨374595909294535628668057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499461212392714171557409 374595909294535628668057)
    ·
      refine ⟨280946931970901721501043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374595909294535628668057 280946931970901721501043)
      ·
        refine ⟨421420397956352582251565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280946931970901721501043 421420397956352582251565)
        ·
          refine ⟨158032649233632218344337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421420397956352582251565 158032649233632218344337)
          ·
            refine ⟨118524486925224163758253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158032649233632218344337 118524486925224163758253)
            ·
              refine ⟨44446682596959061409345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118524486925224163758253 44446682596959061409345)
              ·
                refine ⟨33335011947719296057009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44446682596959061409345 33335011947719296057009)
                ·
                  refine ⟨25001258960789472042757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33335011947719296057009 25001258960789472042757)
                  ·
                    refine ⟨4687736055148026008017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25001258960789472042757 4687736055148026008017)
                    ·
                      rfl

theorem cell23_27388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_27388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27388 prefixEnd_27388 := by exact prefixLift 27388
  have htrace : WordTrace (prefixWord ++ tailWord_27388) baseStart_27388 baseEnd_27388 := by
    simpa [prefixWord, tailWord_27388, baseEnd_27388] using wordTrace_append hprefix tailTrace_27388
  have hstable : (prefixWord ++ tailWord_27388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27388).length < 2 ^ (prefixWord ++ tailWord_27388).sum := by decide
  have hdescent : baseEnd_27388 < baseStart_27388 := by decide
  rcases family_descends (prefixWord ++ tailWord_27388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27415 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_27415 : Nat := 118140960795 + 27415 * 2 ^ 59
def prefixEnd_27415 : Nat := 4983230072969 + 3 ^ 40 * 27415 * 2
def baseEnd_27415 : Nat := 14077072143115472386427

theorem tailTrace_27415 : CollatzResearch.WordTrace tailWord_27415 prefixEnd_27415 14077072143115472386427 := by
  unfold tailWord_27415
  simp only [CollatzResearch.WordTrace]
  refine ⟨999907195687611954347699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 666604797125074636231799 999907195687611954347699)
  ·
    refine ⟨1499860793531417931521549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 999907195687611954347699 1499860793531417931521549)
    ·
      refine ⟨562447797574281724320581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1499860793531417931521549 562447797574281724320581)
      ·
        refine ⟨105458962045177823310109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 562447797574281724320581 105458962045177823310109)
        ·
          refine ⟨39547110766941683741291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105458962045177823310109 39547110766941683741291)
          ·
            refine ⟨59320666150412525611937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39547110766941683741291 59320666150412525611937)
            ·
              refine ⟨44490499612809394208953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59320666150412525611937 44490499612809394208953)
              ·
                refine ⟨33367874709607045656715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44490499612809394208953 33367874709607045656715)
                ·
                  refine ⟨50051812064410568485073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33367874709607045656715 50051812064410568485073)
                  ·
                    refine ⟨37538859048307926363805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50051812064410568485073 37538859048307926363805)
                    ·
                      refine ⟨14077072143115472386427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 37538859048307926363805 14077072143115472386427)
                      ·
                        rfl

theorem cell23_27415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_27415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27415 prefixEnd_27415 := by exact prefixLift 27415
  have htrace : WordTrace (prefixWord ++ tailWord_27415) baseStart_27415 baseEnd_27415 := by
    simpa [prefixWord, tailWord_27415, baseEnd_27415] using wordTrace_append hprefix tailTrace_27415
  have hstable : (prefixWord ++ tailWord_27415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27415).length < 2 ^ (prefixWord ++ tailWord_27415).sum := by decide
  have hdescent : baseEnd_27415 < baseStart_27415 := by decide
  rcases family_descends (prefixWord ++ tailWord_27415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27446 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_27446 : Nat := 118140960795 + 27446 * 2 ^ 59
def prefixEnd_27446 : Nat := 4983230072969 + 3 ^ 40 * 27446 * 2
def baseEnd_27446 : Nat := 14092990043404851098785

theorem tailTrace_27446 : CollatzResearch.WordTrace tailWord_27446 prefixEnd_27446 14092990043404851098785 := by
  unfold tailWord_27446
  simp only [CollatzResearch.WordTrace]
  refine ⟨62564866160956515545387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 667358572383536165817461 62564866160956515545387)
  ·
    refine ⟨93847299241434773318081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62564866160956515545387 93847299241434773318081)
    ·
      refine ⟨70385474431076079988561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93847299241434773318081 70385474431076079988561)
      ·
        refine ⟨52789105823307059991421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70385474431076079988561 52789105823307059991421)
        ·
          refine ⟨19795914683740147496783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52789105823307059991421 19795914683740147496783)
          ·
            refine ⟨29693872025610221245175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19795914683740147496783 29693872025610221245175)
            ·
              refine ⟨44540808038415331867763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29693872025610221245175 44540808038415331867763)
              ·
                refine ⟨66811212057622997801645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44540808038415331867763 66811212057622997801645)
                ·
                  refine ⟨25054204521608624175617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66811212057622997801645 25054204521608624175617)
                  ·
                    refine ⟨18790653391206468131713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25054204521608624175617 18790653391206468131713)
                    ·
                      refine ⟨14092990043404851098785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 18790653391206468131713 14092990043404851098785)
                      ·
                        rfl

theorem cell23_27446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_27446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27446 prefixEnd_27446 := by exact prefixLift 27446
  have htrace : WordTrace (prefixWord ++ tailWord_27446) baseStart_27446 baseEnd_27446 := by
    simpa [prefixWord, tailWord_27446, baseEnd_27446] using wordTrace_append hprefix tailTrace_27446
  have hstable : (prefixWord ++ tailWord_27446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27446).length < 2 ^ (prefixWord ++ tailWord_27446).sum := by decide
  have hdescent : baseEnd_27446 < baseStart_27446 := by decide
  rcases family_descends (prefixWord ++ tailWord_27446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27651 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_27651 : Nat := 118140960795 + 27651 * 2 ^ 59
def prefixEnd_27651 : Nat := 4983230072969 + 3 ^ 40 * 27651 * 2
def baseEnd_27651 : Nat := 14198253577576549035341

theorem tailTrace_27651 : CollatzResearch.WordTrace tailWord_27651 prefixEnd_27651 14198253577576549035341 := by
  unfold tailWord_27651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008514822832624259938807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 672343215221749506625871 1008514822832624259938807)
  ·
    refine ⟨1512772234248936389908211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1008514822832624259938807 1512772234248936389908211)
    ·
      refine ⟨2269158351373404584862317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512772234248936389908211 2269158351373404584862317)
      ·
        refine ⟨850934381765026719323369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2269158351373404584862317 850934381765026719323369)
        ·
          refine ⟨638200786323770039492527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850934381765026719323369 638200786323770039492527)
          ·
            refine ⟨957301179485655059238791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638200786323770039492527 957301179485655059238791)
            ·
              refine ⟨1435951769228482588858187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957301179485655059238791 1435951769228482588858187)
              ·
                refine ⟨2153927653842723883287281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435951769228482588858187 2153927653842723883287281)
                ·
                  refine ⟨1615445740382042912465461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153927653842723883287281 1615445740382042912465461)
                  ·
                    refine ⟨151448038160816523043637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1615445740382042912465461 151448038160816523043637)
                    ·
                      refine ⟨14198253577576549035341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 151448038160816523043637 14198253577576549035341)
                      ·
                        rfl

theorem cell23_27651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_27651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27651 prefixEnd_27651 := by exact prefixLift 27651
  have htrace : WordTrace (prefixWord ++ tailWord_27651) baseStart_27651 baseEnd_27651 := by
    simpa [prefixWord, tailWord_27651, baseEnd_27651] using wordTrace_append hprefix tailTrace_27651
  have hstable : (prefixWord ++ tailWord_27651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27651).length < 2 ^ (prefixWord ++ tailWord_27651).sum := by decide
  have hdescent : baseEnd_27651 < baseStart_27651 := by decide
  rcases family_descends (prefixWord ++ tailWord_27651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27658 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_27658 : Nat := 118140960795 + 27658 * 2 ^ 59
def prefixEnd_27658 : Nat := 4983230072969 + 3 ^ 40 * 27658 * 2
def baseEnd_27658 : Nat := 4733949314052673882603

theorem tailTrace_27658 : CollatzResearch.WordTrace tailWord_27658 prefixEnd_27658 4733949314052673882603 := by
  unfold tailWord_27658
  simp only [CollatzResearch.WordTrace]
  refine ⟨252192533451816113860907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 672513422538176303629085 252192533451816113860907)
  ·
    refine ⟨378288800177724170791361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252192533451816113860907 378288800177724170791361)
    ·
      refine ⟨283716600133293128093521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378288800177724170791361 283716600133293128093521)
      ·
        refine ⟨212787450099969846070141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283716600133293128093521 212787450099969846070141)
        ·
          refine ⟨79795293787488692276303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212787450099969846070141 79795293787488692276303)
          ·
            refine ⟨119692940681233038414455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79795293787488692276303 119692940681233038414455)
            ·
              refine ⟨179539411021849557621683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119692940681233038414455 179539411021849557621683)
              ·
                refine ⟨269309116532774336432525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179539411021849557621683 269309116532774336432525)
                ·
                  refine ⟨100990918699790376162197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269309116532774336432525 100990918699790376162197)
                  ·
                    refine ⟨4733949314052673882603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100990918699790376162197 4733949314052673882603)
                    ·
                      rfl

theorem cell23_27658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_27658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27658 prefixEnd_27658 := by exact prefixLift 27658
  have htrace : WordTrace (prefixWord ++ tailWord_27658) baseStart_27658 baseEnd_27658 := by
    simpa [prefixWord, tailWord_27658, baseEnd_27658] using wordTrace_append hprefix tailTrace_27658
  have hstable : (prefixWord ++ tailWord_27658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27658).length < 2 ^ (prefixWord ++ tailWord_27658).sum := by decide
  have hdescent : baseEnd_27658 < baseStart_27658 := by decide
  rcases family_descends (prefixWord ++ tailWord_27658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27662 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_27662 : Nat := 118140960795 + 27662 * 2 ^ 59
def prefixEnd_27662 : Nat := 4983230072969 + 3 ^ 40 * 27662 * 2
def baseEnd_27662 : Nat := 4734633954925335332597

theorem tailTrace_27662 : CollatzResearch.WordTrace tailWord_27662 prefixEnd_27662 4734633954925335332597 := by
  unfold tailWord_27662
  simp only [CollatzResearch.WordTrace]
  refine ⟨126114503224096642323655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 672610683861848759059493 126114503224096642323655)
  ·
    refine ⟨189171754836144963485483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126114503224096642323655 189171754836144963485483)
    ·
      refine ⟨283757632254217445228225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189171754836144963485483 283757632254217445228225)
      ·
        refine ⟨212818224190663083921169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283757632254217445228225 212818224190663083921169)
        ·
          refine ⟨159613668142997312940877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212818224190663083921169 159613668142997312940877)
          ·
            refine ⟨59855125553623992352829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159613668142997312940877 59855125553623992352829)
            ·
              refine ⟨22445672082608997132311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59855125553623992352829 22445672082608997132311)
              ·
                refine ⟨33668508123913495698467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22445672082608997132311 33668508123913495698467)
                ·
                  refine ⟨50502762185870243547701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33668508123913495698467 50502762185870243547701)
                  ·
                    refine ⟨4734633954925335332597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50502762185870243547701 4734633954925335332597)
                    ·
                      rfl

theorem cell23_27662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_27662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27662 prefixEnd_27662 := by exact prefixLift 27662
  have htrace : WordTrace (prefixWord ++ tailWord_27662) baseStart_27662 baseEnd_27662 := by
    simpa [prefixWord, tailWord_27662, baseEnd_27662] using wordTrace_append hprefix tailTrace_27662
  have hstable : (prefixWord ++ tailWord_27662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27662).length < 2 ^ (prefixWord ++ tailWord_27662).sum := by decide
  have hdescent : baseEnd_27662 < baseStart_27662 := by decide
  rcases family_descends (prefixWord ++ tailWord_27662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27702 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_27702 : Nat := 118140960795 + 27702 * 2 ^ 59
def prefixEnd_27702 : Nat := 4983230072969 + 3 ^ 40 * 27702 * 2
def baseEnd_27702 : Nat := 14224441090955849497607

theorem tailTrace_27702 : CollatzResearch.WordTrace tailWord_27702 prefixEnd_27702 14224441090955849497607 := by
  unfold tailWord_27702
  simp only [CollatzResearch.WordTrace]
  refine ⟨63148434102991248127835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 673583297098573313363573 63148434102991248127835)
  ·
    refine ⟨94722651154486872191753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63148434102991248127835 94722651154486872191753)
    ·
      refine ⟨71041988365865154143815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94722651154486872191753 71041988365865154143815)
      ·
        refine ⟨106562982548797731215723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71041988365865154143815 106562982548797731215723)
        ·
          refine ⟨159844473823196596823585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106562982548797731215723 159844473823196596823585)
          ·
            refine ⟨119883355367397447617689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159844473823196596823585 119883355367397447617689)
            ·
              refine ⟨89912516525548085713267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119883355367397447617689 89912516525548085713267)
              ·
                refine ⟨134868774788322128569901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89912516525548085713267 134868774788322128569901)
                ·
                  refine ⟨50575790545620798213713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134868774788322128569901 50575790545620798213713)
                  ·
                    refine ⟨37931842909215598660285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50575790545620798213713 37931842909215598660285)
                    ·
                      refine ⟨14224441090955849497607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 37931842909215598660285 14224441090955849497607)
                      ·
                        rfl

theorem cell23_27702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_27702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27702 prefixEnd_27702 := by exact prefixLift 27702
  have htrace : WordTrace (prefixWord ++ tailWord_27702) baseStart_27702 baseEnd_27702 := by
    simpa [prefixWord, tailWord_27702, baseEnd_27702] using wordTrace_append hprefix tailTrace_27702
  have hstable : (prefixWord ++ tailWord_27702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27702).length < 2 ^ (prefixWord ++ tailWord_27702).sum := by decide
  have hdescent : baseEnd_27702 < baseStart_27702 := by decide
  rcases family_descends (prefixWord ++ tailWord_27702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27705 : List Nat := [1, 2, 1, 5, 2, 2, 3, 7]
def baseStart_27705 : Nat := 118140960795 + 27705 * 2 ^ 59
def prefixEnd_27705 : Nat := 4983230072969 + 3 ^ 40 * 27705 * 2
def baseEnd_27705 : Nat := 526888204922938435559

theorem tailTrace_27705 : CollatzResearch.WordTrace tailWord_27705 prefixEnd_27705 526888204922938435559 := by
  unfold tailWord_27705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010484364636991482404569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 673656243091327654936379 1010484364636991482404569)
  ·
    refine ⟨757863273477743611803427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1010484364636991482404569 757863273477743611803427)
    ·
      refine ⟨1136794910216615417705141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757863273477743611803427 1136794910216615417705141)
      ·
        refine ⟨106574522832807695409857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1136794910216615417705141 106574522832807695409857)
        ·
          refine ⟨79930892124605771557393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106574522832807695409857 79930892124605771557393)
          ·
            refine ⟨59948169093454328668045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79930892124605771557393 59948169093454328668045)
            ·
              refine ⟨22480563410045373250517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59948169093454328668045 22480563410045373250517)
              ·
                refine ⟨526888204922938435559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22480563410045373250517 526888204922938435559)
                ·
                  rfl

theorem cell23_27705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 7].length) (baseStart_27705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27705 prefixEnd_27705 := by exact prefixLift 27705
  have htrace : WordTrace (prefixWord ++ tailWord_27705) baseStart_27705 baseEnd_27705 := by
    simpa [prefixWord, tailWord_27705, baseEnd_27705] using wordTrace_append hprefix tailTrace_27705
  have hstable : (prefixWord ++ tailWord_27705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27705).length < 2 ^ (prefixWord ++ tailWord_27705).sum := by decide
  have hdescent : baseEnd_27705 < baseStart_27705 := by decide
  rcases family_descends (prefixWord ++ tailWord_27705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27715 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 3]
def baseStart_27715 : Nat := 118140960795 + 27715 * 2 ^ 59
def prefixEnd_27715 : Nat := 4983230072969 + 3 ^ 40 * 27715 * 2
def baseEnd_27715 : Nat := 14231116339464298635047

theorem tailTrace_27715 : CollatzResearch.WordTrace tailWord_27715 prefixEnd_27715 14231116339464298635047 := by
  unfold tailWord_27715
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010849094600763190268599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 673899396400508793512399 1010849094600763190268599)
  ·
    refine ⟨1516273641901144785402899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010849094600763190268599 1516273641901144785402899)
    ·
      refine ⟨2274410462851717178104349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516273641901144785402899 2274410462851717178104349)
      ·
        refine ⟨852903923569393941789131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2274410462851717178104349 852903923569393941789131)
        ·
          refine ⟨1279355885354090912683697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852903923569393941789131 1279355885354090912683697)
          ·
            refine ⟨959516914015568184512773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279355885354090912683697 959516914015568184512773)
            ·
              refine ⟨179909421377919034596145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 959516914015568184512773 179909421377919034596145)
              ·
                refine ⟨134932066033439275947109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179909421377919034596145 134932066033439275947109)
                ·
                  refine ⟨25299762381269864240083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134932066033439275947109 25299762381269864240083)
                  ·
                    refine ⟨37949643571904796360125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25299762381269864240083 37949643571904796360125)
                    ·
                      refine ⟨14231116339464298635047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 37949643571904796360125 14231116339464298635047)
                      ·
                        rfl

theorem cell23_27715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_27715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27715 prefixEnd_27715 := by exact prefixLift 27715
  have htrace : WordTrace (prefixWord ++ tailWord_27715) baseStart_27715 baseEnd_27715 := by
    simpa [prefixWord, tailWord_27715, baseEnd_27715] using wordTrace_append hprefix tailTrace_27715
  have hstable : (prefixWord ++ tailWord_27715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27715).length < 2 ^ (prefixWord ++ tailWord_27715).sum := by decide
  have hdescent : baseEnd_27715 < baseStart_27715 := by decide
  rcases family_descends (prefixWord ++ tailWord_27715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27719 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_27719 : Nat := 118140960795 + 27719 * 2 ^ 59
def prefixEnd_27719 : Nat := 4983230072969 + 3 ^ 40 * 27719 * 2
def baseEnd_27719 : Nat := 14233170262082282985029

theorem tailTrace_27719 : CollatzResearch.WordTrace tailWord_27719 prefixEnd_27719 14233170262082282985029 := by
  unfold tailWord_27719
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010994986586271873414211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 673996657724181248942807 1010994986586271873414211)
  ·
    refine ⟨1516492479879407810121317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010994986586271873414211 1516492479879407810121317)
    ·
      refine ⟨284342339977388964397747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1516492479879407810121317 284342339977388964397747)
      ·
        refine ⟨426513509966083446596621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284342339977388964397747 426513509966083446596621)
        ·
          refine ⟨159942566237281292473733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426513509966083446596621 159942566237281292473733)
          ·
            refine ⟨29989231169490242338825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159942566237281292473733 29989231169490242338825)
            ·
              refine ⟨22491923377117681754119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29989231169490242338825 22491923377117681754119)
              ·
                refine ⟨33737885065676522631179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22491923377117681754119 33737885065676522631179)
                ·
                  refine ⟨50606827598514783946769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33737885065676522631179 50606827598514783946769)
                  ·
                    refine ⟨37955120698886087960077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50606827598514783946769 37955120698886087960077)
                    ·
                      refine ⟨14233170262082282985029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 37955120698886087960077 14233170262082282985029)
                      ·
                        rfl

theorem cell23_27719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_27719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27719 prefixEnd_27719 := by exact prefixLift 27719
  have htrace : WordTrace (prefixWord ++ tailWord_27719) baseStart_27719 baseEnd_27719 := by
    simpa [prefixWord, tailWord_27719, baseEnd_27719] using wordTrace_append hprefix tailTrace_27719
  have hstable : (prefixWord ++ tailWord_27719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27719).length < 2 ^ (prefixWord ++ tailWord_27719).sum := by decide
  have hdescent : baseEnd_27719 < baseStart_27719 := by decide
  rcases family_descends (prefixWord ++ tailWord_27719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27738 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_27738 : Nat := 118140960795 + 27738 * 2 ^ 59
def prefixEnd_27738 : Nat := 4983230072969 + 3 ^ 40 * 27738 * 2
def baseEnd_27738 : Nat := 14242926394517708647441

theorem tailTrace_27738 : CollatzResearch.WordTrace tailWord_27738 prefixEnd_27738 14242926394517708647441 := by
  unfold tailWord_27738
  simp only [CollatzResearch.WordTrace]
  refine ⟨252921993379359529588967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 674458649011625412237245 252921993379359529588967)
  ·
    refine ⟨379382990069039294383451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252921993379359529588967 379382990069039294383451)
    ·
      refine ⟨569074485103558941575177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379382990069039294383451 569074485103558941575177)
      ·
        refine ⟨426805863827669206181383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569074485103558941575177 426805863827669206181383)
        ·
          refine ⟨640208795741503809272075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426805863827669206181383 640208795741503809272075)
          ·
            refine ⟨960313193612255713908113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640208795741503809272075 960313193612255713908113)
            ·
              refine ⟨720234895209191785431085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960313193612255713908113 720234895209191785431085)
              ·
                refine ⟨270088085703446919536657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 720234895209191785431085 270088085703446919536657)
                ·
                  refine ⟨202566064277585189652493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270088085703446919536657 202566064277585189652493)
                  ·
                    refine ⟨75962274104094446119685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202566064277585189652493 75962274104094446119685)
                    ·
                      refine ⟨14242926394517708647441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 75962274104094446119685 14242926394517708647441)
                      ·
                        rfl

theorem cell23_27738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_27738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27738 prefixEnd_27738 := by exact prefixLift 27738
  have htrace : WordTrace (prefixWord ++ tailWord_27738) baseStart_27738 baseEnd_27738 := by
    simpa [prefixWord, tailWord_27738, baseEnd_27738] using wordTrace_append hprefix tailTrace_27738
  have hstable : (prefixWord ++ tailWord_27738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27738).length < 2 ^ (prefixWord ++ tailWord_27738).sum := by decide
  have hdescent : baseEnd_27738 < baseStart_27738 := by decide
  rcases family_descends (prefixWord ++ tailWord_27738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27749 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 2, 1, 3]
def baseStart_27749 : Nat := 118140960795 + 27749 * 2 ^ 59
def prefixEnd_27749 : Nat := 4983230072969 + 3 ^ 40 * 27749 * 2
def baseEnd_27749 : Nat := 14248574681717165609891

theorem tailTrace_27749 : CollatzResearch.WordTrace tailWord_27749 prefixEnd_27749 14248574681717165609891 := by
  unfold tailWord_27749
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012089176477586997006301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 674726117651724664670867 1012089176477586997006301)
  ·
    refine ⟨379533441179095123877363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1012089176477586997006301 379533441179095123877363)
    ·
      refine ⟨569300161768642685816045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379533441179095123877363 569300161768642685816045)
      ·
        refine ⟨213487560663241007181017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569300161768642685816045 213487560663241007181017)
        ·
          refine ⟨160115670497430755385763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213487560663241007181017 160115670497430755385763)
          ·
            refine ⟨240173505746146133078645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160115670497430755385763 240173505746146133078645)
            ·
              refine ⟨22516266163701199976123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240173505746146133078645 22516266163701199976123)
              ·
                refine ⟨33774399245551799964185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22516266163701199976123 33774399245551799964185)
                ·
                  refine ⟨25330799434163849973139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33774399245551799964185 25330799434163849973139)
                  ·
                    refine ⟨37996199151245774959709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25330799434163849973139 37996199151245774959709)
                    ·
                      refine ⟨14248574681717165609891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 37996199151245774959709 14248574681717165609891)
                      ·
                        rfl

theorem cell23_27749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_27749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27749 prefixEnd_27749 := by exact prefixLift 27749
  have htrace : WordTrace (prefixWord ++ tailWord_27749) baseStart_27749 baseEnd_27749 := by
    simpa [prefixWord, tailWord_27749, baseEnd_27749] using wordTrace_append hprefix tailTrace_27749
  have hstable : (prefixWord ++ tailWord_27749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27749).length < 2 ^ (prefixWord ++ tailWord_27749).sum := by decide
  have hdescent : baseEnd_27749 < baseStart_27749 := by decide
  rcases family_descends (prefixWord ++ tailWord_27749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27768 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_27768 : Nat := 118140960795 + 27768 * 2 ^ 59
def prefixEnd_27768 : Nat := 4983230072969 + 3 ^ 40 * 27768 * 2
def baseEnd_27768 : Nat := 14258330814152591272303

theorem tailTrace_27768 : CollatzResearch.WordTrace tailWord_27768 prefixEnd_27768 14258330814152591272303 := by
  unfold tailWord_27768
  simp only [CollatzResearch.WordTrace]
  refine ⟨506391081704376620973979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 675188108939168827965305 506391081704376620973979)
  ·
    refine ⟨759586622556564931460969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506391081704376620973979 759586622556564931460969)
    ·
      refine ⟨569689966917423698595727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759586622556564931460969 569689966917423698595727)
      ·
        refine ⟨854534950376135547893591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569689966917423698595727 854534950376135547893591)
        ·
          refine ⟨1281802425564203321840387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854534950376135547893591 1281802425564203321840387)
          ·
            refine ⟨1922703638346304982760581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281802425564203321840387 1922703638346304982760581)
            ·
              refine ⟨360506932189932184267609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1922703638346304982760581 360506932189932184267609)
              ·
                refine ⟨270380199142449138200707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360506932189932184267609 270380199142449138200707)
                ·
                  refine ⟨405570298713673707301061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270380199142449138200707 405570298713673707301061)
                  ·
                    refine ⟨76044431008813820118949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405570298713673707301061 76044431008813820118949)
                    ·
                      refine ⟨14258330814152591272303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 76044431008813820118949 14258330814152591272303)
                      ·
                        rfl

theorem cell23_27768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_27768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27768 prefixEnd_27768 := by exact prefixLift 27768
  have htrace : WordTrace (prefixWord ++ tailWord_27768) baseStart_27768 baseEnd_27768 := by
    simpa [prefixWord, tailWord_27768, baseEnd_27768] using wordTrace_append hprefix tailTrace_27768
  have hstable : (prefixWord ++ tailWord_27768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27768).length < 2 ^ (prefixWord ++ tailWord_27768).sum := by decide
  have hdescent : baseEnd_27768 < baseStart_27768 := by decide
  rcases family_descends (prefixWord ++ tailWord_27768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27772 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_27772 : Nat := 118140960795 + 27772 * 2 ^ 59
def prefixEnd_27772 : Nat := 4983230072969 + 3 ^ 40 * 27772 * 2
def baseEnd_27772 : Nat := 14260384736770575622285

theorem tailTrace_27772 : CollatzResearch.WordTrace tailWord_27772 prefixEnd_27772 14260384736770575622285 := by
  unfold tailWord_27772
  simp only [CollatzResearch.WordTrace]
  refine ⟨506464027697130962546785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 675285370262841283395713 506464027697130962546785)
  ·
    refine ⟨379848020772848221910089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 506464027697130962546785 379848020772848221910089)
    ·
      refine ⟨284886015579636166432567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379848020772848221910089 284886015579636166432567)
      ·
        refine ⟨427329023369454249648851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284886015579636166432567 427329023369454249648851)
        ·
          refine ⟨640993535054181374473277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427329023369454249648851 640993535054181374473277)
          ·
            refine ⟨240372575645318015427479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640993535054181374473277 240372575645318015427479)
            ·
              refine ⟨360558863467977023141219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240372575645318015427479 360558863467977023141219)
              ·
                refine ⟨540838295201965534711829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360558863467977023141219 540838295201965534711829)
                ·
                  refine ⟨25351795087592134439617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 540838295201965534711829 25351795087592134439617)
                  ·
                    refine ⟨19013846315694100829713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25351795087592134439617 19013846315694100829713)
                    ·
                      refine ⟨14260384736770575622285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19013846315694100829713 14260384736770575622285)
                      ·
                        rfl

theorem cell23_27772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_27772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27772 prefixEnd_27772 := by exact prefixLift 27772
  have htrace : WordTrace (prefixWord ++ tailWord_27772) baseStart_27772 baseEnd_27772 := by
    simpa [prefixWord, tailWord_27772, baseEnd_27772] using wordTrace_append hprefix tailTrace_27772
  have hstable : (prefixWord ++ tailWord_27772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27772).length < 2 ^ (prefixWord ++ tailWord_27772).sum := by decide
  have hdescent : baseEnd_27772 < baseStart_27772 := by decide
  rcases family_descends (prefixWord ++ tailWord_27772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27795 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 5]
def baseStart_27795 : Nat := 118140960795 + 27795 * 2 ^ 59
def prefixEnd_27795 : Nat := 4983230072969 + 3 ^ 40 * 27795 * 2
def baseEnd_27795 : Nat := 1585799421313776181631

theorem tailTrace_27795 : CollatzResearch.WordTrace tailWord_27795 prefixEnd_27795 1585799421313776181631 := by
  unfold tailWord_27795
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013766934310936853180839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 675844622873957902120559 1013766934310936853180839)
  ·
    refine ⟨1520650401466405279771259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1013766934310936853180839 1520650401466405279771259)
    ·
      refine ⟨2280975602199607919656889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520650401466405279771259 2280975602199607919656889)
      ·
        refine ⟨1710731701649705939742667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2280975602199607919656889 1710731701649705939742667)
        ·
          refine ⟨2566097552474558909614001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710731701649705939742667 2566097552474558909614001)
          ·
            refine ⟨1924573164355919182210501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566097552474558909614001 1924573164355919182210501)
            ·
              refine ⟨360857468316734846664469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1924573164355919182210501 360857468316734846664469)
              ·
                refine ⟨16915193827346945937397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 360857468316734846664469 16915193827346945937397)
                ·
                  refine ⟨1585799421313776181631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16915193827346945937397 1585799421313776181631)
                  ·
                    rfl

theorem cell23_27795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 5].length) (baseStart_27795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27795 prefixEnd_27795 := by exact prefixLift 27795
  have htrace : WordTrace (prefixWord ++ tailWord_27795) baseStart_27795 baseEnd_27795 := by
    simpa [prefixWord, tailWord_27795, baseEnd_27795] using wordTrace_append hprefix tailTrace_27795
  have hstable : (prefixWord ++ tailWord_27795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27795).length < 2 ^ (prefixWord ++ tailWord_27795).sum := by decide
  have hdescent : baseEnd_27795 < baseStart_27795 := by decide
  rcases family_descends (prefixWord ++ tailWord_27795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27805 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_27805 : Nat := 118140960795 + 27805 * 2 ^ 59
def prefixEnd_27805 : Nat := 4983230072969 + 3 ^ 40 * 27805 * 2
def baseEnd_27805 : Nat := 14277329598368946509633

theorem tailTrace_27805 : CollatzResearch.WordTrace tailWord_27805 prefixEnd_27805 14277329598368946509633 := by
  unfold tailWord_27805
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014131664274708561044869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 676087776183139040696579 1014131664274708561044869)
  ·
    refine ⟨190149687051507855195913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1014131664274708561044869 190149687051507855195913)
    ·
      refine ⟨142612265288630891396935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190149687051507855195913 142612265288630891396935)
      ·
        refine ⟨213918397932946337095403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142612265288630891396935 213918397932946337095403)
        ·
          refine ⟨320877596899419505643105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213918397932946337095403 320877596899419505643105)
          ·
            refine ⟨240658197674564629232329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320877596899419505643105 240658197674564629232329)
            ·
              refine ⟨180493648255923471924247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240658197674564629232329 180493648255923471924247)
              ·
                refine ⟨270740472383885207886371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180493648255923471924247 270740472383885207886371)
                ·
                  refine ⟨406110708575827811829557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270740472383885207886371 406110708575827811829557)
                  ·
                    refine ⟨38072878928983857359021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 406110708575827811829557 38072878928983857359021)
                    ·
                      refine ⟨14277329598368946509633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38072878928983857359021 14277329598368946509633)
                      ·
                        rfl

theorem cell23_27805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_27805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27805 prefixEnd_27805 := by exact prefixLift 27805
  have htrace : WordTrace (prefixWord ++ tailWord_27805) baseStart_27805 baseEnd_27805 := by
    simpa [prefixWord, tailWord_27805, baseEnd_27805] using wordTrace_append hprefix tailTrace_27805
  have hstable : (prefixWord ++ tailWord_27805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27805).length < 2 ^ (prefixWord ++ tailWord_27805).sum := by decide
  have hdescent : baseEnd_27805 < baseStart_27805 := by decide
  rcases family_descends (prefixWord ++ tailWord_27805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27865 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_27865 : Nat := 118140960795 + 27865 * 2 ^ 59
def prefixEnd_27865 : Nat := 4983230072969 + 3 ^ 40 * 27865 * 2
def baseEnd_27865 : Nat := 14308138437638711759357

theorem tailTrace_27865 : CollatzResearch.WordTrace tailWord_27865 prefixEnd_27865 14308138437638711759357 := by
  unfold tailWord_27865
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016320044057338808229049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 677546696038225872152699 1016320044057338808229049)
  ·
    refine ⟨762240033043004106171787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016320044057338808229049 762240033043004106171787)
    ·
      refine ⟨1143360049564506159257681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762240033043004106171787 1143360049564506159257681)
      ·
        refine ⟨857520037173379619443261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143360049564506159257681 857520037173379619443261)
        ·
          refine ⟨321570013940017357291223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 857520037173379619443261 321570013940017357291223)
          ·
            refine ⟨482355020910026035936835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321570013940017357291223 482355020910026035936835)
            ·
              refine ⟨723532531365039053905253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482355020910026035936835 723532531365039053905253)
              ·
                refine ⟨135662349630944822607235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723532531365039053905253 135662349630944822607235)
                ·
                  refine ⟨203493524446417233910853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135662349630944822607235 203493524446417233910853)
                  ·
                    refine ⟨38155035833703231358285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203493524446417233910853 38155035833703231358285)
                    ·
                      refine ⟨14308138437638711759357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38155035833703231358285 14308138437638711759357)
                      ·
                        rfl

theorem cell23_27865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_27865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27865 prefixEnd_27865 := by exact prefixLift 27865
  have htrace : WordTrace (prefixWord ++ tailWord_27865) baseStart_27865 baseEnd_27865 := by
    simpa [prefixWord, tailWord_27865, baseEnd_27865] using wordTrace_append hprefix tailTrace_27865
  have hstable : (prefixWord ++ tailWord_27865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27865).length < 2 ^ (prefixWord ++ tailWord_27865).sum := by decide
  have hdescent : baseEnd_27865 < baseStart_27865 := by decide
  rcases family_descends (prefixWord ++ tailWord_27865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27872 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 3, 4]
def baseStart_27872 : Nat := 118140960795 + 27872 * 2 ^ 59
def prefixEnd_27872 : Nat := 4983230072969 + 3 ^ 40 * 27872 * 2
def baseEnd_27872 : Nat := 4770577600740061457275

theorem tailTrace_27872 : CollatzResearch.WordTrace tailWord_27872 prefixEnd_27872 4770577600740061457275 := by
  unfold tailWord_27872
  simp only [CollatzResearch.WordTrace]
  refine ⟨508287677515989501866935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 677716903354652669155913 508287677515989501866935)
  ·
    refine ⟨762431516273984252800403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508287677515989501866935 762431516273984252800403)
    ·
      refine ⟨1143647274410976379200605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762431516273984252800403 1143647274410976379200605)
      ·
        refine ⟨428867727904116142200227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1143647274410976379200605 428867727904116142200227)
        ·
          refine ⟨643301591856174213300341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428867727904116142200227 643301591856174213300341)
          ·
            refine ⟨60309524236516332496907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 643301591856174213300341 60309524236516332496907)
            ·
              refine ⟨90464286354774498745361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60309524236516332496907 90464286354774498745361)
              ·
                refine ⟨67848214766080874059021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90464286354774498745361 67848214766080874059021)
                ·
                  refine ⟨25443080537280327772133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67848214766080874059021 25443080537280327772133)
                  ·
                    refine ⟨4770577600740061457275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25443080537280327772133 4770577600740061457275)
                    ·
                      rfl

theorem cell23_27872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_27872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27872 prefixEnd_27872 := by exact prefixLift 27872
  have htrace : WordTrace (prefixWord ++ tailWord_27872) baseStart_27872 baseEnd_27872 := by
    simpa [prefixWord, tailWord_27872, baseEnd_27872] using wordTrace_append hprefix tailTrace_27872
  have hstable : (prefixWord ++ tailWord_27872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27872).length < 2 ^ (prefixWord ++ tailWord_27872).sum := by decide
  have hdescent : baseEnd_27872 < baseStart_27872 := by decide
  rcases family_descends (prefixWord ++ tailWord_27872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27882 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_27882 : Nat := 118140960795 + 27882 * 2 ^ 59
def prefixEnd_27882 : Nat := 4983230072969 + 3 ^ 40 * 27882 * 2
def baseEnd_27882 : Nat := 14316867608765145246779

theorem tailTrace_27882 : CollatzResearch.WordTrace tailWord_27882 prefixEnd_27882 14316867608765145246779 := by
  unfold tailWord_27882
  simp only [CollatzResearch.WordTrace]
  refine ⟨254235021248937677899475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 677960056663833807731933 254235021248937677899475)
  ·
    refine ⟨381352531873406516849213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254235021248937677899475 381352531873406516849213)
    ·
      refine ⟨143007199452527443818455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381352531873406516849213 143007199452527443818455)
      ·
        refine ⟨214510799178791165727683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143007199452527443818455 214510799178791165727683)
        ·
          refine ⟨321766198768186748591525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214510799178791165727683 321766198768186748591525)
          ·
            refine ⟨60331162269035015360911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321766198768186748591525 60331162269035015360911)
            ·
              refine ⟨90496743403552523041367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60331162269035015360911 90496743403552523041367)
              ·
                refine ⟨135745115105328784562051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90496743403552523041367 135745115105328784562051)
                ·
                  refine ⟨203617672657993176843077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135745115105328784562051 203617672657993176843077)
                  ·
                    refine ⟨38178313623373720658077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203617672657993176843077 38178313623373720658077)
                    ·
                      refine ⟨14316867608765145246779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38178313623373720658077 14316867608765145246779)
                      ·
                        rfl

theorem cell23_27882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_27882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27882 prefixEnd_27882 := by exact prefixLift 27882
  have htrace : WordTrace (prefixWord ++ tailWord_27882) baseStart_27882 baseEnd_27882 := by
    simpa [prefixWord, tailWord_27882, baseEnd_27882] using wordTrace_append hprefix tailTrace_27882
  have hstable : (prefixWord ++ tailWord_27882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27882).length < 2 ^ (prefixWord ++ tailWord_27882).sum := by decide
  have hdescent : baseEnd_27882 < baseStart_27882 := by decide
  rcases family_descends (prefixWord ++ tailWord_27882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27902 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_27902 : Nat := 118140960795 + 27902 * 2 ^ 59
def prefixEnd_27902 : Nat := 4983230072969 + 3 ^ 40 * 27902 * 2
def baseEnd_27902 : Nat := 1591904135761674110743

theorem tailTrace_27902 : CollatzResearch.WordTrace tailWord_27902 prefixEnd_27902 1591904135761674110743 := by
  unfold tailWord_27902
  simp only [CollatzResearch.WordTrace]
  refine ⟨127208693115411765915745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 678446363282196084883973 127208693115411765915745)
  ·
    refine ⟨95406519836558824436809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127208693115411765915745 95406519836558824436809)
    ·
      refine ⟨71554889877419118327607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95406519836558824436809 71554889877419118327607)
      ·
        refine ⟨107332334816128677491411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71554889877419118327607 107332334816128677491411)
        ·
          refine ⟨160998502224193016237117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107332334816128677491411 160998502224193016237117)
          ·
            refine ⟨60374438334072381088919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160998502224193016237117 60374438334072381088919)
            ·
              refine ⟨90561657501108571633379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60374438334072381088919 90561657501108571633379)
              ·
                refine ⟨135842486251662857450069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90561657501108571633379 135842486251662857450069)
                ·
                  refine ⟨1591904135761674110743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 135842486251662857450069 1591904135761674110743)
                  ·
                    rfl

theorem cell23_27902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_27902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27902 prefixEnd_27902 := by exact prefixLift 27902
  have htrace : WordTrace (prefixWord ++ tailWord_27902) baseStart_27902 baseEnd_27902 := by
    simpa [prefixWord, tailWord_27902, baseEnd_27902] using wordTrace_append hprefix tailTrace_27902
  have hstable : (prefixWord ++ tailWord_27902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27902).length < 2 ^ (prefixWord ++ tailWord_27902).sum := by decide
  have hdescent : baseEnd_27902 < baseStart_27902 := by decide
  rcases family_descends (prefixWord ++ tailWord_27902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27905 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_27905 : Nat := 118140960795 + 27905 * 2 ^ 59
def prefixEnd_27905 : Nat := 4983230072969 + 3 ^ 40 * 27905 * 2
def baseEnd_27905 : Nat := 14328677663818555259173

theorem tailTrace_27905 : CollatzResearch.WordTrace tailWord_27905 prefixEnd_27905 14328677663818555259173 := by
  unfold tailWord_27905
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017778963912425639685169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 678519309274950426456779 1017778963912425639685169)
  ·
    refine ⟨763334222934319229763877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1017778963912425639685169 763334222934319229763877)
    ·
      refine ⟨143125166800184855580727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 763334222934319229763877 143125166800184855580727)
      ·
        refine ⟨214687750200277283371091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143125166800184855580727 214687750200277283371091)
        ·
          refine ⟨322031625300415925056637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214687750200277283371091 322031625300415925056637)
          ·
            refine ⟨120761859487655971896239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322031625300415925056637 120761859487655971896239)
            ·
              refine ⟨181142789231483957844359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120761859487655971896239 181142789231483957844359)
              ·
                refine ⟨271714183847225936766539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181142789231483957844359 271714183847225936766539)
                ·
                  refine ⟨407571275770838905149809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271714183847225936766539 407571275770838905149809)
                  ·
                    refine ⟨305678456828129178862357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407571275770838905149809 305678456828129178862357)
                    ·
                      refine ⟨14328677663818555259173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 305678456828129178862357 14328677663818555259173)
                      ·
                        rfl

theorem cell23_27905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_27905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27905 prefixEnd_27905 := by exact prefixLift 27905
  have htrace : WordTrace (prefixWord ++ tailWord_27905) baseStart_27905 baseEnd_27905 := by
    simpa [prefixWord, tailWord_27905, baseEnd_27905] using wordTrace_append hprefix tailTrace_27905
  have hstable : (prefixWord ++ tailWord_27905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27905).length < 2 ^ (prefixWord ++ tailWord_27905).sum := by decide
  have hdescent : baseEnd_27905 < baseStart_27905 := by decide
  rcases family_descends (prefixWord ++ tailWord_27905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27906 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_27906 : Nat := 118140960795 + 27906 * 2 ^ 59
def prefixEnd_27906 : Nat := 4983230072969 + 3 ^ 40 * 27906 * 2
def baseEnd_27906 : Nat := 4776397048157683782223

theorem tailTrace_27906 : CollatzResearch.WordTrace tailWord_27906 prefixEnd_27906 4776397048157683782223 := by
  unfold tailWord_27906
  simp only [CollatzResearch.WordTrace]
  refine ⟨254453859227200702617893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 678543624605868540314381 254453859227200702617893)
  ·
    refine ⟨47710098605100131740855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254453859227200702617893 47710098605100131740855)
    ·
      refine ⟨71565147907650197611283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47710098605100131740855 71565147907650197611283)
      ·
        refine ⟨107347721861475296416925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71565147907650197611283 107347721861475296416925)
        ·
          refine ⟨40255395698053236156347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107347721861475296416925 40255395698053236156347)
          ·
            refine ⟨60383093547079854234521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40255395698053236156347 60383093547079854234521)
            ·
              refine ⟨45287320160309890675891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60383093547079854234521 45287320160309890675891)
              ·
                refine ⟨67930980240464836013837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45287320160309890675891 67930980240464836013837)
                ·
                  refine ⟨25474117590174313505189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67930980240464836013837 25474117590174313505189)
                  ·
                    refine ⟨4776397048157683782223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25474117590174313505189 4776397048157683782223)
                    ·
                      rfl

theorem cell23_27906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_27906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27906 prefixEnd_27906 := by exact prefixLift 27906
  have htrace : WordTrace (prefixWord ++ tailWord_27906) baseStart_27906 baseEnd_27906 := by
    simpa [prefixWord, tailWord_27906, baseEnd_27906] using wordTrace_append hprefix tailTrace_27906
  have hstable : (prefixWord ++ tailWord_27906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27906).length < 2 ^ (prefixWord ++ tailWord_27906).sum := by decide
  have hdescent : baseEnd_27906 < baseStart_27906 := by decide
  rcases family_descends (prefixWord ++ tailWord_27906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27932 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_27932 : Nat := 118140960795 + 27932 * 2 ^ 59
def prefixEnd_27932 : Nat := 4983230072969 + 3 ^ 40 * 27932 * 2
def baseEnd_27932 : Nat := 4780847213829983207183

theorem tailTrace_27932 : CollatzResearch.WordTrace tailWord_27932 prefixEnd_27932 4780847213829983207183 := by
  unfold tailWord_27932
  simp only [CollatzResearch.WordTrace]
  refine ⟨509381867407304625459025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 679175823209739500612033 509381867407304625459025)
  ·
    refine ⟨382036400555478469094269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 509381867407304625459025 382036400555478469094269)
    ·
      refine ⟨143263650208304425910351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382036400555478469094269 143263650208304425910351)
      ·
        refine ⟨214895475312456638865527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143263650208304425910351 214895475312456638865527)
        ·
          refine ⟨322343212968684958298291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214895475312456638865527 322343212968684958298291)
          ·
            refine ⟨483514819453027437447437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322343212968684958298291 483514819453027437447437)
            ·
              refine ⟨181318057294885289042789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483514819453027437447437 181318057294885289042789)
              ·
                refine ⟨33997135742790991695523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181318057294885289042789 33997135742790991695523)
                ·
                  refine ⟨50995703614186487543285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33997135742790991695523 50995703614186487543285)
                  ·
                    refine ⟨4780847213829983207183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50995703614186487543285 4780847213829983207183)
                    ·
                      rfl

theorem cell23_27932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_27932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27932 prefixEnd_27932 := by exact prefixLift 27932
  have htrace : WordTrace (prefixWord ++ tailWord_27932) baseStart_27932 baseEnd_27932 := by
    simpa [prefixWord, tailWord_27932, baseEnd_27932] using wordTrace_append hprefix tailTrace_27932
  have hstable : (prefixWord ++ tailWord_27932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27932).length < 2 ^ (prefixWord ++ tailWord_27932).sum := by decide
  have hdescent : baseEnd_27932 < baseStart_27932 := by decide
  rcases family_descends (prefixWord ++ tailWord_27932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27952 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4]
def baseStart_27952 : Nat := 118140960795 + 27952 * 2 ^ 59
def prefixEnd_27952 : Nat := 4983230072969 + 3 ^ 40 * 27952 * 2
def baseEnd_27952 : Nat := 14352811254579871371457

theorem tailTrace_27952 : CollatzResearch.WordTrace tailWord_27952 prefixEnd_27952 14352811254579871371457 := by
  unfold tailWord_27952
  simp only [CollatzResearch.WordTrace]
  refine ⟨509746597371076333323055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 679662129828101777764073 509746597371076333323055)
  ·
    refine ⟨764619896056614499984583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 509746597371076333323055 764619896056614499984583)
    ·
      refine ⟨1146929844084921749976875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764619896056614499984583 1146929844084921749976875)
      ·
        refine ⟨1720394766127382624965313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146929844084921749976875 1720394766127382624965313)
        ·
          refine ⟨1290296074595536968723985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1720394766127382624965313 1290296074595536968723985)
          ·
            refine ⟨967722055946652726542989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290296074595536968723985 967722055946652726542989)
            ·
              refine ⟨362895770979994772453621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967722055946652726542989 362895770979994772453621)
              ·
                refine ⟨34021478529374509917527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362895770979994772453621 34021478529374509917527)
                ·
                  refine ⟨51032217794061764876291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34021478529374509917527 51032217794061764876291)
                  ·
                    refine ⟨76548326691092647314437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51032217794061764876291 76548326691092647314437)
                    ·
                      refine ⟨14352811254579871371457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 76548326691092647314437 14352811254579871371457)
                      ·
                        rfl

theorem cell23_27952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_27952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27952 prefixEnd_27952 := by exact prefixLift 27952
  have htrace : WordTrace (prefixWord ++ tailWord_27952) baseStart_27952 baseEnd_27952 := by
    simpa [prefixWord, tailWord_27952, baseEnd_27952] using wordTrace_append hprefix tailTrace_27952
  have hstable : (prefixWord ++ tailWord_27952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27952).length < 2 ^ (prefixWord ++ tailWord_27952).sum := by decide
  have hdescent : baseEnd_27952 < baseStart_27952 := by decide
  rcases family_descends (prefixWord ++ tailWord_27952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27956 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_27956 : Nat := 118140960795 + 27956 * 2 ^ 59
def prefixEnd_27956 : Nat := 4983230072969 + 3 ^ 40 * 27956 * 2
def baseEnd_27956 : Nat := 14354865177197855721439

theorem tailTrace_27956 : CollatzResearch.WordTrace tailWord_27956 prefixEnd_27956 14354865177197855721439 := by
  unfold tailWord_27956
  simp only [CollatzResearch.WordTrace]
  refine ⟨509819543363830674895861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 679759391151774233194481 509819543363830674895861)
  ·
    refine ⟨47795582190359125771487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 509819543363830674895861 47795582190359125771487)
    ·
      refine ⟨71693373285538688657231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47795582190359125771487 71693373285538688657231)
      ·
        refine ⟨107540059928308032985847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71693373285538688657231 107540059928308032985847)
        ·
          refine ⟨161310089892462049478771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107540059928308032985847 161310089892462049478771)
          ·
            refine ⟨241965134838693074218157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161310089892462049478771 241965134838693074218157)
            ·
              refine ⟨90736925564509902831809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241965134838693074218157 90736925564509902831809)
              ·
                refine ⟨68052694173382427123857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90736925564509902831809 68052694173382427123857)
                ·
                  refine ⟨51039520630036820342893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68052694173382427123857 51039520630036820342893)
                  ·
                    refine ⟨19139820236263807628585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51039520630036820342893 19139820236263807628585)
                    ·
                      refine ⟨14354865177197855721439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19139820236263807628585 14354865177197855721439)
                      ·
                        rfl

theorem cell23_27956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_27956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27956 prefixEnd_27956 := by exact prefixLift 27956
  have htrace : WordTrace (prefixWord ++ tailWord_27956) baseStart_27956 baseEnd_27956 := by
    simpa [prefixWord, tailWord_27956, baseEnd_27956] using wordTrace_append hprefix tailTrace_27956
  have hstable : (prefixWord ++ tailWord_27956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27956).length < 2 ^ (prefixWord ++ tailWord_27956).sum := by decide
  have hdescent : baseEnd_27956 < baseStart_27956 := by decide
  rcases family_descends (prefixWord ++ tailWord_27956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27962 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_27962 : Nat := 118140960795 + 27962 * 2 ^ 59
def prefixEnd_27962 : Nat := 4983230072969 + 3 ^ 40 * 27962 * 2
def baseEnd_27962 : Nat := 4785982020374944082137

theorem tailTrace_27962 : CollatzResearch.WordTrace tailWord_27962 prefixEnd_27962 4785982020374944082137 := by
  unfold tailWord_27962
  simp only [CollatzResearch.WordTrace]
  refine ⟨254964481176481093627535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 679905283137282916340093 254964481176481093627535)
  ·
    refine ⟨382446721764721640441303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254964481176481093627535 382446721764721640441303)
    ·
      refine ⟨573670082647082460661955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382446721764721640441303 573670082647082460661955)
      ·
        refine ⟨860505123970623690992933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573670082647082460661955 860505123970623690992933)
        ·
          refine ⟨161344710744491942061175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 860505123970623690992933 161344710744491942061175)
          ·
            refine ⟨242017066116737913091763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161344710744491942061175 242017066116737913091763)
            ·
              refine ⟨363025599175106869637645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242017066116737913091763 363025599175106869637645)
              ·
                refine ⟨136134599690665076114117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363025599175106869637645 136134599690665076114117)
                ·
                  refine ⟨25525237441999701771397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136134599690665076114117 25525237441999701771397)
                  ·
                    refine ⟨4785982020374944082137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25525237441999701771397 4785982020374944082137)
                    ·
                      rfl

theorem cell23_27962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_27962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27962 prefixEnd_27962 := by exact prefixLift 27962
  have htrace : WordTrace (prefixWord ++ tailWord_27962) baseStart_27962 baseEnd_27962 := by
    simpa [prefixWord, tailWord_27962, baseEnd_27962] using wordTrace_append hprefix tailTrace_27962
  have hstable : (prefixWord ++ tailWord_27962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27962).length < 2 ^ (prefixWord ++ tailWord_27962).sum := by decide
  have hdescent : baseEnd_27962 < baseStart_27962 := by decide
  rcases family_descends (prefixWord ++ tailWord_27962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27975 : List Nat := [1, 1, 4, 1, 2, 3, 1, 10]
def baseStart_27975 : Nat := 118140960795 + 27975 * 2 ^ 59
def prefixEnd_27975 : Nat := 4983230072969 + 3 ^ 40 * 27975 * 2
def baseEnd_27975 : Nat := 532023011467899310513

theorem tailTrace_27975 : CollatzResearch.WordTrace tailWord_27975 prefixEnd_27975 532023011467899310513 := by
  unfold tailWord_27975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020332073658827594733379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 680221382439218396488919 1020332073658827594733379)
  ·
    refine ⟨1530498110488241392100069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1020332073658827594733379 1530498110488241392100069)
    ·
      refine ⟨286968395716545261018763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1530498110488241392100069 286968395716545261018763)
      ·
        refine ⟨430452593574817891528145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286968395716545261018763 430452593574817891528145)
        ·
          refine ⟨322839445181113418646109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430452593574817891528145 322839445181113418646109)
          ·
            refine ⟨121064791942917531992291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322839445181113418646109 121064791942917531992291)
            ·
              refine ⟨181597187914376297988437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121064791942917531992291 181597187914376297988437)
              ·
                refine ⟨532023011467899310513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 181597187914376297988437 532023011467899310513)
                ·
                  rfl

theorem cell23_27975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 10].length) (baseStart_27975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27975 prefixEnd_27975 := by exact prefixLift 27975
  have htrace : WordTrace (prefixWord ++ tailWord_27975) baseStart_27975 baseEnd_27975 := by
    simpa [prefixWord, tailWord_27975, baseEnd_27975] using wordTrace_append hprefix tailTrace_27975
  have hstable : (prefixWord ++ tailWord_27975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27975).length < 2 ^ (prefixWord ++ tailWord_27975).sum := by decide
  have hdescent : baseEnd_27975 < baseStart_27975 := by decide
  rcases family_descends (prefixWord ++ tailWord_27975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27982 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_27982 : Nat := 118140960795 + 27982 * 2 ^ 59
def prefixEnd_27982 : Nat := 4983230072969 + 3 ^ 40 * 27982 * 2
def baseEnd_27982 : Nat := 14368215674214753996319

theorem tailTrace_27982 : CollatzResearch.WordTrace tailWord_27982 prefixEnd_27982 14368215674214753996319 := by
  unfold tailWord_27982
  simp only [CollatzResearch.WordTrace]
  refine ⟨127573423079183473779775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 680391589755645193492133 127573423079183473779775)
  ·
    refine ⟨191360134618775210669663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127573423079183473779775 191360134618775210669663)
    ·
      refine ⟨287040201928162816004495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191360134618775210669663 287040201928162816004495)
      ·
        refine ⟨430560302892244224006743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287040201928162816004495 430560302892244224006743)
        ·
          refine ⟨645840454338366336010115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430560302892244224006743 645840454338366336010115)
          ·
            refine ⟨968760681507549504015173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645840454338366336010115 968760681507549504015173)
            ·
              refine ⟨181642627782665532002845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 968760681507549504015173 181642627782665532002845)
              ·
                refine ⟨68115985418499574501067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181642627782665532002845 68115985418499574501067)
                ·
                  refine ⟨102173978127749361751601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68115985418499574501067 102173978127749361751601)
                  ·
                    refine ⟨76630483595812021313701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102173978127749361751601 76630483595812021313701)
                    ·
                      refine ⟨14368215674214753996319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 76630483595812021313701 14368215674214753996319)
                      ·
                        rfl

theorem cell23_27982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_27982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27982 prefixEnd_27982 := by exact prefixLift 27982
  have htrace : WordTrace (prefixWord ++ tailWord_27982) baseStart_27982 baseEnd_27982 := by
    simpa [prefixWord, tailWord_27982, baseEnd_27982] using wordTrace_append hprefix tailTrace_27982
  have hstable : (prefixWord ++ tailWord_27982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27982).length < 2 ^ (prefixWord ++ tailWord_27982).sum := by decide
  have hdescent : baseEnd_27982 < baseStart_27982 := by decide
  rcases family_descends (prefixWord ++ tailWord_27982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27989 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_27989 : Nat := 118140960795 + 27989 * 2 ^ 59
def prefixEnd_27989 : Nat := 4983230072969 + 3 ^ 40 * 27989 * 2
def baseEnd_27989 : Nat := 14371810038796226608787

theorem tailTrace_27989 : CollatzResearch.WordTrace tailWord_27989 prefixEnd_27989 14371810038796226608787 := by
  unfold tailWord_27989
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020842695608107985743021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 680561797072071990495347 1020842695608107985743021)
  ·
    refine ⟨382816010853040494653633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1020842695608107985743021 382816010853040494653633)
    ·
      refine ⟨287112008139780370990225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382816010853040494653633 287112008139780370990225)
      ·
        refine ⟨215334006104835278242669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287112008139780370990225 215334006104835278242669)
        ·
          refine ⟨80750252289313229341001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215334006104835278242669 80750252289313229341001)
          ·
            refine ⟨60562689216984922005751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80750252289313229341001 60562689216984922005751)
            ·
              refine ⟨90844033825477383008627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60562689216984922005751 90844033825477383008627)
              ·
                refine ⟨136266050738216074512941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90844033825477383008627 136266050738216074512941)
                ·
                  refine ⟨51099769026831027942353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136266050738216074512941 51099769026831027942353)
                  ·
                    refine ⟨38324826770123270956765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51099769026831027942353 38324826770123270956765)
                    ·
                      refine ⟨14371810038796226608787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38324826770123270956765 14371810038796226608787)
                      ·
                        rfl

theorem cell23_27989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_27989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_27989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_27989 prefixEnd_27989 := by exact prefixLift 27989
  have htrace : WordTrace (prefixWord ++ tailWord_27989) baseStart_27989 baseEnd_27989 := by
    simpa [prefixWord, tailWord_27989, baseEnd_27989] using wordTrace_append hprefix tailTrace_27989
  have hstable : (prefixWord ++ tailWord_27989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27989).length < 2 ^ (prefixWord ++ tailWord_27989).sum := by decide
  have hdescent : baseEnd_27989 < baseStart_27989 := by decide
  rcases family_descends (prefixWord ++ tailWord_27989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28014 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_28014 : Nat := 118140960795 + 28014 * 2 ^ 59
def prefixEnd_28014 : Nat := 4983230072969 + 3 ^ 40 * 28014 * 2
def baseEnd_28014 : Nat := 14384647055158628796173

theorem tailTrace_28014 : CollatzResearch.WordTrace tailWord_28014 prefixEnd_28014 14384647055158628796173 := by
  unfold tailWord_28014
  simp only [CollatzResearch.WordTrace]
  refine ⟨127719315064692156925387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 681169680345024836935397 127719315064692156925387)
  ·
    refine ⟨191578972597038235388081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127719315064692156925387 191578972597038235388081)
    ·
      refine ⟨143684229447778676541061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191578972597038235388081 143684229447778676541061)
      ·
        refine ⟨26940793021458501851449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143684229447778676541061 26940793021458501851449)
        ·
          refine ⟨20205594766093876388587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26940793021458501851449 20205594766093876388587)
          ·
            refine ⟨30308392149140814582881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20205594766093876388587 30308392149140814582881)
            ·
              refine ⟨22731294111855610937161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30308392149140814582881 22731294111855610937161)
              ·
                refine ⟨17048470583891708202871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22731294111855610937161 17048470583891708202871)
                ·
                  refine ⟨25572705875837562304307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17048470583891708202871 25572705875837562304307)
                  ·
                    refine ⟨38359058813756343456461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25572705875837562304307 38359058813756343456461)
                    ·
                      refine ⟨14384647055158628796173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38359058813756343456461 14384647055158628796173)
                      ·
                        rfl

theorem cell23_28014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_28014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28014 prefixEnd_28014 := by exact prefixLift 28014
  have htrace : WordTrace (prefixWord ++ tailWord_28014) baseStart_28014 baseEnd_28014 := by
    simpa [prefixWord, tailWord_28014, baseEnd_28014] using wordTrace_append hprefix tailTrace_28014
  have hstable : (prefixWord ++ tailWord_28014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28014).length < 2 ^ (prefixWord ++ tailWord_28014).sum := by decide
  have hdescent : baseEnd_28014 < baseStart_28014 := by decide
  rcases family_descends (prefixWord ++ tailWord_28014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28029 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_28029 : Nat := 118140960795 + 28029 * 2 ^ 59
def prefixEnd_28029 : Nat := 4983230072969 + 3 ^ 40 * 28029 * 2
def baseEnd_28029 : Nat := 14392349264976070108603

theorem tailTrace_28029 : CollatzResearch.WordTrace tailWord_28029 prefixEnd_28029 14392349264976070108603 := by
  unfold tailWord_28029
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022301615463194817199141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 681534410308796544799427 1022301615463194817199141)
  ·
    refine ⟨191681552899349028224839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1022301615463194817199141 191681552899349028224839)
    ·
      refine ⟨287522329349023542337259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191681552899349028224839 287522329349023542337259)
      ·
        refine ⟨431283494023535313505889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287522329349023542337259 431283494023535313505889)
        ·
          refine ⟨323462620517651485129417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431283494023535313505889 323462620517651485129417)
          ·
            refine ⟨242596965388238613847063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323462620517651485129417 242596965388238613847063)
            ·
              refine ⟨363895448082357920770595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242596965388238613847063 363895448082357920770595)
              ·
                refine ⟨545843172123536881155893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363895448082357920770595 545843172123536881155893)
                ·
                  refine ⟨51172797386581582608365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 545843172123536881155893 51172797386581582608365)
                  ·
                    refine ⟨19189799019968093478137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51172797386581582608365 19189799019968093478137)
                    ·
                      refine ⟨14392349264976070108603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19189799019968093478137 14392349264976070108603)
                      ·
                        rfl

theorem cell23_28029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_28029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28029 prefixEnd_28029 := by exact prefixLift 28029
  have htrace : WordTrace (prefixWord ++ tailWord_28029) baseStart_28029 baseEnd_28029 := by
    simpa [prefixWord, tailWord_28029, baseEnd_28029] using wordTrace_append hprefix tailTrace_28029
  have hstable : (prefixWord ++ tailWord_28029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28029).length < 2 ^ (prefixWord ++ tailWord_28029).sum := by decide
  have hdescent : baseEnd_28029 < baseStart_28029 := by decide
  rcases family_descends (prefixWord ++ tailWord_28029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28036 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_28036 : Nat := 118140960795 + 28036 * 2 ^ 59
def prefixEnd_28036 : Nat := 4983230072969 + 3 ^ 40 * 28036 * 2
def baseEnd_28036 : Nat := 14395943629557542721071

theorem tailTrace_28036 : CollatzResearch.WordTrace tailWord_28036 prefixEnd_28036 14395943629557542721071 := by
  unfold tailWord_28036
  simp only [CollatzResearch.WordTrace]
  refine ⟨511278463218917506351981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 681704617625223341802641 511278463218917506351981)
  ·
    refine ⟨191729423707094064881993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 511278463218917506351981 191729423707094064881993)
    ·
      refine ⟨143797067780320548661495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191729423707094064881993 143797067780320548661495)
      ·
        refine ⟨215695601670480822992243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143797067780320548661495 215695601670480822992243)
        ·
          refine ⟨323543402505721234488365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215695601670480822992243 323543402505721234488365)
          ·
            refine ⟨121328775939645462933137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323543402505721234488365 121328775939645462933137)
            ·
              refine ⟨90996581954734097199853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121328775939645462933137 90996581954734097199853)
              ·
                refine ⟨34123718233025286449945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90996581954734097199853 34123718233025286449945)
                ·
                  refine ⟨25592788674768964837459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34123718233025286449945 25592788674768964837459)
                  ·
                    refine ⟨38389183012153447256189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25592788674768964837459 38389183012153447256189)
                    ·
                      refine ⟨14395943629557542721071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38389183012153447256189 14395943629557542721071)
                      ·
                        rfl

theorem cell23_28036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_28036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28036 prefixEnd_28036 := by exact prefixLift 28036
  have htrace : WordTrace (prefixWord ++ tailWord_28036) baseStart_28036 baseEnd_28036 := by
    simpa [prefixWord, tailWord_28036, baseEnd_28036] using wordTrace_append hprefix tailTrace_28036
  have hstable : (prefixWord ++ tailWord_28036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28036).length < 2 ^ (prefixWord ++ tailWord_28036).sum := by decide
  have hdescent : baseEnd_28036 < baseStart_28036 := by decide
  rcases family_descends (prefixWord ++ tailWord_28036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28063 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 1, 3, 2]
def baseStart_28063 : Nat := 118140960795 + 28063 * 2 ^ 59
def prefixEnd_28063 : Nat := 4983230072969 + 3 ^ 40 * 28063 * 2
def baseEnd_28063 : Nat := 14409807607228937083447

theorem tailTrace_28063 : CollatzResearch.WordTrace tailWord_28063 prefixEnd_28063 14409807607228937083447 := by
  unfold tailWord_28063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1023541697340018623936843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 682361131560012415957895 1023541697340018623936843)
  ·
    refine ⟨1535312546010027935905265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1023541697340018623936843 1535312546010027935905265)
    ·
      refine ⟨1151484409507520951928949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1535312546010027935905265 1151484409507520951928949)
      ·
        refine ⟨107951663391330089243339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1151484409507520951928949 107951663391330089243339)
        ·
          refine ⟨161927495086995133865009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107951663391330089243339 161927495086995133865009)
          ·
            refine ⟨121445621315246350398757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161927495086995133865009 121445621315246350398757)
            ·
              refine ⟨22771053996608690699767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121445621315246350398757 22771053996608690699767)
              ·
                refine ⟨34156580994913036049651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22771053996608690699767 34156580994913036049651)
                ·
                  refine ⟨51234871492369554074477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34156580994913036049651 51234871492369554074477)
                  ·
                    refine ⟨19213076809638582777929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51234871492369554074477 19213076809638582777929)
                    ·
                      refine ⟨14409807607228937083447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19213076809638582777929 14409807607228937083447)
                      ·
                        rfl

theorem cell23_28063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_28063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28063 prefixEnd_28063 := by exact prefixLift 28063
  have htrace : WordTrace (prefixWord ++ tailWord_28063) baseStart_28063 baseEnd_28063 := by
    simpa [prefixWord, tailWord_28063, baseEnd_28063] using wordTrace_append hprefix tailTrace_28063
  have hstable : (prefixWord ++ tailWord_28063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28063).length < 2 ^ (prefixWord ++ tailWord_28063).sum := by decide
  have hdescent : baseEnd_28063 < baseStart_28063 := by decide
  rcases family_descends (prefixWord ++ tailWord_28063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28129 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_28129 : Nat := 118140960795 + 28129 * 2 ^ 59
def prefixEnd_28129 : Nat := 4983230072969 + 3 ^ 40 * 28129 * 2
def baseEnd_28129 : Nat := 4814565776808559619381

theorem tailTrace_28129 : CollatzResearch.WordTrace tailWord_28129 prefixEnd_28129 4814565776808559619381 := by
  unfold tailWord_28129
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025948915100911895839441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 683965943400607930559627 1025948915100911895839441)
  ·
    refine ⟨769461686325683921879581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1025948915100911895839441 769461686325683921879581)
    ·
      refine ⟨288548132372131470704843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 769461686325683921879581 288548132372131470704843)
      ·
        refine ⟨432822198558197206057265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288548132372131470704843 432822198558197206057265)
        ·
          refine ⟨324616648918647904542949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432822198558197206057265 324616648918647904542949)
          ·
            refine ⟨60865621672246482101803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324616648918647904542949 60865621672246482101803)
            ·
              refine ⟨91298432508369723152705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60865621672246482101803 91298432508369723152705)
              ·
                refine ⟨68473824381277292364529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91298432508369723152705 68473824381277292364529)
                ·
                  refine ⟨51355368285957969273397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68473824381277292364529 51355368285957969273397)
                  ·
                    refine ⟨4814565776808559619381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51355368285957969273397 4814565776808559619381)
                    ·
                      rfl

theorem cell23_28129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_28129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28129 prefixEnd_28129 := by exact prefixLift 28129
  have htrace : WordTrace (prefixWord ++ tailWord_28129) baseStart_28129 baseEnd_28129 := by
    simpa [prefixWord, tailWord_28129, baseEnd_28129] using wordTrace_append hprefix tailTrace_28129
  have hstable : (prefixWord ++ tailWord_28129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28129).length < 2 ^ (prefixWord ++ tailWord_28129).sum := by decide
  have hdescent : baseEnd_28129 < baseStart_28129 := by decide
  rcases family_descends (prefixWord ++ tailWord_28129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28133 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 5]
def baseStart_28133 : Nat := 118140960795 + 28133 * 2 ^ 59
def prefixEnd_28133 : Nat := 4983230072969 + 3 ^ 40 * 28133 * 2
def baseEnd_28133 : Nat := 1605083472560407023125

theorem tailTrace_28133 : CollatzResearch.WordTrace tailWord_28133 prefixEnd_28133 1605083472560407023125 := by
  unfold tailWord_28133
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026094807086420578985053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 684063204724280385990035 1026094807086420578985053)
  ·
    refine ⟨384785552657407717119395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1026094807086420578985053 384785552657407717119395)
    ·
      refine ⟨577178328986111575679093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384785552657407717119395 577178328986111575679093)
      ·
        refine ⟨54110468342447960219915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 577178328986111575679093 54110468342447960219915)
        ·
          refine ⟨81165702513671940329873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54110468342447960219915 81165702513671940329873)
          ·
            refine ⟨60874276885253955247405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81165702513671940329873 60874276885253955247405)
            ·
              refine ⟨22827853831970233217777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60874276885253955247405 22827853831970233217777)
              ·
                refine ⟨17120890373977674913333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22827853831970233217777 17120890373977674913333)
                ·
                  refine ⟨1605083472560407023125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17120890373977674913333 1605083472560407023125)
                  ·
                    rfl

theorem cell23_28133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_28133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28133 prefixEnd_28133 := by exact prefixLift 28133
  have htrace : WordTrace (prefixWord ++ tailWord_28133) baseStart_28133 baseEnd_28133 := by
    simpa [prefixWord, tailWord_28133, baseEnd_28133] using wordTrace_append hprefix tailTrace_28133
  have hstable : (prefixWord ++ tailWord_28133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28133).length < 2 ^ (prefixWord ++ tailWord_28133).sum := by decide
  have hdescent : baseEnd_28133 < baseStart_28133 := by decide
  rcases family_descends (prefixWord ++ tailWord_28133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28193 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 1, 4]
def baseStart_28193 : Nat := 118140960795 + 28193 * 2 ^ 59
def prefixEnd_28193 : Nat := 4983230072969 + 3 ^ 40 * 28193 * 2
def baseEnd_28193 : Nat := 4825520030771142819283

theorem tailTrace_28193 : CollatzResearch.WordTrace tailWord_28193 prefixEnd_28193 4825520030771142819283 := by
  unfold tailWord_28193
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028283186869050826169233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 685522124579367217446155 1028283186869050826169233)
  ·
    refine ⟨771212390151788119626925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1028283186869050826169233 771212390151788119626925)
    ·
      refine ⟨289204646306920544860097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 771212390151788119626925 289204646306920544860097)
      ·
        refine ⟨216903484730190408645073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289204646306920544860097 216903484730190408645073)
        ·
          refine ⟨162677613547642806483805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216903484730190408645073 162677613547642806483805)
          ·
            refine ⟨61004105080366052431427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162677613547642806483805 61004105080366052431427)
            ·
              refine ⟨91506157620549078647141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61004105080366052431427 91506157620549078647141)
              ·
                refine ⟨17157404553852952246339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91506157620549078647141 17157404553852952246339)
                ·
                  refine ⟨25736106830779428369509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17157404553852952246339 25736106830779428369509)
                  ·
                    refine ⟨4825520030771142819283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25736106830779428369509 4825520030771142819283)
                    ·
                      rfl

theorem cell23_28193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_28193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28193 prefixEnd_28193 := by exact prefixLift 28193
  have htrace : WordTrace (prefixWord ++ tailWord_28193) baseStart_28193 baseEnd_28193 := by
    simpa [prefixWord, tailWord_28193, baseEnd_28193] using wordTrace_append hprefix tailTrace_28193
  have hstable : (prefixWord ++ tailWord_28193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28193).length < 2 ^ (prefixWord ++ tailWord_28193).sum := by decide
  have hdescent : baseEnd_28193 < baseStart_28193 := by decide
  rcases family_descends (prefixWord ++ tailWord_28193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28206 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_28206 : Nat := 118140960795 + 28206 * 2 ^ 59
def prefixEnd_28206 : Nat := 4983230072969 + 3 ^ 40 * 28206 * 2
def baseEnd_28206 : Nat := 1609248371202430843921

theorem tailTrace_28206 : CollatzResearch.WordTrace tailWord_28206 prefixEnd_28206 1609248371202430843921 := by
  unfold tailWord_28206
  simp only [CollatzResearch.WordTrace]
  refine ⟨128594666977744255799059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 685838223881302697594981 128594666977744255799059)
  ·
    refine ⟨192892000466616383698589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128594666977744255799059 192892000466616383698589)
    ·
      refine ⟨72334500174981143886971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192892000466616383698589 72334500174981143886971)
      ·
        refine ⟨108501750262471715830457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72334500174981143886971 108501750262471715830457)
        ·
          refine ⟨81376312696853786872843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108501750262471715830457 81376312696853786872843)
          ·
            refine ⟨122064469045280680309265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81376312696853786872843 122064469045280680309265)
            ·
              refine ⟨91548351783960510231949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122064469045280680309265 91548351783960510231949)
              ·
                refine ⟨34330631918985191336981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91548351783960510231949 34330631918985191336981)
                ·
                  refine ⟨1609248371202430843921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34330631918985191336981 1609248371202430843921)
                  ·
                    rfl

theorem cell23_28206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_28206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28206 prefixEnd_28206 := by exact prefixLift 28206
  have htrace : WordTrace (prefixWord ++ tailWord_28206) baseStart_28206 baseEnd_28206 := by
    simpa [prefixWord, tailWord_28206, baseEnd_28206] using wordTrace_append hprefix tailTrace_28206
  have hstable : (prefixWord ++ tailWord_28206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28206).length < 2 ^ (prefixWord ++ tailWord_28206).sum := by decide
  have hdescent : baseEnd_28206 < baseStart_28206 := by decide
  rcases family_descends (prefixWord ++ tailWord_28206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28216 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_28216 : Nat := 118140960795 + 28216 * 2 ^ 59
def prefixEnd_28216 : Nat := 4983230072969 + 3 ^ 40 * 28216 * 2
def baseEnd_28216 : Nat := 14488370147366838470243

theorem tailTrace_28216 : CollatzResearch.WordTrace tailWord_28216 prefixEnd_28216 14488370147366838470243 := by
  unfold tailWord_28216
  simp only [CollatzResearch.WordTrace]
  refine ⟨514561032892862877128251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 686081377190483836171001 514561032892862877128251)
  ·
    refine ⟨771841549339294315692377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 514561032892862877128251 771841549339294315692377)
    ·
      refine ⟨578881162004470736769283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 771841549339294315692377 578881162004470736769283)
      ·
        refine ⟨868321743006706105153925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578881162004470736769283 868321743006706105153925)
        ·
          refine ⟨162810326813757394716361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 868321743006706105153925 162810326813757394716361)
          ·
            refine ⟨122107745110318046037271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162810326813757394716361 122107745110318046037271)
            ·
              refine ⟨183161617665477069055907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122107745110318046037271 183161617665477069055907)
              ·
                refine ⟨274742426498215603583861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183161617665477069055907 274742426498215603583861)
                ·
                  refine ⟨25757102484207712835987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274742426498215603583861 25757102484207712835987)
                  ·
                    refine ⟨38635653726311569253981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25757102484207712835987 38635653726311569253981)
                    ·
                      refine ⟨14488370147366838470243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38635653726311569253981 14488370147366838470243)
                      ·
                        rfl

theorem cell23_28216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_28216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28216 prefixEnd_28216 := by exact prefixLift 28216
  have htrace : WordTrace (prefixWord ++ tailWord_28216) baseStart_28216 baseEnd_28216 := by
    simpa [prefixWord, tailWord_28216, baseEnd_28216] using wordTrace_append hprefix tailTrace_28216
  have hstable : (prefixWord ++ tailWord_28216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28216).length < 2 ^ (prefixWord ++ tailWord_28216).sum := by decide
  have hdescent : baseEnd_28216 < baseStart_28216 := by decide
  rcases family_descends (prefixWord ++ tailWord_28216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28220 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_28220 : Nat := 118140960795 + 28220 * 2 ^ 59
def prefixEnd_28220 : Nat := 4983230072969 + 3 ^ 40 * 28220 * 2
def baseEnd_28220 : Nat := 14490424069984822820225

theorem tailTrace_28220 : CollatzResearch.WordTrace tailWord_28220 prefixEnd_28220 14490424069984822820225 := by
  unfold tailWord_28220
  simp only [CollatzResearch.WordTrace]
  refine ⟨514633978885617218701057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 686178638514156291601409 514633978885617218701057)
  ·
    refine ⟨385975484164212914025793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 514633978885617218701057 385975484164212914025793)
    ·
      refine ⟨289481613123159685519345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385975484164212914025793 289481613123159685519345)
      ·
        refine ⟨217111209842369764139509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289481613123159685519345 217111209842369764139509)
        ·
          refine ⟨20354175922722165388079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217111209842369764139509 20354175922722165388079)
          ·
            refine ⟨30531263884083248082119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20354175922722165388079 30531263884083248082119)
            ·
              refine ⟨45796895826124872123179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30531263884083248082119 45796895826124872123179)
              ·
                refine ⟨68695343739187308184769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45796895826124872123179 68695343739187308184769)
                ·
                  refine ⟨51521507804390481138577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68695343739187308184769 51521507804390481138577)
                  ·
                    refine ⟨38641130853292860853933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51521507804390481138577 38641130853292860853933)
                    ·
                      refine ⟨14490424069984822820225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38641130853292860853933 14490424069984822820225)
                      ·
                        rfl

theorem cell23_28220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_28220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28220 prefixEnd_28220 := by exact prefixLift 28220
  have htrace : WordTrace (prefixWord ++ tailWord_28220) baseStart_28220 baseEnd_28220 := by
    simpa [prefixWord, tailWord_28220, baseEnd_28220] using wordTrace_append hprefix tailTrace_28220
  have hstable : (prefixWord ++ tailWord_28220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28220).length < 2 ^ (prefixWord ++ tailWord_28220).sum := by decide
  have hdescent : baseEnd_28220 < baseStart_28220 := by decide
  rcases family_descends (prefixWord ++ tailWord_28220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28236 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_28236 : Nat := 118140960795 + 28236 * 2 ^ 59
def prefixEnd_28236 : Nat := 4983230072969 + 3 ^ 40 * 28236 * 2
def baseEnd_28236 : Nat := 4832879920152253406717

theorem tailTrace_28236 : CollatzResearch.WordTrace tailWord_28236 prefixEnd_28236 4832879920152253406717 := by
  unfold tailWord_28236
  simp only [CollatzResearch.WordTrace]
  refine ⟨514925762856634584992281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 686567683808846113323041 514925762856634584992281)
  ·
    refine ⟨386194322142475938744211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 514925762856634584992281 386194322142475938744211)
    ·
      refine ⟨579291483213713908116317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386194322142475938744211 579291483213713908116317)
      ·
        refine ⟨217234306205142715543619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579291483213713908116317 217234306205142715543619)
        ·
          refine ⟨325851459307714073315429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217234306205142715543619 325851459307714073315429)
          ·
            refine ⟨61097148620196388746643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325851459307714073315429 61097148620196388746643)
            ·
              refine ⟨91645722930294583119965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61097148620196388746643 91645722930294583119965)
              ·
                refine ⟨34367146098860468669987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91645722930294583119965 34367146098860468669987)
                ·
                  refine ⟨51550719148290703004981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34367146098860468669987 51550719148290703004981)
                  ·
                    refine ⟨4832879920152253406717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51550719148290703004981 4832879920152253406717)
                    ·
                      rfl

theorem cell23_28236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_28236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28236 prefixEnd_28236 := by exact prefixLift 28236
  have htrace : WordTrace (prefixWord ++ tailWord_28236) baseStart_28236 baseEnd_28236 := by
    simpa [prefixWord, tailWord_28236, baseEnd_28236] using wordTrace_append hprefix tailTrace_28236
  have hstable : (prefixWord ++ tailWord_28236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28236).length < 2 ^ (prefixWord ++ tailWord_28236).sum := by decide
  have hdescent : baseEnd_28236 < baseStart_28236 := by decide
  rcases family_descends (prefixWord ++ tailWord_28236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28259 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5]
def baseStart_28259 : Nat := 118140960795 + 28259 * 2 ^ 59
def prefixEnd_28259 : Nat := 4983230072969 + 3 ^ 40 * 28259 * 2
def baseEnd_28259 : Nat := 14510449815510170232545

theorem tailTrace_28259 : CollatzResearch.WordTrace tailWord_28259 prefixEnd_28259 14510449815510170232545 := by
  unfold tailWord_28259
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030690404629944098071831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 687126936419962732047887 1030690404629944098071831)
  ·
    refine ⟨1546035606944916147107747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1030690404629944098071831 1546035606944916147107747)
    ·
      refine ⟨2319053410417374220661621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546035606944916147107747 2319053410417374220661621)
      ·
        refine ⟨217411257226628833187027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2319053410417374220661621 217411257226628833187027)
        ·
          refine ⟨326116885839943249780541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217411257226628833187027 326116885839943249780541)
          ·
            refine ⟨122293832189978718667703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326116885839943249780541 122293832189978718667703)
            ·
              refine ⟨183440748284968078001555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122293832189978718667703 183440748284968078001555)
              ·
                refine ⟨275161122427452117002333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183440748284968078001555 275161122427452117002333)
                ·
                  refine ⟨103185420910294543875875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275161122427452117002333 103185420910294543875875)
                  ·
                    refine ⟨154778131365441815813813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103185420910294543875875 154778131365441815813813)
                    ·
                      refine ⟨14510449815510170232545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 154778131365441815813813 14510449815510170232545)
                      ·
                        rfl

theorem cell23_28259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_28259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28259 prefixEnd_28259 := by exact prefixLift 28259
  have htrace : WordTrace (prefixWord ++ tailWord_28259) baseStart_28259 baseEnd_28259 := by
    simpa [prefixWord, tailWord_28259, baseEnd_28259] using wordTrace_append hprefix tailTrace_28259
  have hstable : (prefixWord ++ tailWord_28259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28259).length < 2 ^ (prefixWord ++ tailWord_28259).sum := by decide
  have hdescent : baseEnd_28259 < baseStart_28259 := by decide
  rcases family_descends (prefixWord ++ tailWord_28259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28266 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_28266 : Nat := 118140960795 + 28266 * 2 ^ 59
def prefixEnd_28266 : Nat := 4983230072969 + 3 ^ 40 * 28266 * 2
def baseEnd_28266 : Nat := 4838014726697214281671

theorem tailTrace_28266 : CollatzResearch.WordTrace tailWord_28266 prefixEnd_28266 4838014726697214281671 := by
  unfold tailWord_28266
  simp only [CollatzResearch.WordTrace]
  refine ⟨257736428901146073394163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 687297143736389529051101 257736428901146073394163)
  ·
    refine ⟨386604643351719110091245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257736428901146073394163 386604643351719110091245)
    ·
      refine ⟨144976741256894666284217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386604643351719110091245 144976741256894666284217)
      ·
        refine ⟨108732555942670999713163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144976741256894666284217 108732555942670999713163)
        ·
          refine ⟨163098833914006499569745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108732555942670999713163 163098833914006499569745)
          ·
            refine ⟨122324125435504874677309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163098833914006499569745 122324125435504874677309)
            ·
              refine ⟨45871547038314328003991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122324125435504874677309 45871547038314328003991)
              ·
                refine ⟨68807320557471492005987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45871547038314328003991 68807320557471492005987)
                ·
                  refine ⟨103210980836207238008981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68807320557471492005987 103210980836207238008981)
                  ·
                    refine ⟨4838014726697214281671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103210980836207238008981 4838014726697214281671)
                    ·
                      rfl

theorem cell23_28266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_28266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28266 prefixEnd_28266 := by exact prefixLift 28266
  have htrace : WordTrace (prefixWord ++ tailWord_28266) baseStart_28266 baseEnd_28266 := by
    simpa [prefixWord, tailWord_28266, baseEnd_28266] using wordTrace_append hprefix tailTrace_28266
  have hstable : (prefixWord ++ tailWord_28266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28266).length < 2 ^ (prefixWord ++ tailWord_28266).sum := by decide
  have hdescent : baseEnd_28266 < baseStart_28266 := by decide
  rcases family_descends (prefixWord ++ tailWord_28266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28323 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 3]
def baseStart_28323 : Nat := 118140960795 + 28323 * 2 ^ 59
def prefixEnd_28323 : Nat := 4983230072969 + 3 ^ 40 * 28323 * 2
def baseEnd_28323 : Nat := 14543312577397919832251

theorem tailTrace_28323 : CollatzResearch.WordTrace tailWord_28323 prefixEnd_28323 14543312577397919832251 := by
  unfold tailWord_28323
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033024676398083028401623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 688683117598722018934415 1033024676398083028401623)
  ·
    refine ⟨1549537014597124542602435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1033024676398083028401623 1549537014597124542602435)
    ·
      refine ⟨2324305521895686813903653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1549537014597124542602435 2324305521895686813903653)
      ·
        refine ⟨435807285355441277606935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2324305521895686813903653 435807285355441277606935)
        ·
          refine ⟨653710928033161916410403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435807285355441277606935 653710928033161916410403)
          ·
            refine ⟨980566392049742874615605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653710928033161916410403 980566392049742874615605)
            ·
              refine ⟨91928099254663394495213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 980566392049742874615605 91928099254663394495213)
              ·
                refine ⟨34473037220498772935705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91928099254663394495213 34473037220498772935705)
                ·
                  refine ⟨25854777915374079701779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34473037220498772935705 25854777915374079701779)
                  ·
                    refine ⟨38782166873061119552669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25854777915374079701779 38782166873061119552669)
                    ·
                      refine ⟨14543312577397919832251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 38782166873061119552669 14543312577397919832251)
                      ·
                        rfl

theorem cell23_28323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_28323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28323 prefixEnd_28323 := by exact prefixLift 28323
  have htrace : WordTrace (prefixWord ++ tailWord_28323) baseStart_28323 baseEnd_28323 := by
    simpa [prefixWord, tailWord_28323, baseEnd_28323] using wordTrace_append hprefix tailTrace_28323
  have hstable : (prefixWord ++ tailWord_28323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28323).length < 2 ^ (prefixWord ++ tailWord_28323).sum := by decide
  have hdescent : baseEnd_28323 < baseStart_28323 := by decide
  rcases family_descends (prefixWord ++ tailWord_28323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28356 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_28356 : Nat := 118140960795 + 28356 * 2 ^ 59
def prefixEnd_28356 : Nat := 4983230072969 + 3 ^ 40 * 28356 * 2
def baseEnd_28356 : Nat := 4853419146332096906533

theorem tailTrace_28356 : CollatzResearch.WordTrace tailWord_28356 prefixEnd_28356 4853419146332096906533 := by
  unfold tailWord_28356
  simp only [CollatzResearch.WordTrace]
  refine ⟨517114142639264832176461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 689485523519019776235281 517114142639264832176461)
  ·
    refine ⟨193917803489724312066173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 517114142639264832176461 193917803489724312066173)
    ·
      refine ⟨72719176308646617024815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193917803489724312066173 72719176308646617024815)
      ·
        refine ⟨109078764462969925537223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72719176308646617024815 109078764462969925537223)
        ·
          refine ⟨163618146694454888305835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109078764462969925537223 163618146694454888305835)
          ·
            refine ⟨245427220041682332458753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163618146694454888305835 245427220041682332458753)
            ·
              refine ⟨184070415031261749344065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245427220041682332458753 184070415031261749344065)
              ·
                refine ⟨138052811273446312008049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184070415031261749344065 138052811273446312008049)
                ·
                  refine ⟨103539608455084734006037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138052811273446312008049 103539608455084734006037)
                  ·
                    refine ⟨4853419146332096906533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103539608455084734006037 4853419146332096906533)
                    ·
                      rfl

theorem cell23_28356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_28356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28356 prefixEnd_28356 := by exact prefixLift 28356
  have htrace : WordTrace (prefixWord ++ tailWord_28356) baseStart_28356 baseEnd_28356 := by
    simpa [prefixWord, tailWord_28356, baseEnd_28356] using wordTrace_append hprefix tailTrace_28356
  have hstable : (prefixWord ++ tailWord_28356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28356).length < 2 ^ (prefixWord ++ tailWord_28356).sum := by decide
  have hdescent : baseEnd_28356 < baseStart_28356 := by decide
  rcases family_descends (prefixWord ++ tailWord_28356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28358 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_28358 : Nat := 118140960795 + 28358 * 2 ^ 59
def prefixEnd_28358 : Nat := 4983230072969 + 3 ^ 40 * 28358 * 2
def baseEnd_28358 : Nat := 14561284400305282894591

theorem tailTrace_28358 : CollatzResearch.WordTrace tailWord_28358 prefixEnd_28358 14561284400305282894591 := by
  unfold tailWord_28358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32321913477227625185179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 689534154180856003950485 32321913477227625185179)
  ·
    refine ⟨48482870215841437777769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32321913477227625185179 48482870215841437777769)
    ·
      refine ⟨36362152661881078333327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48482870215841437777769 36362152661881078333327)
      ·
        refine ⟨54543228992821617499991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36362152661881078333327 54543228992821617499991)
        ·
          refine ⟨81814843489232426249987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54543228992821617499991 81814843489232426249987)
          ·
            refine ⟨122722265233848639374981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81814843489232426249987 122722265233848639374981)
            ·
              refine ⟨23010424731346619882809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122722265233848639374981 23010424731346619882809)
              ·
                refine ⟨17257818548509964912107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23010424731346619882809 17257818548509964912107)
                ·
                  refine ⟨25886727822764947368161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17257818548509964912107 25886727822764947368161)
                  ·
                    refine ⟨19415045867073710526121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25886727822764947368161 19415045867073710526121)
                    ·
                      refine ⟨14561284400305282894591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19415045867073710526121 14561284400305282894591)
                      ·
                        rfl

theorem cell23_28358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_28358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28358 prefixEnd_28358 := by exact prefixLift 28358
  have htrace : WordTrace (prefixWord ++ tailWord_28358) baseStart_28358 baseEnd_28358 := by
    simpa [prefixWord, tailWord_28358, baseEnd_28358] using wordTrace_append hprefix tailTrace_28358
  have hstable : (prefixWord ++ tailWord_28358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28358).length < 2 ^ (prefixWord ++ tailWord_28358).sum := by decide
  have hdescent : baseEnd_28358 < baseStart_28358 := by decide
  rcases family_descends (prefixWord ++ tailWord_28358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28363 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 4, 2, 2]
def baseStart_28363 : Nat := 118140960795 + 28363 * 2 ^ 59
def prefixEnd_28363 : Nat := 4983230072969 + 3 ^ 40 * 28363 * 2
def baseEnd_28363 : Nat := 14563851803577763332067

theorem tailTrace_28363 : CollatzResearch.WordTrace tailWord_28363 prefixEnd_28363 14563851803577763332067 := by
  unfold tailWord_28363
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034483596253169859857743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 689655730835446573238495 1034483596253169859857743)
  ·
    refine ⟨1551725394379754789786615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034483596253169859857743 1551725394379754789786615)
    ·
      refine ⟨2327588091569632184679923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551725394379754789786615 2327588091569632184679923)
      ·
        refine ⟨3491382137354448277019885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327588091569632184679923 3491382137354448277019885)
        ·
          refine ⟨1309268301507918103882457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3491382137354448277019885 1309268301507918103882457)
          ·
            refine ⟨981951226130938577911843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309268301507918103882457 981951226130938577911843)
            ·
              refine ⟨1472926839196407866867765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981951226130938577911843 1472926839196407866867765)
              ·
                refine ⟨138086891174663237518853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1472926839196407866867765 138086891174663237518853)
                ·
                  refine ⟨25891292095249357034785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138086891174663237518853 25891292095249357034785)
                  ·
                    refine ⟨19418469071437017776089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25891292095249357034785 19418469071437017776089)
                    ·
                      refine ⟨14563851803577763332067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 19418469071437017776089 14563851803577763332067)
                      ·
                        rfl

theorem cell23_28363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 2, 2].length) (baseStart_28363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28363 prefixEnd_28363 := by exact prefixLift 28363
  have htrace : WordTrace (prefixWord ++ tailWord_28363) baseStart_28363 baseEnd_28363 := by
    simpa [prefixWord, tailWord_28363, baseEnd_28363] using wordTrace_append hprefix tailTrace_28363
  have hstable : (prefixWord ++ tailWord_28363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28363).length < 2 ^ (prefixWord ++ tailWord_28363).sum := by decide
  have hdescent : baseEnd_28363 < baseStart_28363 := by decide
  rcases family_descends (prefixWord ++ tailWord_28363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
