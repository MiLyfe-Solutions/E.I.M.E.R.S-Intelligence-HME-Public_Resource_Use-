import V185TrunkScan23Chunk0583

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3453703 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3453703 : Nat := 118140960795 + 3453703 * 2 ^ 59
def prefixEnd_3453703 : Nat := 4983230072969 + 3 ^ 40 * 3453703 * 2
def baseEnd_3453703 : Nat := 1773409676875206104829215

theorem tailTrace_3453703 : CollatzResearch.WordTrace tailWord_3453703 prefixEnd_3453703 1773409676875206104829215 := by
  unfold tailWord_3453703
  simp only [CollatzResearch.WordTrace]
  refine ⟨125966897006831351357509763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83977931337887567571673175 125966897006831351357509763)
  ·
    refine ⟨188950345510247027036264645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125966897006831351357509763 188950345510247027036264645)
    ·
      refine ⟨35428189783171317569299621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188950345510247027036264645 35428189783171317569299621)
      ·
        refine ⟨6642785584344622044243679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35428189783171317569299621 6642785584344622044243679)
        ·
          refine ⟨9964178376516933066365519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642785584344622044243679 9964178376516933066365519)
          ·
            refine ⟨14946267564775399599548279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964178376516933066365519 14946267564775399599548279)
            ·
              refine ⟨22419401347163099399322419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946267564775399599548279 22419401347163099399322419)
              ·
                refine ⟨33629102020744649098983629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22419401347163099399322419 33629102020744649098983629)
                ·
                  refine ⟨12610913257779243412118861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33629102020744649098983629 12610913257779243412118861)
                  ·
                    refine ⟨4729092471667216279544573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12610913257779243412118861 4729092471667216279544573)
                    ·
                      refine ⟨1773409676875206104829215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4729092471667216279544573 1773409676875206104829215)
                      ·
                        rfl

theorem cell23_3453703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3453703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453703 prefixEnd_3453703 := by exact prefixLift 3453703
  have htrace : WordTrace (prefixWord ++ tailWord_3453703) baseStart_3453703 baseEnd_3453703 := by
    simpa [prefixWord, tailWord_3453703, baseEnd_3453703] using wordTrace_append hprefix tailTrace_3453703
  have hstable : (prefixWord ++ tailWord_3453703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453703).length < 2 ^ (prefixWord ++ tailWord_3453703).sum := by decide
  have hdescent : baseEnd_3453703 < baseStart_3453703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453730 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_3453730 : Nat := 118140960795 + 3453730 * 2 ^ 59
def prefixEnd_3453730 : Nat := 4983230072969 + 3 ^ 40 * 3453730 * 2
def baseEnd_3453730 : Nat := 1773423540852877499191591

theorem tailTrace_3453730 : CollatzResearch.WordTrace tailWord_3453730 prefixEnd_3453730 1773423540852877499191591 := by
  unfold tailWord_3453730
  simp only [CollatzResearch.WordTrace]
  refine ⟨31491970444433383742185661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83978587851822356645828429 31491970444433383742185661)
  ·
    refine ⟨11809488916662518903319623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31491970444433383742185661 11809488916662518903319623)
    ·
      refine ⟨17714233374993778354979435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11809488916662518903319623 17714233374993778354979435)
      ·
        refine ⟨26571350062490667532469153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17714233374993778354979435 26571350062490667532469153)
        ·
          refine ⟨19928512546868000649351865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26571350062490667532469153 19928512546868000649351865)
          ·
            refine ⟨14946384410151000487013899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19928512546868000649351865 14946384410151000487013899)
            ·
              refine ⟨22419576615226500730520849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946384410151000487013899 22419576615226500730520849)
              ·
                refine ⟨16814682461419875547890637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22419576615226500730520849 16814682461419875547890637)
                ·
                  refine ⟨6305505923032453330458989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16814682461419875547890637 6305505923032453330458989)
                  ·
                    refine ⟨2364564721137169998922121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6305505923032453330458989 2364564721137169998922121)
                    ·
                      refine ⟨1773423540852877499191591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364564721137169998922121 1773423540852877499191591)
                      ·
                        rfl

theorem cell23_3453730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_3453730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453730 prefixEnd_3453730 := by exact prefixLift 3453730
  have htrace : WordTrace (prefixWord ++ tailWord_3453730) baseStart_3453730 baseEnd_3453730 := by
    simpa [prefixWord, tailWord_3453730, baseEnd_3453730] using wordTrace_append hprefix tailTrace_3453730
  have hstable : (prefixWord ++ tailWord_3453730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453730).length < 2 ^ (prefixWord ++ tailWord_3453730).sum := by decide
  have hdescent : baseEnd_3453730 < baseStart_3453730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453756 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3453756 : Nat := 118140960795 + 3453756 * 2 ^ 59
def prefixEnd_3453756 : Nat := 4983230072969 + 3 ^ 40 * 3453756 * 2
def baseEnd_3453756 : Nat := 1773436891349894397466471

theorem tailTrace_3453756 : CollatzResearch.WordTrace tailWord_3453756 prefixEnd_3453756 1773436891349894397466471 := by
  unfold tailWord_3453756
  simp only [CollatzResearch.WordTrace]
  refine ⟨62984415037819670704594561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83979220050426227606126081 62984415037819670704594561)
  ·
    refine ⟨47238311278364753028445921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62984415037819670704594561 47238311278364753028445921)
    ·
      refine ⟨35428733458773564771334441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47238311278364753028445921 35428733458773564771334441)
      ·
        refine ⟨26571550094080173578500831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35428733458773564771334441 26571550094080173578500831)
        ·
          refine ⟨39857325141120260367751247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26571550094080173578500831 39857325141120260367751247)
          ·
            refine ⟨59785987711680390551626871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39857325141120260367751247 59785987711680390551626871)
            ·
              refine ⟨89678981567520585827440307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59785987711680390551626871 89678981567520585827440307)
              ·
                refine ⟨134518472351280878741160461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89678981567520585827440307 134518472351280878741160461)
                ·
                  refine ⟨50444427131730329527935173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134518472351280878741160461 50444427131730329527935173)
                  ·
                    refine ⟨9458330087199436786487845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50444427131730329527935173 9458330087199436786487845)
                    ·
                      refine ⟨1773436891349894397466471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9458330087199436786487845 1773436891349894397466471)
                      ·
                        rfl

theorem cell23_3453756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3453756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453756 prefixEnd_3453756 := by exact prefixLift 3453756
  have htrace : WordTrace (prefixWord ++ tailWord_3453756) baseStart_3453756 baseEnd_3453756 := by
    simpa [prefixWord, tailWord_3453756, baseEnd_3453756] using wordTrace_append hprefix tailTrace_3453756
  have hstable : (prefixWord ++ tailWord_3453756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453756).length < 2 ^ (prefixWord ++ tailWord_3453756).sum := by decide
  have hdescent : baseEnd_3453756 < baseStart_3453756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453777 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 4, 2, 2]
def baseStart_3453777 : Nat := 118140960795 + 3453777 * 2 ^ 59
def prefixEnd_3453777 : Nat := 4983230072969 + 3 ^ 40 * 3453777 * 2
def baseEnd_3453777 : Nat := 1773447674443638815303875

theorem tailTrace_3453777 : CollatzResearch.WordTrace tailWord_3453777 prefixEnd_3453777 1773447674443638815303875 := by
  unfold tailWord_3453777
  simp only [CollatzResearch.WordTrace]
  refine ⟨125969596008563261995703585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83979730672375507997135723 125969596008563261995703585)
  ·
    refine ⟨94477197006422446496777689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125969596008563261995703585 94477197006422446496777689)
    ·
      refine ⟨70857897754816834872583267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94477197006422446496777689 70857897754816834872583267)
      ·
        refine ⟨106286846632225252308874901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70857897754816834872583267 106286846632225252308874901)
        ·
          refine ⟨4982195935885558701978511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106286846632225252308874901 4982195935885558701978511)
          ·
            refine ⟨7473293903828338052967767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982195935885558701978511 7473293903828338052967767)
            ·
              refine ⟨11209940855742507079451651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473293903828338052967767 11209940855742507079451651)
              ·
                refine ⟨16814911283613760619177477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11209940855742507079451651 16814911283613760619177477)
                ·
                  refine ⟨3152795865677580116095777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16814911283613760619177477 3152795865677580116095777)
                  ·
                    refine ⟨2364596899258185087071833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3152795865677580116095777 2364596899258185087071833)
                    ·
                      refine ⟨1773447674443638815303875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364596899258185087071833 1773447674443638815303875)
                      ·
                        rfl

theorem cell23_3453777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_3453777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453777 prefixEnd_3453777 := by exact prefixLift 3453777
  have htrace : WordTrace (prefixWord ++ tailWord_3453777) baseStart_3453777 baseEnd_3453777 := by
    simpa [prefixWord, tailWord_3453777, baseEnd_3453777] using wordTrace_append hprefix tailTrace_3453777
  have hstable : (prefixWord ++ tailWord_3453777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453777).length < 2 ^ (prefixWord ++ tailWord_3453777).sum := by decide
  have hdescent : baseEnd_3453777 < baseStart_3453777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453783 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 7]
def baseStart_3453783 : Nat := 118140960795 + 3453783 * 2 ^ 59
def prefixEnd_3453783 : Nat := 4983230072969 + 3 ^ 40 * 3453783 * 2
def baseEnd_3453783 : Nat := 197050083925285087980983

theorem tailTrace_3453783 : CollatzResearch.WordTrace tailWord_3453783 prefixEnd_3453783 197050083925285087980983 := by
  unfold tailWord_3453783
  simp only [CollatzResearch.WordTrace]
  refine ⟨125969814846541525020422003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83979876564361016680281335 125969814846541525020422003)
  ·
    refine ⟨188954722269812287530633005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125969814846541525020422003 188954722269812287530633005)
    ·
      refine ⟨70858020851179607823987377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188954722269812287530633005 70858020851179607823987377)
      ·
        refine ⟨53143515638384705867990533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70858020851179607823987377 53143515638384705867990533)
        ·
          refine ⟨9964409182197132350248225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53143515638384705867990533 9964409182197132350248225)
          ·
            refine ⟨7473306886647849262686169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9964409182197132350248225 7473306886647849262686169)
            ·
              refine ⟨5604980164985886947014627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7473306886647849262686169 5604980164985886947014627)
              ·
                refine ⟨8407470247478830420521941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604980164985886947014627 8407470247478830420521941)
                ·
                  refine ⟨197050083925285087980983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8407470247478830420521941 197050083925285087980983)
                  ·
                    rfl

theorem cell23_3453783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 7].length) (baseStart_3453783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453783 prefixEnd_3453783 := by exact prefixLift 3453783
  have htrace : WordTrace (prefixWord ++ tailWord_3453783) baseStart_3453783 baseEnd_3453783 := by
    simpa [prefixWord, tailWord_3453783, baseEnd_3453783] using wordTrace_append hprefix tailTrace_3453783
  have hstable : (prefixWord ++ tailWord_3453783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453783).length < 2 ^ (prefixWord ++ tailWord_3453783).sum := by decide
  have hdescent : baseEnd_3453783 < baseStart_3453783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453794 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_3453794 : Nat := 118140960795 + 3453794 * 2 ^ 59
def prefixEnd_3453794 : Nat := 4983230072969 + 3 ^ 40 * 3453794 * 2
def baseEnd_3453794 : Nat := 1773456403614765248791297

theorem tailTrace_3453794 : CollatzResearch.WordTrace tailWord_3453794 prefixEnd_3453794 1773456403614765248791297 := by
  unfold tailWord_3453794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31492554012375418474768109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83980144033001115932714957 31492554012375418474768109)
  ·
    refine ⟨11809707754640781928038041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31492554012375418474768109 11809707754640781928038041)
    ·
      refine ⟨8857280815980586446028531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11809707754640781928038041 8857280815980586446028531)
      ·
        refine ⟨13285921223970879669042797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857280815980586446028531 13285921223970879669042797)
        ·
          refine ⟨4982220458989079875891049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13285921223970879669042797 4982220458989079875891049)
          ·
            refine ⟨3736665344241809906918287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4982220458989079875891049 3736665344241809906918287)
            ·
              refine ⟨5604998016362714860377431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736665344241809906918287 5604998016362714860377431)
              ·
                refine ⟨8407497024544072290566147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604998016362714860377431 8407497024544072290566147)
                ·
                  refine ⟨12611245536816108435849221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407497024544072290566147 12611245536816108435849221)
                  ·
                    refine ⟨2364608538153020331721729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12611245536816108435849221 2364608538153020331721729)
                    ·
                      refine ⟨1773456403614765248791297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364608538153020331721729 1773456403614765248791297)
                      ·
                        rfl

theorem cell23_3453794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_3453794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453794 prefixEnd_3453794 := by exact prefixLift 3453794
  have htrace : WordTrace (prefixWord ++ tailWord_3453794) baseStart_3453794 baseEnd_3453794 := by
    simpa [prefixWord, tailWord_3453794, baseEnd_3453794] using wordTrace_append hprefix tailTrace_3453794
  have hstable : (prefixWord ++ tailWord_3453794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453794).length < 2 ^ (prefixWord ++ tailWord_3453794).sum := by decide
  have hdescent : baseEnd_3453794 < baseStart_3453794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453803 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 2, 5, 2]
def baseStart_3453803 : Nat := 118140960795 + 3453803 * 2 ^ 59
def prefixEnd_3453803 : Nat := 4983230072969 + 3 ^ 40 * 3453803 * 2
def baseEnd_3453803 : Nat := 1773461024940655713578755

theorem tailTrace_3453803 : CollatzResearch.WordTrace tailWord_3453803 prefixEnd_3453803 1773461024940655713578755 := by
  unfold tailWord_3453803
  simp only [CollatzResearch.WordTrace]
  refine ⟨125970544306469068436150063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83980362870979378957433375 125970544306469068436150063)
  ·
    refine ⟨188955816459703602654225095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125970544306469068436150063 188955816459703602654225095)
    ·
      refine ⟨283433724689555403981337643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188955816459703602654225095 283433724689555403981337643)
      ·
        refine ⟨425150587034333105972006465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283433724689555403981337643 425150587034333105972006465)
        ·
          refine ⟨318862940275749829479004849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425150587034333105972006465 318862940275749829479004849)
          ·
            refine ⟨239147205206812372109253637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318862940275749829479004849 239147205206812372109253637)
            ·
              refine ⟨44840100976277319770485057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239147205206812372109253637 44840100976277319770485057)
              ·
                refine ⟨33630075732207989827863793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44840100976277319770485057 33630075732207989827863793)
                ·
                  refine ⟨25222556799155992370897845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33630075732207989827863793 25222556799155992370897845)
                  ·
                    refine ⟨2364614699920874284771673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25222556799155992370897845 2364614699920874284771673)
                    ·
                      refine ⟨1773461024940655713578755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364614699920874284771673 1773461024940655713578755)
                      ·
                        rfl

theorem cell23_3453803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5, 2].length) (baseStart_3453803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453803 prefixEnd_3453803 := by exact prefixLift 3453803
  have htrace : WordTrace (prefixWord ++ tailWord_3453803) baseStart_3453803 baseEnd_3453803 := by
    simpa [prefixWord, tailWord_3453803, baseEnd_3453803] using wordTrace_append hprefix tailTrace_3453803
  have hstable : (prefixWord ++ tailWord_3453803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453803).length < 2 ^ (prefixWord ++ tailWord_3453803).sum := by decide
  have hdescent : baseEnd_3453803 < baseStart_3453803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453813 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3453813 : Nat := 118140960795 + 3453813 * 2 ^ 59
def prefixEnd_3453813 : Nat := 4983230072969 + 3 ^ 40 * 3453813 * 2
def baseEnd_3453813 : Nat := 591155386582400224817903

theorem tailTrace_3453813 : CollatzResearch.WordTrace tailWord_3453813 prefixEnd_3453813 591155386582400224817903 := by
  unfold tailWord_3453813
  simp only [CollatzResearch.WordTrace]
  refine ⟨125970909036432840144014093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83980606024288560096009395 125970909036432840144014093)
  ·
    refine ⟨47239090888662315054005285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125970909036432840144014093 47239090888662315054005285)
    ·
      refine ⟨8857329541624184072625991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47239090888662315054005285 8857329541624184072625991)
      ·
        refine ⟨13285994312436276108938987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857329541624184072625991 13285994312436276108938987)
        ·
          refine ⟨19928991468654414163408481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13285994312436276108938987 19928991468654414163408481)
          ·
            refine ⟨14946743601490810622556361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19928991468654414163408481 14946743601490810622556361)
            ·
              refine ⟨11210057701118107966917271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14946743601490810622556361 11210057701118107966917271)
              ·
                refine ⟨16815086551677161950375907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11210057701118107966917271 16815086551677161950375907)
                ·
                  refine ⟨25222629827515742925563861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16815086551677161950375907 25222629827515742925563861)
                  ·
                    refine ⟨591155386582400224817903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25222629827515742925563861 591155386582400224817903)
                    ·
                      rfl

theorem cell23_3453813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3453813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453813 prefixEnd_3453813 := by exact prefixLift 3453813
  have htrace : WordTrace (prefixWord ++ tailWord_3453813) baseStart_3453813 baseEnd_3453813 := by
    simpa [prefixWord, tailWord_3453813, baseEnd_3453813] using wordTrace_append hprefix tailTrace_3453813
  have hstable : (prefixWord ++ tailWord_3453813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453813).length < 2 ^ (prefixWord ++ tailWord_3453813).sum := by decide
  have hdescent : baseEnd_3453813 < baseStart_3453813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453833 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_3453833 : Nat := 118140960795 + 3453833 * 2 ^ 59
def prefixEnd_3453833 : Nat := 4983230072969 + 3 ^ 40 * 3453833 * 2
def baseEnd_3453833 : Nat := 1773476429360290596203617

theorem tailTrace_3453833 : CollatzResearch.WordTrace tailWord_3453833 prefixEnd_3453833 1773476429360290596203617 := by
  unfold tailWord_3453833
  simp only [CollatzResearch.WordTrace]
  refine ⟨125971638496360383559742153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83981092330906922373161435 125971638496360383559742153)
  ·
    refine ⟨94478728872270287669806615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125971638496360383559742153 94478728872270287669806615)
    ·
      refine ⟨141718093308405431504709923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94478728872270287669806615 141718093308405431504709923)
      ·
        refine ⟨212577139962608147257064885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141718093308405431504709923 212577139962608147257064885)
        ·
          refine ⟨19929106871494513805349833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212577139962608147257064885 19929106871494513805349833)
          ·
            refine ⟨14946830153620885354012375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19929106871494513805349833 14946830153620885354012375)
            ·
              refine ⟨22420245230431328031018563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946830153620885354012375 22420245230431328031018563)
              ·
                refine ⟨33630367845646992046527845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22420245230431328031018563 33630367845646992046527845)
                ·
                  refine ⟨6305693971058811008723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33630367845646992046527845 6305693971058811008723971)
                  ·
                    refine ⟨9458540956588216513085957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305693971058811008723971 9458540956588216513085957)
                    ·
                      refine ⟨1773476429360290596203617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9458540956588216513085957 1773476429360290596203617)
                      ·
                        rfl

theorem cell23_3453833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_3453833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453833 prefixEnd_3453833 := by exact prefixLift 3453833
  have htrace : WordTrace (prefixWord ++ tailWord_3453833) baseStart_3453833 baseEnd_3453833 := by
    simpa [prefixWord, tailWord_3453833, baseEnd_3453833] using wordTrace_append hprefix tailTrace_3453833
  have hstable : (prefixWord ++ tailWord_3453833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453833).length < 2 ^ (prefixWord ++ tailWord_3453833).sum := by decide
  have hdescent : baseEnd_3453833 < baseStart_3453833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453843 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 3, 4]
def baseStart_3453843 : Nat := 118140960795 + 3453843 * 2 ^ 59
def prefixEnd_3453843 : Nat := 4983230072969 + 3 ^ 40 * 3453843 * 2
def baseEnd_3453843 : Nat := 591160521388945185692857

theorem tailTrace_3453843 : CollatzResearch.WordTrace tailWord_3453843 prefixEnd_3453843 591160521388945185692857 := by
  unfold tailWord_3453843
  simp only [CollatzResearch.WordTrace]
  refine ⟨125972003226324155267606183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83981335484216103511737455 125972003226324155267606183)
  ·
    refine ⟨188958004839486232901409275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125972003226324155267606183 188958004839486232901409275)
    ·
      refine ⟨283437007259229349352113913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188958004839486232901409275 283437007259229349352113913)
      ·
        refine ⟨212577755444422012014085435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283437007259229349352113913 212577755444422012014085435)
        ·
          refine ⟨318866633166633018021128153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212577755444422012014085435 318866633166633018021128153)
          ·
            refine ⟨239149974874974763515846115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318866633166633018021128153 239149974874974763515846115)
            ·
              refine ⟨358724962312462145273769173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239149974874974763515846115 358724962312462145273769173)
              ·
                refine ⟨8407616304198331529853965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 358724962312462145273769173 8407616304198331529853965)
                ·
                  refine ⟨3152856114074374323695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8407616304198331529853965 3152856114074374323695237)
                  ·
                    refine ⟨591160521388945185692857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3152856114074374323695237 591160521388945185692857)
                    ·
                      rfl

theorem cell23_3453843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 4].length) (baseStart_3453843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453843 prefixEnd_3453843 := by exact prefixLift 3453843
  have htrace : WordTrace (prefixWord ++ tailWord_3453843) baseStart_3453843 baseEnd_3453843 := by
    simpa [prefixWord, tailWord_3453843, baseEnd_3453843] using wordTrace_append hprefix tailTrace_3453843
  have hstable : (prefixWord ++ tailWord_3453843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453843).length < 2 ^ (prefixWord ++ tailWord_3453843).sum := by decide
  have hdescent : baseEnd_3453843 < baseStart_3453843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453877 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3453877 : Nat := 118140960795 + 3453877 * 2 ^ 59
def prefixEnd_3453877 : Nat := 4983230072969 + 3 ^ 40 * 3453877 * 2
def baseEnd_3453877 : Nat := 591166340836362808017805

theorem tailTrace_3453877 : CollatzResearch.WordTrace tailWord_3453877 prefixEnd_3453877 591166340836362808017805 := by
  unfold tailWord_3453877
  simp only [CollatzResearch.WordTrace]
  refine ⟨125973243308200979074343885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83982162205467319382895923 125973243308200979074343885)
  ·
    refine ⟨47239966240575367152878957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125973243308200979074343885 47239966240575367152878957)
    ·
      refine ⟨17714987340215762682329609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47239966240575367152878957 17714987340215762682329609)
      ·
        refine ⟨13286240505161822011747207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17714987340215762682329609 13286240505161822011747207)
        ·
          refine ⟨19929360757742733017620811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13286240505161822011747207 19929360757742733017620811)
          ·
            refine ⟨29894041136614099526431217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19929360757742733017620811 29894041136614099526431217)
            ·
              refine ⟨22420530852460574644823413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29894041136614099526431217 22420530852460574644823413)
              ·
                refine ⟨2101924767418178872952195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22420530852460574644823413 2101924767418178872952195)
                ·
                  refine ⟨3152887151127268309428293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101924767418178872952195 3152887151127268309428293)
                  ·
                    refine ⟨591166340836362808017805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3152887151127268309428293 591166340836362808017805)
                    ·
                      rfl

theorem cell23_3453877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3453877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453877 prefixEnd_3453877 := by exact prefixLift 3453877
  have htrace : WordTrace (prefixWord ++ tailWord_3453877) baseStart_3453877 baseEnd_3453877 := by
    simpa [prefixWord, tailWord_3453877, baseEnd_3453877] using wordTrace_append hprefix tailTrace_3453877
  have hstable : (prefixWord ++ tailWord_3453877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453877).length < 2 ^ (prefixWord ++ tailWord_3453877).sum := by decide
  have hdescent : baseEnd_3453877 < baseStart_3453877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453903 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 3, 5]
def baseStart_3453903 : Nat := 118140960795 + 3453903 * 2 ^ 59
def prefixEnd_3453903 : Nat := 4983230072969 + 3 ^ 40 * 3453903 * 2
def baseEnd_3453903 : Nat := 591170791002035107442765

theorem tailTrace_3453903 : CollatzResearch.WordTrace tailWord_3453903 prefixEnd_3453903 591170791002035107442765 := by
  unfold tailWord_3453903
  simp only [CollatzResearch.WordTrace]
  refine ⟨125974191606106785514790363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83982794404071190343193575 125974191606106785514790363)
  ·
    refine ⟨188961287409160178272185545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125974191606106785514790363 188961287409160178272185545)
    ·
      refine ⟨141720965556870133704139159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188961287409160178272185545 141720965556870133704139159)
      ·
        refine ⟨212581448335305200556208739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141720965556870133704139159 212581448335305200556208739)
        ·
          refine ⟨318872172502957800834313109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212581448335305200556208739 318872172502957800834313109)
          ·
            refine ⟨14947133086076146914108427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 318872172502957800834313109 14947133086076146914108427)
            ·
              refine ⟨22420699629114220371162641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14947133086076146914108427 22420699629114220371162641)
              ·
                refine ⟨16815524721835665278371981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22420699629114220371162641 16815524721835665278371981)
                ·
                  refine ⟨6305821770688374479389493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16815524721835665278371981 6305821770688374479389493)
                  ·
                    refine ⟨591170791002035107442765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6305821770688374479389493 591170791002035107442765)
                    ·
                      rfl

theorem cell23_3453903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_3453903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453903 prefixEnd_3453903 := by exact prefixLift 3453903
  have htrace : WordTrace (prefixWord ++ tailWord_3453903) baseStart_3453903 baseEnd_3453903 := by
    simpa [prefixWord, tailWord_3453903, baseEnd_3453903] using wordTrace_append hprefix tailTrace_3453903
  have hstable : (prefixWord ++ tailWord_3453903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453903).length < 2 ^ (prefixWord ++ tailWord_3453903).sum := by decide
  have hdescent : baseEnd_3453903 < baseStart_3453903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453917 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3453917 : Nat := 118140960795 + 3453917 * 2 ^ 59
def prefixEnd_3453917 : Nat := 4983230072969 + 3 ^ 40 * 3453917 * 2
def baseEnd_3453917 : Nat := 1773519561735268267553231

theorem tailTrace_3453917 : CollatzResearch.WordTrace tailWord_3453917 prefixEnd_3453917 1773519561735268267553231 := by
  unfold tailWord_3453917
  simp only [CollatzResearch.WordTrace]
  refine ⟨125974702228056065905800005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83983134818704043937200003 125974702228056065905800005)
  ·
    refine ⟨23620256667760512357337501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125974702228056065905800005 23620256667760512357337501)
    ·
      refine ⟨8857596250410192134001563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23620256667760512357337501 8857596250410192134001563)
      ·
        refine ⟨13286394375615288201002345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857596250410192134001563 13286394375615288201002345)
        ·
          refine ⟨9964795781711466150751759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286394375615288201002345 9964795781711466150751759)
          ·
            refine ⟨14947193672567199226127639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964795781711466150751759 14947193672567199226127639)
            ·
              refine ⟨22420790508850798839191459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14947193672567199226127639 22420790508850798839191459)
              ·
                refine ⟨33631185763276198258787189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22420790508850798839191459 33631185763276198258787189)
                ·
                  refine ⟨3152923665307143586761299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33631185763276198258787189 3152923665307143586761299)
                  ·
                    refine ⟨4729385497960715380141949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3152923665307143586761299 4729385497960715380141949)
                    ·
                      refine ⟨1773519561735268267553231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4729385497960715380141949 1773519561735268267553231)
                      ·
                        rfl

theorem cell23_3453917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3453917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453917 prefixEnd_3453917 := by exact prefixLift 3453917
  have htrace : WordTrace (prefixWord ++ tailWord_3453917) baseStart_3453917 baseEnd_3453917 := by
    simpa [prefixWord, tailWord_3453917, baseEnd_3453917] using wordTrace_append hprefix tailTrace_3453917
  have hstable : (prefixWord ++ tailWord_3453917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453917).length < 2 ^ (prefixWord ++ tailWord_3453917).sum := by decide
  have hdescent : baseEnd_3453917 < baseStart_3453917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453927 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3453927 : Nat := 118140960795 + 3453927 * 2 ^ 59
def prefixEnd_3453927 : Nat := 4983230072969 + 3 ^ 40 * 3453927 * 2
def baseEnd_3453927 : Nat := 1773524696541813228428185

theorem tailTrace_3453927 : CollatzResearch.WordTrace tailWord_3453927 prefixEnd_3453927 1773524696541813228428185 := by
  unfold tailWord_3453927
  simp only [CollatzResearch.WordTrace]
  refine ⟨125975066958019837613664035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83983377972013225075776023 125975066958019837613664035)
  ·
    refine ⟨188962600437029756420496053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125975066958019837613664035 188962600437029756420496053)
    ·
      refine ⟨17715243790971539664421505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188962600437029756420496053 17715243790971539664421505)
      ·
        refine ⟨13286432843228654748316129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17715243790971539664421505 13286432843228654748316129)
        ·
          refine ⟨9964824632421491061237097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286432843228654748316129 9964824632421491061237097)
          ·
            refine ⟨7473618474316118295927823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9964824632421491061237097 7473618474316118295927823)
            ·
              refine ⟨11210427711474177443891735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473618474316118295927823 11210427711474177443891735)
              ·
                refine ⟨16815641567211266165837603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11210427711474177443891735 16815641567211266165837603)
                ·
                  refine ⟨25223462350816899248756405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16815641567211266165837603 25223462350816899248756405)
                  ·
                    refine ⟨2364699595389084304570913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25223462350816899248756405 2364699595389084304570913)
                    ·
                      refine ⟨1773524696541813228428185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364699595389084304570913 1773524696541813228428185)
                      ·
                        rfl

theorem cell23_3453927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3453927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453927 prefixEnd_3453927 := by exact prefixLift 3453927
  have htrace : WordTrace (prefixWord ++ tailWord_3453927) baseStart_3453927 baseEnd_3453927 := by
    simpa [prefixWord, tailWord_3453927, baseEnd_3453927] using wordTrace_append hprefix tailTrace_3453927
  have hstable : (prefixWord ++ tailWord_3453927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453927).length < 2 ^ (prefixWord ++ tailWord_3453927).sum := by decide
  have hdescent : baseEnd_3453927 < baseStart_3453927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453937 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 1, 5]
def baseStart_3453937 : Nat := 118140960795 + 3453937 * 2 ^ 59
def prefixEnd_3453937 : Nat := 4983230072969 + 3 ^ 40 * 3453937 * 2
def baseEnd_3453937 : Nat := 591176610449452729767713

theorem tailTrace_3453937 : CollatzResearch.WordTrace tailWord_3453937 prefixEnd_3453937 591176610449452729767713 := by
  unfold tailWord_3453937
  simp only [CollatzResearch.WordTrace]
  refine ⟨125975431687983609321528065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83983621125322406214352043 125975431687983609321528065)
  ·
    refine ⟨94481573765987706991146049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125975431687983609321528065 94481573765987706991146049)
    ·
      refine ⟨70861180324490780243359537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94481573765987706991146049 70861180324490780243359537)
      ·
        refine ⟨53145885243368085182519653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70861180324490780243359537 53145885243368085182519653)
        ·
          refine ⟨9964853483131515971722435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53145885243368085182519653 9964853483131515971722435)
          ·
            refine ⟨14947280224697273957583653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964853483131515971722435 14947280224697273957583653)
            ·
              refine ⟨2802615042130738867046935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14947280224697273957583653 2802615042130738867046935)
              ·
                refine ⟨4203922563196108300570403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802615042130738867046935 4203922563196108300570403)
                ·
                  refine ⟨6305883844794162450855605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203922563196108300570403 6305883844794162450855605)
                  ·
                    refine ⟨591176610449452729767713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6305883844794162450855605 591176610449452729767713)
                    ·
                      rfl

theorem cell23_3453937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_3453937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453937 prefixEnd_3453937 := by exact prefixLift 3453937
  have htrace : WordTrace (prefixWord ++ tailWord_3453937) baseStart_3453937 baseEnd_3453937 := by
    simpa [prefixWord, tailWord_3453937, baseEnd_3453937] using wordTrace_append hprefix tailTrace_3453937
  have hstable : (prefixWord ++ tailWord_3453937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453937).length < 2 ^ (prefixWord ++ tailWord_3453937).sum := by decide
  have hdescent : baseEnd_3453937 < baseStart_3453937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453941 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 6]
def baseStart_3453941 : Nat := 118140960795 + 3453941 * 2 ^ 59
def prefixEnd_3453941 : Nat := 4983230072969 + 3 ^ 40 * 3453941 * 2
def baseEnd_3453941 : Nat := 197059098363441797072569

theorem tailTrace_3453941 : CollatzResearch.WordTrace tailWord_3453941 prefixEnd_3453941 197059098363441797072569 := by
  unfold tailWord_3453941
  simp only [CollatzResearch.WordTrace]
  refine ⟨125975577579969118004673677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83983718386646078669782451 125975577579969118004673677)
  ·
    refine ⟨47240841592488419251752629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125975577579969118004673677 47240841592488419251752629)
    ·
      refine ⟨4428828899295789304851809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47240841592488419251752629 4428828899295789304851809)
      ·
        refine ⟨3321621674471841978638857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4428828899295789304851809 3321621674471841978638857)
        ·
          refine ⟨2491216255853881483979143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3321621674471841978638857 2491216255853881483979143)
          ·
            refine ⟨3736824383780822225968715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491216255853881483979143 3736824383780822225968715)
            ·
              refine ⟨5605236575671233338953073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736824383780822225968715 5605236575671233338953073)
              ·
                refine ⟨4203927431753425004214805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5605236575671233338953073 4203927431753425004214805)
                ·
                  refine ⟨197059098363441797072569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4203927431753425004214805 197059098363441797072569)
                  ·
                    rfl

theorem cell23_3453941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_3453941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453941 prefixEnd_3453941 := by exact prefixLift 3453941
  have htrace : WordTrace (prefixWord ++ tailWord_3453941) baseStart_3453941 baseEnd_3453941 := by
    simpa [prefixWord, tailWord_3453941, baseEnd_3453941] using wordTrace_append hprefix tailTrace_3453941
  have hstable : (prefixWord ++ tailWord_3453941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453941).length < 2 ^ (prefixWord ++ tailWord_3453941).sum := by decide
  have hdescent : baseEnd_3453941 < baseStart_3453941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453960 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3453960 : Nat := 118140960795 + 3453960 * 2 ^ 59
def prefixEnd_3453960 : Nat := 4983230072969 + 3 ^ 40 * 3453960 * 2
def baseEnd_3453960 : Nat := 1773541641403411599315533

theorem tailTrace_3453960 : CollatzResearch.WordTrace tailWord_3453960 prefixEnd_3453960 1773541641403411599315533 := by
  unfold tailWord_3453960
  simp only [CollatzResearch.WordTrace]
  refine ⟨62988135283450142124807667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83984180377933522833076889 62988135283450142124807667)
  ·
    refine ⟨94482202925175213187211501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62988135283450142124807667 94482202925175213187211501)
    ·
      refine ⟨35430826096940704945204313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94482202925175213187211501 35430826096940704945204313)
      ·
        refine ⟨26573119572705528708903235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35430826096940704945204313 26573119572705528708903235)
        ·
          refine ⟨39859679359058293063354853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26573119572705528708903235 39859679359058293063354853)
          ·
            refine ⟨7473689879823429949379035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39859679359058293063354853 7473689879823429949379035)
            ·
              refine ⟨11210534819735144924068553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473689879823429949379035 11210534819735144924068553)
              ·
                refine ⟨8407901114801358693051415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11210534819735144924068553 8407901114801358693051415)
                ·
                  refine ⟨12611851672202038039577123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407901114801358693051415 12611851672202038039577123)
                  ·
                    refine ⟨18917777508303057059365685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12611851672202038039577123 18917777508303057059365685)
                    ·
                      refine ⟨1773541641403411599315533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18917777508303057059365685 1773541641403411599315533)
                      ·
                        rfl

theorem cell23_3453960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3453960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453960 prefixEnd_3453960 := by exact prefixLift 3453960
  have htrace : WordTrace (prefixWord ++ tailWord_3453960) baseStart_3453960 baseEnd_3453960 := by
    simpa [prefixWord, tailWord_3453960, baseEnd_3453960] using wordTrace_append hprefix tailTrace_3453960
  have hstable : (prefixWord ++ tailWord_3453960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453960).length < 2 ^ (prefixWord ++ tailWord_3453960).sum := by decide
  have hdescent : baseEnd_3453960 < baseStart_3453960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453980 : List Nat := [2, 2, 3, 1, 4, 1, 1, 9]
def baseStart_3453980 : Nat := 118140960795 + 3453980 * 2 ^ 59
def prefixEnd_3453980 : Nat := 4983230072969 + 3 ^ 40 * 3453980 * 2
def baseEnd_3453980 : Nat := 65687107815425982261683

theorem tailTrace_3453980 : CollatzResearch.WordTrace tailWord_3453980 prefixEnd_3453980 65687107815425982261683 := by
  unfold tailWord_3453980
  simp only [CollatzResearch.WordTrace]
  refine ⟨62988500013413913832671697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83984666684551885110228929 62988500013413913832671697)
  ·
    refine ⟨47241375010060435374503773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62988500013413913832671697 47241375010060435374503773)
    ·
      refine ⟨17715515628772663265438915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47241375010060435374503773 17715515628772663265438915)
      ·
        refine ⟨26573273443158994898158373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17715515628772663265438915 26573273443158994898158373)
        ·
          refine ⟨4982488770592311543404695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26573273443158994898158373 4982488770592311543404695)
          ·
            refine ⟨7473733155888467315107043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982488770592311543404695 7473733155888467315107043)
            ·
              refine ⟨11210599733832700972660565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473733155888467315107043 11210599733832700972660565)
              ·
                refine ⟨65687107815425982261683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11210599733832700972660565 65687107815425982261683)
                ·
                  rfl

theorem cell23_3453980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 9].length) (baseStart_3453980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453980 prefixEnd_3453980 := by exact prefixLift 3453980
  have htrace : WordTrace (prefixWord ++ tailWord_3453980) baseStart_3453980 baseEnd_3453980 := by
    simpa [prefixWord, tailWord_3453980, baseEnd_3453980] using wordTrace_append hprefix tailTrace_3453980
  have hstable : (prefixWord ++ tailWord_3453980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453980).length < 2 ^ (prefixWord ++ tailWord_3453980).sum := by decide
  have hdescent : baseEnd_3453980 < baseStart_3453980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454003 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_3454003 : Nat := 118140960795 + 3454003 * 2 ^ 59
def prefixEnd_3454003 : Nat := 4983230072969 + 3 ^ 40 * 3454003 * 2
def baseEnd_3454003 : Nat := 1773563721071554931077835

theorem tailTrace_3454003 : CollatzResearch.WordTrace tailWord_3454003 prefixEnd_3454003 1773563721071554931077835 := by
  unfold tailWord_3454003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125977838905744502593430663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83985225937163001728953775 125977838905744502593430663)
  ·
    refine ⟨188966758358616753890145995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125977838905744502593430663 188966758358616753890145995)
    ·
      refine ⟨283450137537925130835218993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188966758358616753890145995 283450137537925130835218993)
      ·
        refine ⟨212587603153443848126414245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283450137537925130835218993 212587603153443848126414245)
        ·
          refine ⟨39860175591270721523702671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212587603153443848126414245 39860175591270721523702671)
          ·
            refine ⟨59790263386906082285554007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39860175591270721523702671 59790263386906082285554007)
            ·
              refine ⟨89685395080359123428331011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59790263386906082285554007 89685395080359123428331011)
              ·
                refine ⟨134528092620538685142496517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89685395080359123428331011 134528092620538685142496517)
                ·
                  refine ⟨25224017366351003464218097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134528092620538685142496517 25224017366351003464218097)
                  ·
                    refine ⟨18918013024763252598163573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25224017366351003464218097 18918013024763252598163573)
                    ·
                      refine ⟨1773563721071554931077835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18918013024763252598163573 1773563721071554931077835)
                      ·
                        rfl

theorem cell23_3454003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_3454003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454003 prefixEnd_3454003 := by exact prefixLift 3454003
  have htrace : WordTrace (prefixWord ++ tailWord_3454003) baseStart_3454003 baseEnd_3454003 := by
    simpa [prefixWord, tailWord_3454003, baseEnd_3454003] using wordTrace_append hprefix tailTrace_3454003
  have hstable : (prefixWord ++ tailWord_3454003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454003).length < 2 ^ (prefixWord ++ tailWord_3454003).sum := by decide
  have hdescent : baseEnd_3454003 < baseStart_3454003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454007 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_3454007 : Nat := 118140960795 + 3454007 * 2 ^ 59
def prefixEnd_3454007 : Nat := 4983230072969 + 3 ^ 40 * 3454007 * 2
def baseEnd_3454007 : Nat := 1773565774994172915427817

theorem tailTrace_3454007 : CollatzResearch.WordTrace tailWord_3454007 prefixEnd_3454007 1773565774994172915427817 := by
  unfold tailWord_3454007
  simp only [CollatzResearch.WordTrace]
  refine ⟨125977984797730011276576275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83985323198486674184384183 125977984797730011276576275)
  ·
    refine ⟨188966977196595016914864413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125977984797730011276576275 188966977196595016914864413)
    ·
      refine ⟨70862616448723131343074155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188966977196595016914864413 70862616448723131343074155)
      ·
        refine ⟨106293924673084697014611233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70862616448723131343074155 106293924673084697014611233)
        ·
          refine ⟨79720443504813522760958425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106293924673084697014611233 79720443504813522760958425)
          ·
            refine ⟨59790332628610142070718819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79720443504813522760958425 59790332628610142070718819)
            ·
              refine ⟨89685498942915213106078229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59790332628610142070718819 89685498942915213106078229)
              ·
                refine ⟨4204007762949150614347417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89685498942915213106078229 4204007762949150614347417)
                ·
                  refine ⟨3153005822211862960760563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204007762949150614347417 3153005822211862960760563)
                  ·
                    refine ⟨4729508733317794441140845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3153005822211862960760563 4729508733317794441140845)
                    ·
                      refine ⟨1773565774994172915427817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4729508733317794441140845 1773565774994172915427817)
                      ·
                        rfl

theorem cell23_3454007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_3454007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454007 prefixEnd_3454007 := by exact prefixLift 3454007
  have htrace : WordTrace (prefixWord ++ tailWord_3454007) baseStart_3454007 baseEnd_3454007 := by
    simpa [prefixWord, tailWord_3454007, baseEnd_3454007] using wordTrace_append hprefix tailTrace_3454007
  have hstable : (prefixWord ++ tailWord_3454007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454007).length < 2 ^ (prefixWord ++ tailWord_3454007).sum := by decide
  have hdescent : baseEnd_3454007 < baseStart_3454007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454008 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 1, 2, 2]
def baseStart_3454008 : Nat := 118140960795 + 3454008 * 2 ^ 59
def prefixEnd_3454008 : Nat := 4983230072969 + 3 ^ 40 * 3454008 * 2
def baseEnd_3454008 : Nat := 1773566288474827411515313

theorem tailTrace_3454008 : CollatzResearch.WordTrace tailWord_3454008 prefixEnd_3454008 1773566288474827411515313 := by
  unfold tailWord_3454008
  simp only [CollatzResearch.WordTrace]
  refine ⟨62989010635363194223681339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83985347513817592298241785 62989010635363194223681339)
  ·
    refine ⟨94483515953044791335522009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62989010635363194223681339 94483515953044791335522009)
    ·
      refine ⟨70862636964783593501641507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94483515953044791335522009 70862636964783593501641507)
      ·
        refine ⟨106293955447175390252462261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70862636964783593501641507 106293955447175390252462261)
        ·
          refine ⟨9965058323172692836168337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106293955447175390252462261 9965058323172692836168337)
          ·
            refine ⟨7473793742379519627126253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9965058323172692836168337 7473793742379519627126253)
            ·
              refine ⟨2802672653392319860172345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7473793742379519627126253 2802672653392319860172345)
              ·
                refine ⟨2102004490044239895129259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802672653392319860172345 2102004490044239895129259)
                ·
                  refine ⟨3153006735066359842693889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102004490044239895129259 3153006735066359842693889)
                  ·
                    refine ⟨2364755051299769882020417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3153006735066359842693889 2364755051299769882020417)
                    ·
                      refine ⟨1773566288474827411515313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364755051299769882020417 1773566288474827411515313)
                      ·
                        rfl

theorem cell23_3454008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_3454008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454008 prefixEnd_3454008 := by exact prefixLift 3454008
  have htrace : WordTrace (prefixWord ++ tailWord_3454008) baseStart_3454008 baseEnd_3454008 := by
    simpa [prefixWord, tailWord_3454008, baseEnd_3454008] using wordTrace_append hprefix tailTrace_3454008
  have hstable : (prefixWord ++ tailWord_3454008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454008).length < 2 ^ (prefixWord ++ tailWord_3454008).sum := by decide
  have hdescent : baseEnd_3454008 < baseStart_3454008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454034 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_3454034 : Nat := 118140960795 + 3454034 * 2 ^ 59
def prefixEnd_3454034 : Nat := 4983230072969 + 3 ^ 40 * 3454034 * 2
def baseEnd_3454034 : Nat := 1773579638971844309790193

theorem tailTrace_3454034 : CollatzResearch.WordTrace tailWord_3454034 prefixEnd_3454034 1773579638971844309790193 := by
  unfold tailWord_3454034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31494742392158048721952289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83985979712421463258539437 31494742392158048721952289)
  ·
    refine ⟨23621056794118536541464217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31494742392158048721952289 23621056794118536541464217)
    ·
      refine ⟨17715792595588902406098163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23621056794118536541464217 17715792595588902406098163)
      ·
        refine ⟨26573688893383353609147245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17715792595588902406098163 26573688893383353609147245)
        ·
          refine ⟨9965133335018757603430217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26573688893383353609147245 9965133335018757603430217)
          ·
            refine ⟨7473850001264068202572663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9965133335018757603430217 7473850001264068202572663)
            ·
              refine ⟨11210775001896102303858995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473850001264068202572663 11210775001896102303858995)
              ·
                refine ⟨16816162502844153455788493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11210775001896102303858995 16816162502844153455788493)
                ·
                  refine ⟨6306060938566557545920685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16816162502844153455788493 6306060938566557545920685)
                  ·
                    refine ⟨2364772851962459079720257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6306060938566557545920685 2364772851962459079720257)
                    ·
                      refine ⟨1773579638971844309790193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364772851962459079720257 1773579638971844309790193)
                      ·
                        rfl

theorem cell23_3454034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_3454034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454034 prefixEnd_3454034 := by exact prefixLift 3454034
  have htrace : WordTrace (prefixWord ++ tailWord_3454034) baseStart_3454034 baseEnd_3454034 := by
    simpa [prefixWord, tailWord_3454034, baseEnd_3454034] using wordTrace_append hprefix tailTrace_3454034
  have hstable : (prefixWord ++ tailWord_3454034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454034).length < 2 ^ (prefixWord ++ tailWord_3454034).sum := by decide
  have hdescent : baseEnd_3454034 < baseStart_3454034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454047 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 1, 4, 2]
def baseStart_3454047 : Nat := 118140960795 + 3454047 * 2 ^ 59
def prefixEnd_3454047 : Nat := 4983230072969 + 3 ^ 40 * 3454047 * 2
def baseEnd_3454047 : Nat := 1773586314220352758927633

theorem tailTrace_3454047 : CollatzResearch.WordTrace tailWord_3454047 prefixEnd_3454047 1773586314220352758927633 := by
  unfold tailWord_3454047
  simp only [CollatzResearch.WordTrace]
  refine ⟨125979443717585098108032395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83986295811723398738688263 125979443717585098108032395)
  ·
    refine ⟨188969165576377647162048593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125979443717585098108032395 188969165576377647162048593)
    ·
      refine ⟨141726874182283235371536445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188969165576377647162048593 141726874182283235371536445)
      ·
        refine ⟨53147577818356213264326167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141726874182283235371536445 53147577818356213264326167)
        ·
          refine ⟨79721366727534319896489251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53147577818356213264326167 79721366727534319896489251)
          ·
            refine ⟨119582050091301479844733877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79721366727534319896489251 119582050091301479844733877)
            ·
              refine ⟨11210817196059513735443801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119582050091301479844733877 11210817196059513735443801)
              ·
                refine ⟨8408112897044635301582851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11210817196059513735443801 8408112897044635301582851)
                ·
                  refine ⟨12612169345566952952374277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8408112897044635301582851 12612169345566952952374277)
                  ·
                    refine ⟨2364781752293803678570177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12612169345566952952374277 2364781752293803678570177)
                    ·
                      refine ⟨1773586314220352758927633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364781752293803678570177 1773586314220352758927633)
                      ·
                        rfl

theorem cell23_3454047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_3454047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454047 prefixEnd_3454047 := by exact prefixLift 3454047
  have htrace : WordTrace (prefixWord ++ tailWord_3454047) baseStart_3454047 baseEnd_3454047 := by
    simpa [prefixWord, tailWord_3454047, baseEnd_3454047] using wordTrace_append hprefix tailTrace_3454047
  have hstable : (prefixWord ++ tailWord_3454047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454047).length < 2 ^ (prefixWord ++ tailWord_3454047).sum := by decide
  have hdescent : baseEnd_3454047 < baseStart_3454047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454060 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3454060 : Nat := 118140960795 + 3454060 * 2 ^ 59
def prefixEnd_3454060 : Nat := 4983230072969 + 3 ^ 40 * 3454060 * 2
def baseEnd_3454060 : Nat := 1773592989468861208065073

theorem tailTrace_3454060 : CollatzResearch.WordTrace tailWord_3454060 prefixEnd_3454060 1773592989468861208065073 := by
  unfold tailWord_3454060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62989958933269000664127817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83986611911025334218837089 62989958933269000664127817)
  ·
    refine ⟨47242469199951750498095863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62989958933269000664127817 47242469199951750498095863)
    ·
      refine ⟨70863703799927625747143795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47242469199951750498095863 70863703799927625747143795)
      ·
        refine ⟨106295555699891438620715693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70863703799927625747143795 106295555699891438620715693)
        ·
          refine ⟨39860833387459289482768385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106295555699891438620715693 39860833387459289482768385)
          ·
            refine ⟨29895625040594467112076289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39860833387459289482768385 29895625040594467112076289)
            ·
              refine ⟨22421718780445850334057217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29895625040594467112076289 22421718780445850334057217)
              ·
                refine ⟨16816289085334387750542913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22421718780445850334057217 16816289085334387750542913)
                ·
                  refine ⟨12612216814000790812907185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16816289085334387750542913 12612216814000790812907185)
                  ·
                    refine ⟨9459162610500593109680389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12612216814000790812907185 9459162610500593109680389)
                    ·
                      refine ⟨1773592989468861208065073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9459162610500593109680389 1773592989468861208065073)
                      ·
                        rfl

theorem cell23_3454060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3454060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454060 prefixEnd_3454060 := by exact prefixLift 3454060
  have htrace : WordTrace (prefixWord ++ tailWord_3454060) baseStart_3454060 baseEnd_3454060 := by
    simpa [prefixWord, tailWord_3454060, baseEnd_3454060] using wordTrace_append hprefix tailTrace_3454060
  have hstable : (prefixWord ++ tailWord_3454060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454060).length < 2 ^ (prefixWord ++ tailWord_3454060).sum := by decide
  have hdescent : baseEnd_3454060 < baseStart_3454060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454080 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_3454080 : Nat := 118140960795 + 3454080 * 2 ^ 59
def prefixEnd_3454080 : Nat := 4983230072969 + 3 ^ 40 * 3454080 * 2
def baseEnd_3454080 : Nat := 1773603259081951129814981

theorem tailTrace_3454080 : CollatzResearch.WordTrace tailWord_3454080 prefixEnd_3454080 1773603259081951129814981 := by
  unfold tailWord_3454080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62990323663232772371991847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83987098217643696495989129 62990323663232772371991847)
  ·
    refine ⟨94485485494849158557987771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62990323663232772371991847 94485485494849158557987771)
    ·
      refine ⟨141728228242273737836981657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94485485494849158557987771 141728228242273737836981657)
      ·
        refine ⟨106296171181705303377736243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141728228242273737836981657 106296171181705303377736243)
        ·
          refine ⟨159444256772557955066604365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106296171181705303377736243 159444256772557955066604365)
          ·
            refine ⟨59791596289709233149976637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159444256772557955066604365 59791596289709233149976637)
            ·
              refine ⟨22421848608640962431241239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59791596289709233149976637 22421848608640962431241239)
              ·
                refine ⟨33632772912961443646861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22421848608640962431241239 33632772912961443646861859)
                ·
                  refine ⟨50449159369442165470292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33632772912961443646861859 50449159369442165470292789)
                  ·
                    refine ⟨4729608690885203012839949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50449159369442165470292789 4729608690885203012839949)
                    ·
                      refine ⟨1773603259081951129814981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4729608690885203012839949 1773603259081951129814981)
                      ·
                        rfl

theorem cell23_3454080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_3454080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454080 prefixEnd_3454080 := by exact prefixLift 3454080
  have htrace : WordTrace (prefixWord ++ tailWord_3454080) baseStart_3454080 baseEnd_3454080 := by
    simpa [prefixWord, tailWord_3454080, baseEnd_3454080] using wordTrace_append hprefix tailTrace_3454080
  have hstable : (prefixWord ++ tailWord_3454080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454080).length < 2 ^ (prefixWord ++ tailWord_3454080).sum := by decide
  have hdescent : baseEnd_3454080 < baseStart_3454080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454081 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_3454081 : Nat := 118140960795 + 3454081 * 2 ^ 59
def prefixEnd_3454081 : Nat := 4983230072969 + 3 ^ 40 * 3454081 * 2
def baseEnd_3454081 : Nat := 1773603772562605625902477

theorem tailTrace_3454081 : CollatzResearch.WordTrace tailWord_3454081 prefixEnd_3454081 1773603772562605625902477 := by
  unfold tailWord_3454081
  simp only [CollatzResearch.WordTrace]
  refine ⟨125980683799461921914770097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83987122532974614609846731 125980683799461921914770097)
  ·
    refine ⟨94485512849596441436077573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125980683799461921914770097 94485512849596441436077573)
    ·
      refine ⟨17716033659299332769264545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94485512849596441436077573 17716033659299332769264545)
      ·
        refine ⟨13287025244474499576948409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17716033659299332769264545 13287025244474499576948409)
        ·
          refine ⟨9965268933355874682711307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13287025244474499576948409 9965268933355874682711307)
          ·
            refine ⟨14947903400033812024066961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9965268933355874682711307 14947903400033812024066961)
            ·
              refine ⟨11210927550025359018050221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14947903400033812024066961 11210927550025359018050221)
              ·
                refine ⟨4204097831259509631768833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11210927550025359018050221 4204097831259509631768833)
                ·
                  refine ⟨3153073373444632223826625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204097831259509631768833 3153073373444632223826625)
                  ·
                    refine ⟨2364805030083474167869969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3153073373444632223826625 2364805030083474167869969)
                    ·
                      refine ⟨1773603772562605625902477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364805030083474167869969 1773603772562605625902477)
                      ·
                        rfl

theorem cell23_3454081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_3454081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454081 prefixEnd_3454081 := by exact prefixLift 3454081
  have htrace : WordTrace (prefixWord ++ tailWord_3454081) baseStart_3454081 baseEnd_3454081 := by
    simpa [prefixWord, tailWord_3454081, baseEnd_3454081] using wordTrace_append hprefix tailTrace_3454081
  have hstable : (prefixWord ++ tailWord_3454081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454081).length < 2 ^ (prefixWord ++ tailWord_3454081).sum := by decide
  have hdescent : baseEnd_3454081 < baseStart_3454081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454104 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 5]
def baseStart_3454104 : Nat := 118140960795 + 3454104 * 2 ^ 59
def prefixEnd_3454104 : Nat := 4983230072969 + 3 ^ 40 * 3454104 * 2
def baseEnd_3454104 : Nat := 197068398068628781768319

theorem tailTrace_3454104 : CollatzResearch.WordTrace tailWord_3454104 prefixEnd_3454104 197068398068628781768319 := by
  unfold tailWord_3454104
  simp only [CollatzResearch.WordTrace]
  refine ⟨62990761339189298421428683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83987681785585731228571577 62990761339189298421428683)
  ·
    refine ⟨94486142008783947632143025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62990761339189298421428683 94486142008783947632143025)
    ·
      refine ⟨70864606506587960724107269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94486142008783947632143025 70864606506587960724107269)
      ·
        refine ⟨13287113719985242635770113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70864606506587960724107269 13287113719985242635770113)
        ·
          refine ⟨9965335289988931976827585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13287113719985242635770113 9965335289988931976827585)
          ·
            refine ⟨7474001467491698982620689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9965335289988931976827585 7474001467491698982620689)
            ·
              refine ⟨5605501100618774236965517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7474001467491698982620689 5605501100618774236965517)
              ·
                refine ⟨2102062912732040338862069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5605501100618774236965517 2102062912732040338862069)
                ·
                  refine ⟨197068398068628781768319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2102062912732040338862069 197068398068628781768319)
                  ·
                    rfl

theorem cell23_3454104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 5].length) (baseStart_3454104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454104 prefixEnd_3454104 := by exact prefixLift 3454104
  have htrace : WordTrace (prefixWord ++ tailWord_3454104) baseStart_3454104 baseEnd_3454104 := by
    simpa [prefixWord, tailWord_3454104, baseEnd_3454104] using wordTrace_append hprefix tailTrace_3454104
  have hstable : (prefixWord ++ tailWord_3454104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454104).length < 2 ^ (prefixWord ++ tailWord_3454104).sum := by decide
  have hdescent : baseEnd_3454104 < baseStart_3454104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454180 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_3454180 : Nat := 118140960795 + 3454180 * 2 ^ 59
def prefixEnd_3454180 : Nat := 4983230072969 + 3 ^ 40 * 3454180 * 2
def baseEnd_3454180 : Nat := 1773654607147400738564521

theorem tailTrace_3454180 : CollatzResearch.WordTrace tailWord_3454180 prefixEnd_3454180 1773654607147400738564521 := by
  unfold tailWord_3454180
  simp only [CollatzResearch.WordTrace]
  refine ⟨62992147313051630911311997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83989529750735507881749329 62992147313051630911311997)
  ·
    refine ⟨23622055242394361591741999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62992147313051630911311997 23622055242394361591741999)
    ·
      refine ⟨35433082863591542387612999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23622055242394361591741999 35433082863591542387612999)
      ·
        refine ⟨53149624295387313581419499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35433082863591542387612999 53149624295387313581419499)
        ·
          refine ⟨79724436443080970372129249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53149624295387313581419499 79724436443080970372129249)
          ·
            refine ⟨59793327332310727779096937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79724436443080970372129249 59793327332310727779096937)
            ·
              refine ⟨44844995499233045834322703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59793327332310727779096937 44844995499233045834322703)
              ·
                refine ⟨67267493248849568751484055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44844995499233045834322703 67267493248849568751484055)
                ·
                  refine ⟨100901239873274353127226083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67267493248849568751484055 100901239873274353127226083)
                  ·
                    refine ⟨151351859809911529690839125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100901239873274353127226083 151351859809911529690839125)
                    ·
                      refine ⟨1773654607147400738564521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 151351859809911529690839125 1773654607147400738564521)
                      ·
                        rfl

theorem cell23_3454180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3454180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454180 prefixEnd_3454180 := by exact prefixLift 3454180
  have htrace : WordTrace (prefixWord ++ tailWord_3454180) baseStart_3454180 baseEnd_3454180 := by
    simpa [prefixWord, tailWord_3454180, baseEnd_3454180] using wordTrace_append hprefix tailTrace_3454180
  have hstable : (prefixWord ++ tailWord_3454180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454180).length < 2 ^ (prefixWord ++ tailWord_3454180).sum := by decide
  have hdescent : baseEnd_3454180 < baseStart_3454180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454181 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_3454181 : Nat := 118140960795 + 3454181 * 2 ^ 59
def prefixEnd_3454181 : Nat := 4983230072969 + 3 ^ 40 * 3454181 * 2
def baseEnd_3454181 : Nat := 591218373542685078217339

theorem tailTrace_3454181 : CollatzResearch.WordTrace tailWord_3454181 prefixEnd_3454181 591218373542685078217339 := by
  unfold tailWord_3454181
  simp only [CollatzResearch.WordTrace]
  refine ⟨125984331099099638993410397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83989554066066425995606931 125984331099099638993410397)
  ·
    refine ⟨47244124162162364622528899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125984331099099638993410397 47244124162162364622528899)
    ·
      refine ⟨70866186243243546933793349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47244124162162364622528899 70866186243243546933793349)
      ·
        refine ⟨13287409920608165050086253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70866186243243546933793349 13287409920608165050086253)
        ·
          refine ⟨4982778720228061893782345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13287409920608165050086253 4982778720228061893782345)
          ·
            refine ⟨3737084040171046420336759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4982778720228061893782345 3737084040171046420336759)
            ·
              refine ⟨5605626060256569630505139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737084040171046420336759 5605626060256569630505139)
              ·
                refine ⟨8408439090384854445757709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605626060256569630505139 8408439090384854445757709)
                ·
                  refine ⟨3153164658894320417159141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8408439090384854445757709 3153164658894320417159141)
                  ·
                    refine ⟨591218373542685078217339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153164658894320417159141 591218373542685078217339)
                    ·
                      rfl

theorem cell23_3454181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_3454181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454181 prefixEnd_3454181 := by exact prefixLift 3454181
  have htrace : WordTrace (prefixWord ++ tailWord_3454181) baseStart_3454181 baseEnd_3454181 := by
    simpa [prefixWord, tailWord_3454181, baseEnd_3454181] using wordTrace_append hprefix tailTrace_3454181
  have hstable : (prefixWord ++ tailWord_3454181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454181).length < 2 ^ (prefixWord ++ tailWord_3454181).sum := by decide
  have hdescent : baseEnd_3454181 < baseStart_3454181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454194 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_3454194 : Nat := 118140960795 + 3454194 * 2 ^ 59
def prefixEnd_3454194 : Nat := 4983230072969 + 3 ^ 40 * 3454194 * 2
def baseEnd_3454194 : Nat := 197073532875173742643273

theorem tailTrace_3454194 : CollatzResearch.WordTrace tailWord_3454194 prefixEnd_3454194 197073532875173742643273 := by
  unfold tailWord_3454194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31496201312013135553408409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83989870165368361475755757 31496201312013135553408409)
  ·
    refine ⟨23622150984009851665056307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31496201312013135553408409 23622150984009851665056307)
    ·
      refine ⟨35433226476014777497584461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23622150984009851665056307 35433226476014777497584461)
      ·
        refine ⟨13287459928505541561594173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35433226476014777497584461 13287459928505541561594173)
        ·
          refine ⟨4982797473189578085597815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13287459928505541561594173 4982797473189578085597815)
          ·
            refine ⟨7474196209784367128396723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982797473189578085597815 7474196209784367128396723)
            ·
              refine ⟨11211294314676550692595085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7474196209784367128396723 11211294314676550692595085)
              ·
                refine ⟨4204235368003706509723157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11211294314676550692595085 4204235368003706509723157)
                ·
                  refine ⟨197073532875173742643273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4204235368003706509723157 197073532875173742643273)
                  ·
                    rfl

theorem cell23_3454194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_3454194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454194 prefixEnd_3454194 := by exact prefixLift 3454194
  have htrace : WordTrace (prefixWord ++ tailWord_3454194) baseStart_3454194 baseEnd_3454194 := by
    simpa [prefixWord, tailWord_3454194, baseEnd_3454194] using wordTrace_append hprefix tailTrace_3454194
  have hstable : (prefixWord ++ tailWord_3454194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454194).length < 2 ^ (prefixWord ++ tailWord_3454194).sum := by decide
  have hdescent : baseEnd_3454194 < baseStart_3454194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454207 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 3, 5]
def baseStart_3454207 : Nat := 118140960795 + 3454207 * 2 ^ 59
def prefixEnd_3454207 : Nat := 4983230072969 + 3 ^ 40 * 3454207 * 2
def baseEnd_3454207 : Nat := 591222823708357377642299

theorem tailTrace_3454207 : CollatzResearch.WordTrace tailWord_3454207 prefixEnd_3454207 591222823708357377642299 := by
  unfold tailWord_3454207
  simp only [CollatzResearch.WordTrace]
  refine ⟨125985279397005445433856875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83990186264670296955904583 125985279397005445433856875)
  ·
    refine ⟨188977919095508168150785313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125985279397005445433856875 188977919095508168150785313)
    ·
      refine ⟨141733439321631126113088985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188977919095508168150785313 141733439321631126113088985)
      ·
        refine ⟨106300079491223344584816739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141733439321631126113088985 106300079491223344584816739)
        ·
          refine ⟨159450119236835016877225109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106300079491223344584816739 159450119236835016877225109)
          ·
            refine ⟨7474224339226641416119927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159450119236835016877225109 7474224339226641416119927)
            ·
              refine ⟨11211336508839962124179891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7474224339226641416119927 11211336508839962124179891)
              ·
                refine ⟨16817004763259943186269837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11211336508839962124179891 16817004763259943186269837)
                ·
                  refine ⟨6306376786222478694851189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16817004763259943186269837 6306376786222478694851189)
                  ·
                    refine ⟨591222823708357377642299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6306376786222478694851189 591222823708357377642299)
                    ·
                      rfl

theorem cell23_3454207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_3454207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454207 prefixEnd_3454207 := by exact prefixLift 3454207
  have htrace : WordTrace (prefixWord ++ tailWord_3454207) baseStart_3454207 baseEnd_3454207 := by
    simpa [prefixWord, tailWord_3454207, baseEnd_3454207] using wordTrace_append hprefix tailTrace_3454207
  have hstable : (prefixWord ++ tailWord_3454207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454207).length < 2 ^ (prefixWord ++ tailWord_3454207).sum := by decide
  have hdescent : baseEnd_3454207 < baseStart_3454207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454261 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_3454261 : Nat := 118140960795 + 3454261 * 2 ^ 59
def prefixEnd_3454261 : Nat := 4983230072969 + 3 ^ 40 * 3454261 * 2
def baseEnd_3454261 : Nat := 1773696199080414921651649

theorem tailTrace_3454261 : CollatzResearch.WordTrace tailWord_3454261 prefixEnd_3454261 1773696199080414921651649 := by
  unfold tailWord_3454261
  simp only [CollatzResearch.WordTrace]
  refine ⟨125987248938809812656322637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83991499292539875104215091 125987248938809812656322637)
  ·
    refine ⟨47245218352053679746120989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125987248938809812656322637 47245218352053679746120989)
    ·
      refine ⟨17716956882020129904795371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47245218352053679746120989 17716956882020129904795371)
      ·
        refine ⟨26575435323030194857193057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17716956882020129904795371 26575435323030194857193057)
        ·
          refine ⟨19931576492272646142894793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26575435323030194857193057 19931576492272646142894793)
          ·
            refine ⟨14948682369204484607171095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19931576492272646142894793 14948682369204484607171095)
            ·
              refine ⟨22423023553806726910756643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14948682369204484607171095 22423023553806726910756643)
              ·
                refine ⟨33634535330710090366134965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22423023553806726910756643 33634535330710090366134965)
                ·
                  refine ⟨3153237687254070971825153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33634535330710090366134965 3153237687254070971825153)
                  ·
                    refine ⟨2364928265440553228868865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3153237687254070971825153 2364928265440553228868865)
                    ·
                      refine ⟨1773696199080414921651649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364928265440553228868865 1773696199080414921651649)
                      ·
                        rfl

theorem cell23_3454261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_3454261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454261 prefixEnd_3454261 := by exact prefixLift 3454261
  have htrace : WordTrace (prefixWord ++ tailWord_3454261) baseStart_3454261 baseEnd_3454261 := by
    simpa [prefixWord, tailWord_3454261, baseEnd_3454261] using wordTrace_append hprefix tailTrace_3454261
  have hstable : (prefixWord ++ tailWord_3454261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454261).length < 2 ^ (prefixWord ++ tailWord_3454261).sum := by decide
  have hdescent : baseEnd_3454261 < baseStart_3454261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454264 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_3454264 : Nat := 118140960795 + 3454264 * 2 ^ 59
def prefixEnd_3454264 : Nat := 4983230072969 + 3 ^ 40 * 3454264 * 2
def baseEnd_3454264 : Nat := 1773697739522378409914135

theorem tailTrace_3454264 : CollatzResearch.WordTrace tailWord_3454264 prefixEnd_3454264 1773697739522378409914135 := by
  unfold tailWord_3454264
  simp only [CollatzResearch.WordTrace]
  refine ⟨62993679178899472084340923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83991572238532629445787897 62993679178899472084340923)
  ·
    refine ⟨94490518768349208126511385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62993679178899472084340923 94490518768349208126511385)
    ·
      refine ⟨70867889076261906094883539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94490518768349208126511385 70867889076261906094883539)
      ·
        refine ⟨106301833614392859142325309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70867889076261906094883539 106301833614392859142325309)
        ·
          refine ⟨39863187605397322178371991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106301833614392859142325309 39863187605397322178371991)
          ·
            refine ⟨59794781408095983267557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39863187605397322178371991 59794781408095983267557987)
            ·
              refine ⟨89692172112143974901336981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59794781408095983267557987 89692172112143974901336981)
              ·
                refine ⟨4204320567756748823500171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89692172112143974901336981 4204320567756748823500171)
                ·
                  refine ⟨6306480851635123235250257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4204320567756748823500171 6306480851635123235250257)
                  ·
                    refine ⟨4729860638726342426437693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6306480851635123235250257 4729860638726342426437693)
                    ·
                      refine ⟨1773697739522378409914135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4729860638726342426437693 1773697739522378409914135)
                      ·
                        rfl

theorem cell23_3454264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_3454264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454264 prefixEnd_3454264 := by exact prefixLift 3454264
  have htrace : WordTrace (prefixWord ++ tailWord_3454264) baseStart_3454264 baseEnd_3454264 := by
    simpa [prefixWord, tailWord_3454264, baseEnd_3454264] using wordTrace_append hprefix tailTrace_3454264
  have hstable : (prefixWord ++ tailWord_3454264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454264).length < 2 ^ (prefixWord ++ tailWord_3454264).sum := by decide
  have hdescent : baseEnd_3454264 < baseStart_3454264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454265 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3454265 : Nat := 118140960795 + 3454265 * 2 ^ 59
def prefixEnd_3454265 : Nat := 4983230072969 + 3 ^ 40 * 3454265 * 2
def baseEnd_3454265 : Nat := 1773698253003032906001631

theorem tailTrace_3454265 : CollatzResearch.WordTrace tailWord_3454265 prefixEnd_3454265 1773698253003032906001631 := by
  unfold tailWord_3454265
  simp only [CollatzResearch.WordTrace]
  refine ⟨125987394830795321339468249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83991596553863547559645499 125987394830795321339468249)
  ·
    refine ⟨94490546123096491004601187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125987394830795321339468249 94490546123096491004601187)
    ·
      refine ⟨141735819184644736506901781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94490546123096491004601187 141735819184644736506901781)
      ·
        refine ⟨6643866524280222023761021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141735819184644736506901781 6643866524280222023761021)
        ·
          refine ⟨2491449946605083258910383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6643866524280222023761021 2491449946605083258910383)
          ·
            refine ⟨3737174919907624888365575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491449946605083258910383 3737174919907624888365575)
            ·
              refine ⟨5605762379861437332548363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737174919907624888365575 5605762379861437332548363)
              ·
                refine ⟨8408643569792155998822545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605762379861437332548363 8408643569792155998822545)
                ·
                  refine ⟨6306482677344116999116909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8408643569792155998822545 6306482677344116999116909)
                  ·
                    refine ⟨2364931004004043874668841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6306482677344116999116909 2364931004004043874668841)
                    ·
                      refine ⟨1773698253003032906001631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364931004004043874668841 1773698253003032906001631)
                      ·
                        rfl

theorem cell23_3454265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3454265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454265 prefixEnd_3454265 := by exact prefixLift 3454265
  have htrace : WordTrace (prefixWord ++ tailWord_3454265) baseStart_3454265 baseEnd_3454265 := by
    simpa [prefixWord, tailWord_3454265, baseEnd_3454265] using wordTrace_append hprefix tailTrace_3454265
  have hstable : (prefixWord ++ tailWord_3454265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454265).length < 2 ^ (prefixWord ++ tailWord_3454265).sum := by decide
  have hdescent : baseEnd_3454265 < baseStart_3454265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454281 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 1, 2, 3]
def baseStart_3454281 : Nat := 118140960795 + 3454281 * 2 ^ 59
def prefixEnd_3454281 : Nat := 4983230072969 + 3 ^ 40 * 3454281 * 2
def baseEnd_3454281 : Nat := 1773706468693504843401557

theorem tailTrace_3454281 : CollatzResearch.WordTrace tailWord_3454281 prefixEnd_3454281 1773706468693504843401557 := by
  unfold tailWord_3454281
  simp only [CollatzResearch.WordTrace]
  refine ⟨125987978398737356072050697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83991985599158237381367131 125987978398737356072050697)
  ·
    refine ⟨94490983799053017054038023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125987978398737356072050697 94490983799053017054038023)
    ·
      refine ⟨141736475698579525581057035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94490983799053017054038023 141736475698579525581057035)
      ·
        refine ⟨212604713547869288371585553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141736475698579525581057035 212604713547869288371585553)
        ·
          refine ⟨159453535160901966278689165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212604713547869288371585553 159453535160901966278689165)
          ·
            refine ⟨59795075685338237354508437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159453535160901966278689165 59795075685338237354508437)
            ·
              refine ⟨2802894172750229875992583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59795075685338237354508437 2802894172750229875992583)
              ·
                refine ⟨4204341259125344813988875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802894172750229875992583 4204341259125344813988875)
                ·
                  refine ⟨6306511888688017220983313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4204341259125344813988875 6306511888688017220983313)
                  ·
                    refine ⟨4729883916516012915737485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6306511888688017220983313 4729883916516012915737485)
                    ·
                      refine ⟨1773706468693504843401557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4729883916516012915737485 1773706468693504843401557)
                      ·
                        rfl

theorem cell23_3454281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 2, 3].length) (baseStart_3454281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454281 prefixEnd_3454281 := by exact prefixLift 3454281
  have htrace : WordTrace (prefixWord ++ tailWord_3454281) baseStart_3454281 baseEnd_3454281 := by
    simpa [prefixWord, tailWord_3454281, baseEnd_3454281] using wordTrace_append hprefix tailTrace_3454281
  have hstable : (prefixWord ++ tailWord_3454281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454281).length < 2 ^ (prefixWord ++ tailWord_3454281).sum := by decide
  have hdescent : baseEnd_3454281 < baseStart_3454281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454318 : List Nat := [4, 1, 2, 4, 1, 2, 2, 7]
def baseStart_3454318 : Nat := 118140960795 + 3454318 * 2 ^ 59
def prefixEnd_3454318 : Nat := 4983230072969 + 3 ^ 40 * 3454318 * 2
def baseEnd_3454318 : Nat := 65693535832508192542181

theorem tailTrace_3454318 : CollatzResearch.WordTrace tailWord_3454318 prefixEnd_3454318 65693535832508192542181 := by
  unfold tailWord_3454318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748665987450413923893451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83992885266402207594098405 15748665987450413923893451)
  ·
    refine ⟨23622998981175620885840177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15748665987450413923893451 23622998981175620885840177)
    ·
      refine ⟨17717249235881715664380133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23622998981175620885840177 17717249235881715664380133)
      ·
        refine ⟨3321984231727821687071275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17717249235881715664380133 3321984231727821687071275)
        ·
          refine ⟨4982976347591732530606913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321984231727821687071275 4982976347591732530606913)
          ·
            refine ⟨3737232260693799397955185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4982976347591732530606913 3737232260693799397955185)
            ·
              refine ⟨2802924195520349548466389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3737232260693799397955185 2802924195520349548466389)
              ·
                refine ⟨65693535832508192542181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2802924195520349548466389 65693535832508192542181)
                ·
                  rfl

theorem cell23_3454318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_3454318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454318 prefixEnd_3454318 := by exact prefixLift 3454318
  have htrace : WordTrace (prefixWord ++ tailWord_3454318) baseStart_3454318 baseEnd_3454318 := by
    simpa [prefixWord, tailWord_3454318, baseEnd_3454318] using wordTrace_append hprefix tailTrace_3454318
  have hstable : (prefixWord ++ tailWord_3454318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454318).length < 2 ^ (prefixWord ++ tailWord_3454318).sum := by decide
  have hdescent : baseEnd_3454318 < baseStart_3454318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454321 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 1, 3, 2]
def baseStart_3454321 : Nat := 118140960795 + 3454321 * 2 ^ 59
def prefixEnd_3454321 : Nat := 4983230072969 + 3 ^ 40 * 3454321 * 2
def baseEnd_3454321 : Nat := 1773727007919684686901373

theorem tailTrace_3454321 : CollatzResearch.WordTrace tailWord_3454321 prefixEnd_3454321 1773727007919684686901373 := by
  unfold tailWord_3454321
  simp only [CollatzResearch.WordTrace]
  refine ⟨125989437318592442903506817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83992958212394961935671211 125989437318592442903506817)
  ·
    refine ⟨94492077988944332177630113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125989437318592442903506817 94492077988944332177630113)
    ·
      refine ⟨70869058491708249133222585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94492077988944332177630113 70869058491708249133222585)
      ·
        refine ⟨53151793868781186849916939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70869058491708249133222585 53151793868781186849916939)
        ·
          refine ⟨79727690803171780274875409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53151793868781186849916939 79727690803171780274875409)
          ·
            refine ⟨59795768102378835206156557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79727690803171780274875409 59795768102378835206156557)
            ·
              refine ⟨22423413038392063202308709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59795768102378835206156557 22423413038392063202308709)
              ·
                refine ⟨4204389944698511850432883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22423413038392063202308709 4204389944698511850432883)
                ·
                  refine ⟨6306584917047767775649325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4204389944698511850432883 6306584917047767775649325)
                  ·
                    refine ⟨2364969343892912915868497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6306584917047767775649325 2364969343892912915868497)
                    ·
                      refine ⟨1773727007919684686901373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364969343892912915868497 1773727007919684686901373)
                      ·
                        rfl

theorem cell23_3454321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_3454321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454321 prefixEnd_3454321 := by exact prefixLift 3454321
  have htrace : WordTrace (prefixWord ++ tailWord_3454321) baseStart_3454321 baseEnd_3454321 := by
    simpa [prefixWord, tailWord_3454321, baseEnd_3454321] using wordTrace_append hprefix tailTrace_3454321
  have hstable : (prefixWord ++ tailWord_3454321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454321).length < 2 ^ (prefixWord ++ tailWord_3454321).sum := by decide
  have hdescent : baseEnd_3454321 < baseStart_3454321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454368 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 2, 2, 2]
def baseStart_3454368 : Nat := 118140960795 + 3454368 * 2 ^ 59
def prefixEnd_3454368 : Nat := 4983230072969 + 3 ^ 40 * 3454368 * 2
def baseEnd_3454368 : Nat := 1773751141510446003013657

theorem tailTrace_3454368 : CollatzResearch.WordTrace tailWord_3454368 prefixEnd_3454368 1773751141510446003013657 := by
  unfold tailWord_3454368
  simp only [CollatzResearch.WordTrace]
  refine ⟨62995575774711084965233879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83994101032948113286978505 62995575774711084965233879)
  ·
    refine ⟨94493363662066627447850819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62995575774711084965233879 94493363662066627447850819)
    ·
      refine ⟨141740045493099941171776229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94493363662066627447850819 141740045493099941171776229)
      ·
        refine ⟨26576258529956238969708043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141740045493099941171776229 26576258529956238969708043)
        ·
          refine ⟨39864387794934358454562065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26576258529956238969708043 39864387794934358454562065)
          ·
            refine ⟨29898290846200768840921549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39864387794934358454562065 29898290846200768840921549)
            ·
              refine ⟨11211859067325288315345581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29898290846200768840921549 11211859067325288315345581)
              ·
                refine ⟨4204447150246983118254593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11211859067325288315345581 4204447150246983118254593)
                ·
                  refine ⟨3153335362685237338690945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204447150246983118254593 3153335362685237338690945)
                  ·
                    refine ⟨2365001522013928004018209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3153335362685237338690945 2365001522013928004018209)
                    ·
                      refine ⟨1773751141510446003013657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365001522013928004018209 1773751141510446003013657)
                      ·
                        rfl

theorem cell23_3454368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_3454368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454368 prefixEnd_3454368 := by exact prefixLift 3454368
  have htrace : WordTrace (prefixWord ++ tailWord_3454368) baseStart_3454368 baseEnd_3454368 := by
    simpa [prefixWord, tailWord_3454368, baseEnd_3454368] using wordTrace_append hprefix tailTrace_3454368
  have hstable : (prefixWord ++ tailWord_3454368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454368).length < 2 ^ (prefixWord ++ tailWord_3454368).sum := by decide
  have hdescent : baseEnd_3454368 < baseStart_3454368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454387 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 1, 7]
def baseStart_3454387 : Nat := 118140960795 + 3454387 * 2 ^ 59
def prefixEnd_3454387 : Nat := 4983230072969 + 3 ^ 40 * 3454387 * 2
def baseEnd_3454387 : Nat := 591253632547627142892023

theorem tailTrace_3454387 : CollatzResearch.WordTrace tailWord_3454387 prefixEnd_3454387 591253632547627142892023 := by
  unfold tailWord_3454387
  simp only [CollatzResearch.WordTrace]
  refine ⟨125991844536353336175409415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83994563024235557450272943 125991844536353336175409415)
  ·
    refine ⟨188987766804530004263114123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125991844536353336175409415 188987766804530004263114123)
    ·
      refine ⟨283481650206795006394671185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188987766804530004263114123 283481650206795006394671185)
      ·
        refine ⟨212611237655096254796003389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283481650206795006394671185 212611237655096254796003389)
        ·
          refine ⟨79729214120661095548501271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212611237655096254796003389 79729214120661095548501271)
          ·
            refine ⟨119593821180991643322751907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79729214120661095548501271 119593821180991643322751907)
            ·
              refine ⟨179390731771487464984127861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119593821180991643322751907 179390731771487464984127861)
              ·
                refine ⟨16817881103576949842261987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179390731771487464984127861 16817881103576949842261987)
                ·
                  refine ⟨25226821655365424763392981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16817881103576949842261987 25226821655365424763392981)
                  ·
                    refine ⟨591253632547627142892023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25226821655365424763392981 591253632547627142892023)
                    ·
                      rfl

theorem cell23_3454387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 7].length) (baseStart_3454387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454387 prefixEnd_3454387 := by exact prefixLift 3454387
  have htrace : WordTrace (prefixWord ++ tailWord_3454387) baseStart_3454387 baseEnd_3454387 := by
    simpa [prefixWord, tailWord_3454387, baseEnd_3454387] using wordTrace_append hprefix tailTrace_3454387
  have hstable : (prefixWord ++ tailWord_3454387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454387).length < 2 ^ (prefixWord ++ tailWord_3454387).sum := by decide
  have hdescent : baseEnd_3454387 < baseStart_3454387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454414 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3454414 : Nat := 118140960795 + 3454414 * 2 ^ 59
def prefixEnd_3454414 : Nat := 4983230072969 + 3 ^ 40 * 3454414 * 2
def baseEnd_3454414 : Nat := 1773774761620552823038445

theorem tailTrace_3454414 : CollatzResearch.WordTrace tailWord_3454414 prefixEnd_3454414 1773774761620552823038445 := by
  unfold tailWord_3454414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15749103663406939973330287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83995219538170346524428197 15749103663406939973330287)
  ·
    refine ⟨23623655495110409959995431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15749103663406939973330287 23623655495110409959995431)
    ·
      refine ⟨35435483242665614939993147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23623655495110409959995431 35435483242665614939993147)
      ·
        refine ⟨53153224863998422409989721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35435483242665614939993147 53153224863998422409989721)
        ·
          refine ⟨39864918647998816807492291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53153224863998422409989721 39864918647998816807492291)
          ·
            refine ⟨59797377971998225211238437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39864918647998816807492291 59797377971998225211238437)
            ·
              refine ⟨11212008369749667227107207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59797377971998225211238437 11212008369749667227107207)
              ·
                refine ⟨16818012554624500840660811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11212008369749667227107207 16818012554624500840660811)
                ·
                  refine ⟨25227018831936751260991217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16818012554624500840660811 25227018831936751260991217)
                  ·
                    refine ⟨18920264123952563445743413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25227018831936751260991217 18920264123952563445743413)
                    ·
                      refine ⟨1773774761620552823038445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18920264123952563445743413 1773774761620552823038445)
                      ·
                        rfl

theorem cell23_3454414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3454414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454414 prefixEnd_3454414 := by exact prefixLift 3454414
  have htrace : WordTrace (prefixWord ++ tailWord_3454414) baseStart_3454414 baseEnd_3454414 := by
    simpa [prefixWord, tailWord_3454414, baseEnd_3454414] using wordTrace_append hprefix tailTrace_3454414
  have hstable : (prefixWord ++ tailWord_3454414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454414).length < 2 ^ (prefixWord ++ tailWord_3454414).sum := by decide
  have hdescent : baseEnd_3454414 < baseStart_3454414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454417 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3454417 : Nat := 118140960795 + 3454417 * 2 ^ 59
def prefixEnd_3454417 : Nat := 4983230072969 + 3 ^ 40 * 3454417 * 2
def baseEnd_3454417 : Nat := 591258767354172103766977

theorem tailTrace_3454417 : CollatzResearch.WordTrace tailWord_3454417 prefixEnd_3454417 591258767354172103766977 := by
  unfold tailWord_3454417
  simp only [CollatzResearch.WordTrace]
  refine ⟨125992938726244651299001505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83995292484163100866001003 125992938726244651299001505)
  ·
    refine ⟨94494704044683488474251129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125992938726244651299001505 94494704044683488474251129)
    ·
      refine ⟨70871028033512616355688347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94494704044683488474251129 70871028033512616355688347)
      ·
        refine ⟨106306542050268924533532521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70871028033512616355688347 106306542050268924533532521)
        ·
          refine ⟨79729906537701693400149391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106306542050268924533532521 79729906537701693400149391)
          ·
            refine ⟨119594859806552540100224087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79729906537701693400149391 119594859806552540100224087)
            ·
              refine ⟨179392289709828810150336131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119594859806552540100224087 179392289709828810150336131)
              ·
                refine ⟨269088434564743215225504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179392289709828810150336131 269088434564743215225504197)
                ·
                  refine ⟨50454081480889352854782037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269088434564743215225504197 50454081480889352854782037)
                  ·
                    refine ⟨591258767354172103766977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50454081480889352854782037 591258767354172103766977)
                    ·
                      rfl

theorem cell23_3454417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3454417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454417 prefixEnd_3454417 := by exact prefixLift 3454417
  have htrace : WordTrace (prefixWord ++ tailWord_3454417) baseStart_3454417 baseEnd_3454417 := by
    simpa [prefixWord, tailWord_3454417, baseEnd_3454417] using wordTrace_append hprefix tailTrace_3454417
  have hstable : (prefixWord ++ tailWord_3454417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454417).length < 2 ^ (prefixWord ++ tailWord_3454417).sum := by decide
  have hdescent : baseEnd_3454417 < baseStart_3454417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454424 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_3454424 : Nat := 118140960795 + 3454424 * 2 ^ 59
def prefixEnd_3454424 : Nat := 4983230072969 + 3 ^ 40 * 3454424 * 2
def baseEnd_3454424 : Nat := 1773779896427097783913399

theorem tailTrace_3454424 : CollatzResearch.WordTrace tailWord_3454424 prefixEnd_3454424 1773779896427097783913399 := by
  unfold tailWord_3454424
  simp only [CollatzResearch.WordTrace]
  refine ⟨62996597018609645747253163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83995462691479527663004217 62996597018609645747253163)
  ·
    refine ⟨94494895527914468620879745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62996597018609645747253163 94494895527914468620879745)
    ·
      refine ⟨70871171645935851465659809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94494895527914468620879745 70871171645935851465659809)
      ·
        refine ⟨53153378734451888599244857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70871171645935851465659809 53153378734451888599244857)
        ·
          refine ⟨39865034050838916449433643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53153378734451888599244857 39865034050838916449433643)
          ·
            refine ⟨59797551076258374674150465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39865034050838916449433643 59797551076258374674150465)
            ·
              refine ⟨44848163307193781005612849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59797551076258374674150465 44848163307193781005612849)
              ·
                refine ⟨33636122480395335754209637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44848163307193781005612849 33636122480395335754209637)
                ·
                  refine ⟨6306772965074125453914307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33636122480395335754209637 6306772965074125453914307)
                  ·
                    refine ⟨9460159447611188180871461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6306772965074125453914307 9460159447611188180871461)
                    ·
                      refine ⟨1773779896427097783913399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9460159447611188180871461 1773779896427097783913399)
                      ·
                        rfl

theorem cell23_3454424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_3454424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454424 prefixEnd_3454424 := by exact prefixLift 3454424
  have htrace : WordTrace (prefixWord ++ tailWord_3454424) baseStart_3454424 baseEnd_3454424 := by
    simpa [prefixWord, tailWord_3454424, baseEnd_3454424] using wordTrace_append hprefix tailTrace_3454424
  have hstable : (prefixWord ++ tailWord_3454424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454424).length < 2 ^ (prefixWord ++ tailWord_3454424).sum := by decide
  have hdescent : baseEnd_3454424 < baseStart_3454424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454481 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 6]
def baseStart_3454481 : Nat := 118140960795 + 3454481 * 2 ^ 59
def prefixEnd_3454481 : Nat := 4983230072969 + 3 ^ 40 * 3454481 * 2
def baseEnd_3454481 : Nat := 197089907202711562322293

theorem tailTrace_3454481 : CollatzResearch.WordTrace tailWord_3454481 prefixEnd_3454481 197089907202711562322293 := by
  unfold tailWord_3454481
  simp only [CollatzResearch.WordTrace]
  refine ⟨125995272998012790229331297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83996848665341860152887531 125995272998012790229331297)
  ·
    refine ⟨94496454748509592671998473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125995272998012790229331297 94496454748509592671998473)
    ·
      refine ⟨70872341061382194503998855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94496454748509592671998473 70872341061382194503998855)
      ·
        refine ⟨106308511592073291755998283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70872341061382194503998855 106308511592073291755998283)
        ·
          refine ⟨159462767388109937633997425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106308511592073291755998283 159462767388109937633997425)
          ·
            refine ⟨119597075541082453225498069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159462767388109937633997425 119597075541082453225498069)
            ·
              refine ⟨2803056457994119997472611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119597075541082453225498069 2803056457994119997472611)
              ·
                refine ⟨4204584686991179996208917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803056457994119997472611 4204584686991179996208917)
                ·
                  refine ⟨197089907202711562322293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4204584686991179996208917 197089907202711562322293)
                  ·
                    rfl

theorem cell23_3454481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 6].length) (baseStart_3454481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454481 prefixEnd_3454481 := by exact prefixLift 3454481
  have htrace : WordTrace (prefixWord ++ tailWord_3454481) baseStart_3454481 baseEnd_3454481 := by
    simpa [prefixWord, tailWord_3454481, baseEnd_3454481] using wordTrace_append hprefix tailTrace_3454481
  have hstable : (prefixWord ++ tailWord_3454481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454481).length < 2 ^ (prefixWord ++ tailWord_3454481).sum := by decide
  have hdescent : baseEnd_3454481 < baseStart_3454481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454544 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_3454544 : Nat := 118140960795 + 3454544 * 2 ^ 59
def prefixEnd_3454544 : Nat := 4983230072969 + 3 ^ 40 * 3454544 * 2
def baseEnd_3454544 : Nat := 1773841514105637314412847

theorem tailTrace_3454544 : CollatzResearch.WordTrace tailWord_3454544 prefixEnd_3454544 1773841514105637314412847 := by
  unfold tailWord_3454544
  simp only [CollatzResearch.WordTrace]
  refine ⟨62998785398392275994437343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83998380531189701325916457 62998785398392275994437343)
  ·
    refine ⟨94498178097588413991656015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62998785398392275994437343 94498178097588413991656015)
    ·
      refine ⟨141747267146382620987484023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94498178097588413991656015 141747267146382620987484023)
      ·
        refine ⟨212620900719573931481226035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141747267146382620987484023 212620900719573931481226035)
        ·
          refine ⟨318931351079360897221839053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212620900719573931481226035 318931351079360897221839053)
          ·
            refine ⟨119599256654760336458189645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318931351079360897221839053 119599256654760336458189645)
            ·
              refine ⟨44849721245535126171821117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119599256654760336458189645 44849721245535126171821117)
              ·
                refine ⟨16818645467075672314432919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44849721245535126171821117 16818645467075672314432919)
                ·
                  refine ⟨25227968200613508471649379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16818645467075672314432919 25227968200613508471649379)
                  ·
                    refine ⟨37841952300920262707474069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25227968200613508471649379 37841952300920262707474069)
                    ·
                      refine ⟨1773841514105637314412847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37841952300920262707474069 1773841514105637314412847)
                      ·
                        rfl

theorem cell23_3454544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_3454544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454544 prefixEnd_3454544 := by exact prefixLift 3454544
  have htrace : WordTrace (prefixWord ++ tailWord_3454544) baseStart_3454544 baseEnd_3454544 := by
    simpa [prefixWord, tailWord_3454544, baseEnd_3454544] using wordTrace_append hprefix tailTrace_3454544
  have hstable : (prefixWord ++ tailWord_3454544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454544).length < 2 ^ (prefixWord ++ tailWord_3454544).sum := by decide
  have hdescent : baseEnd_3454544 < baseStart_3454544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454561 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3454561 : Nat := 118140960795 + 3454561 * 2 ^ 59
def prefixEnd_3454561 : Nat := 4983230072969 + 3 ^ 40 * 3454561 * 2
def baseEnd_3454561 : Nat := 1773850243276763747900269

theorem tailTrace_3454561 : CollatzResearch.WordTrace tailWord_3454561 prefixEnd_3454561 1773850243276763747900269 := by
  unfold tailWord_3454561
  simp only [CollatzResearch.WordTrace]
  refine ⟨125998190837722963892243537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83998793891815309261495691 125998190837722963892243537)
  ·
    refine ⟨94498643128292222919182653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125998190837722963892243537 94498643128292222919182653)
    ·
      refine ⟨35436991173109583594693495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94498643128292222919182653 35436991173109583594693495)
      ·
        refine ⟨53155486759664375392040243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35436991173109583594693495 53155486759664375392040243)
        ·
          refine ⟨79733230139496563088060365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53155486759664375392040243 79733230139496563088060365)
          ·
            refine ⟨29899961302311211158022637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79733230139496563088060365 29899961302311211158022637)
            ·
              refine ⟨11212485488366704184258489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29899961302311211158022637 11212485488366704184258489)
              ·
                refine ⟨8409364116275028138193867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11212485488366704184258489 8409364116275028138193867)
                ·
                  refine ⟨12614046174412542207290801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8409364116275028138193867 12614046174412542207290801)
                  ·
                    refine ⟨9460534630809406655468101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12614046174412542207290801 9460534630809406655468101)
                    ·
                      refine ⟨1773850243276763747900269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9460534630809406655468101 1773850243276763747900269)
                      ·
                        rfl

theorem cell23_3454561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3454561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454561 prefixEnd_3454561 := by exact prefixLift 3454561
  have htrace : WordTrace (prefixWord ++ tailWord_3454561) baseStart_3454561 baseEnd_3454561 := by
    simpa [prefixWord, tailWord_3454561, baseEnd_3454561] using wordTrace_append hprefix tailTrace_3454561
  have hstable : (prefixWord ++ tailWord_3454561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454561).length < 2 ^ (prefixWord ++ tailWord_3454561).sum := by decide
  have hdescent : baseEnd_3454561 < baseStart_3454561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454565 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 1, 1, 4]
def baseStart_3454565 : Nat := 118140960795 + 3454565 * 2 ^ 59
def prefixEnd_3454565 : Nat := 4983230072969 + 3 ^ 40 * 3454565 * 2
def baseEnd_3454565 : Nat := 1773852297199381732250251

theorem tailTrace_3454565 : CollatzResearch.WordTrace tailWord_3454565 prefixEnd_3454565 1773852297199381732250251 := by
  unfold tailWord_3454565
  simp only [CollatzResearch.WordTrace]
  refine ⟨125998336729708472575389149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83998891153138981716926099 125998336729708472575389149)
  ·
    refine ⟨47249376273640677215770931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125998336729708472575389149 47249376273640677215770931)
    ·
      refine ⟨70874064410461015823656397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47249376273640677215770931 70874064410461015823656397)
      ·
        refine ⟨26577774153922880933871149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70874064410461015823656397 26577774153922880933871149)
        ·
          refine ⟨9966665307721080350201681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26577774153922880933871149 9966665307721080350201681)
          ·
            refine ⟨7474998980790810262651261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9966665307721080350201681 7474998980790810262651261)
            ·
              refine ⟨2803124617796553848494223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7474998980790810262651261 2803124617796553848494223)
              ·
                refine ⟨4204686926694830772741335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803124617796553848494223 4204686926694830772741335)
                ·
                  refine ⟨6307030390042246159112003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4204686926694830772741335 6307030390042246159112003)
                  ·
                    refine ⟨9460545585063369238668005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6307030390042246159112003 9460545585063369238668005)
                    ·
                      refine ⟨1773852297199381732250251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9460545585063369238668005 1773852297199381732250251)
                      ·
                        rfl

theorem cell23_3454565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_3454565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454565 prefixEnd_3454565 := by exact prefixLift 3454565
  have htrace : WordTrace (prefixWord ++ tailWord_3454565) baseStart_3454565 baseEnd_3454565 := by
    simpa [prefixWord, tailWord_3454565, baseEnd_3454565] using wordTrace_append hprefix tailTrace_3454565
  have hstable : (prefixWord ++ tailWord_3454565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454565).length < 2 ^ (prefixWord ++ tailWord_3454565).sum := by decide
  have hdescent : baseEnd_3454565 < baseStart_3454565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454568 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3454568 : Nat := 118140960795 + 3454568 * 2 ^ 59
def prefixEnd_3454568 : Nat := 4983230072969 + 3 ^ 40 * 3454568 * 2
def baseEnd_3454568 : Nat := 1773853837641345220512737

theorem tailTrace_3454568 : CollatzResearch.WordTrace tailWord_3454568 prefixEnd_3454568 1773853837641345220512737 := by
  unfold tailWord_3454568
  simp only [CollatzResearch.WordTrace]
  refine ⟨62999223074348802043874179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83998964099131736058498905 62999223074348802043874179)
  ·
    refine ⟨94498834611523203065811269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62999223074348802043874179 94498834611523203065811269)
    ·
      refine ⟨17718531489660600574839613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94498834611523203065811269 17718531489660600574839613)
      ·
        refine ⟨6644449308622725215564855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17718531489660600574839613 6644449308622725215564855)
        ·
          refine ⟨9966673962934087823347283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644449308622725215564855 9966673962934087823347283)
          ·
            refine ⟨14950010944401131735020925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966673962934087823347283 14950010944401131735020925)
            ·
              refine ⟨5606254104150424400632847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14950010944401131735020925 5606254104150424400632847)
              ·
                refine ⟨8409381156225636600949271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606254104150424400632847 8409381156225636600949271)
                ·
                  refine ⟨12614071734338454901423907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8409381156225636600949271 12614071734338454901423907)
                  ·
                    refine ⟨18921107601507682352135861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12614071734338454901423907 18921107601507682352135861)
                    ·
                      refine ⟨1773853837641345220512737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18921107601507682352135861 1773853837641345220512737)
                      ·
                        rfl

theorem cell23_3454568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3454568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454568 prefixEnd_3454568 := by exact prefixLift 3454568
  have htrace : WordTrace (prefixWord ++ tailWord_3454568) baseStart_3454568 baseEnd_3454568 := by
    simpa [prefixWord, tailWord_3454568, baseEnd_3454568] using wordTrace_append hprefix tailTrace_3454568
  have hstable : (prefixWord ++ tailWord_3454568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454568).length < 2 ^ (prefixWord ++ tailWord_3454568).sum := by decide
  have hdescent : baseEnd_3454568 < baseStart_3454568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454671 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_3454671 : Nat := 118140960795 + 3454671 * 2 ^ 59
def prefixEnd_3454671 : Nat := 4983230072969 + 3 ^ 40 * 3454671 * 2
def baseEnd_3454671 : Nat := 1773906726148758317524763

theorem tailTrace_3454671 : CollatzResearch.WordTrace tailWord_3454671 prefixEnd_3454671 1773906726148758317524763 := by
  unfold tailWord_3454671
  simp only [CollatzResearch.WordTrace]
  refine ⟨126002202867324452678747867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84001468578216301785831911 126002202867324452678747867)
  ·
    refine ⟨189003304300986679018121801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126002202867324452678747867 189003304300986679018121801)
    ·
      refine ⟨141752478225740009263591351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189003304300986679018121801 141752478225740009263591351)
      ·
        refine ⟨212628717338610013895387027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141752478225740009263591351 212628717338610013895387027)
        ·
          refine ⟨318943076007915020843080541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212628717338610013895387027 318943076007915020843080541)
          ·
            refine ⟨119603653502968132816155203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318943076007915020843080541 119603653502968132816155203)
            ·
              refine ⟨179405480254452199224232805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119603653502968132816155203 179405480254452199224232805)
              ·
                refine ⟨33638527547709787354543651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179405480254452199224232805 33638527547709787354543651)
                ·
                  refine ⟨50457791321564681031815477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33638527547709787354543651 50457791321564681031815477)
                  ·
                    refine ⟨4730417936396688846732701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50457791321564681031815477 4730417936396688846732701)
                    ·
                      refine ⟨1773906726148758317524763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4730417936396688846732701 1773906726148758317524763)
                      ·
                        rfl

theorem cell23_3454671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_3454671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454671 prefixEnd_3454671 := by exact prefixLift 3454671
  have htrace : WordTrace (prefixWord ++ tailWord_3454671) baseStart_3454671 baseEnd_3454671 := by
    simpa [prefixWord, tailWord_3454671, baseEnd_3454671] using wordTrace_append hprefix tailTrace_3454671
  have hstable : (prefixWord ++ tailWord_3454671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454671).length < 2 ^ (prefixWord ++ tailWord_3454671).sum := by decide
  have hdescent : baseEnd_3454671 < baseStart_3454671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454711 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_3454711 : Nat := 118140960795 + 3454711 * 2 ^ 59
def prefixEnd_3454711 : Nat := 4983230072969 + 3 ^ 40 * 3454711 * 2
def baseEnd_3454711 : Nat := 1773927265374938161024579

theorem tailTrace_3454711 : CollatzResearch.WordTrace tailWord_3454711 prefixEnd_3454711 1773927265374938161024579 := by
  unfold tailWord_3454711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126003661787179539510203987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84002441191453026340135991 126003661787179539510203987)
  ·
    refine ⟨189005492680769309265305981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126003661787179539510203987 189005492680769309265305981)
    ·
      refine ⟨70877059755288490974489743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189005492680769309265305981 70877059755288490974489743)
      ·
        refine ⟨106315589632932736461734615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70877059755288490974489743 106315589632932736461734615)
        ·
          refine ⟨159473384449399104692601923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106315589632932736461734615 159473384449399104692601923)
          ·
            refine ⟨239210076674098657038902885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159473384449399104692601923 239210076674098657038902885)
            ·
              refine ⟨44851889376393498194794291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239210076674098657038902885 44851889376393498194794291)
              ·
                refine ⟨67277834064590247292191437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44851889376393498194794291 67277834064590247292191437)
                ·
                  refine ⟨25229187774221342734571789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67277834064590247292191437 25229187774221342734571789)
                  ·
                    refine ⟨9460945415333003525464421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25229187774221342734571789 9460945415333003525464421)
                    ·
                      refine ⟨1773927265374938161024579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9460945415333003525464421 1773927265374938161024579)
                      ·
                        rfl

theorem cell23_3454711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_3454711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454711 prefixEnd_3454711 := by exact prefixLift 3454711
  have htrace : WordTrace (prefixWord ++ tailWord_3454711) baseStart_3454711 baseEnd_3454711 := by
    simpa [prefixWord, tailWord_3454711, baseEnd_3454711] using wordTrace_append hprefix tailTrace_3454711
  have hstable : (prefixWord ++ tailWord_3454711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454711).length < 2 ^ (prefixWord ++ tailWord_3454711).sum := by decide
  have hdescent : baseEnd_3454711 < baseStart_3454711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454721 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3454721 : Nat := 118140960795 + 3454721 * 2 ^ 59
def prefixEnd_3454721 : Nat := 4983230072969 + 3 ^ 40 * 3454721 * 2
def baseEnd_3454721 : Nat := 591310800060494373966511

theorem tailTrace_3454721 : CollatzResearch.WordTrace tailWord_3454721 prefixEnd_3454721 591310800060494373966511 := by
  unfold tailWord_3454721
  simp only [CollatzResearch.WordTrace]
  refine ⟨126004026517143311218068017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84002684344762207478712011 126004026517143311218068017)
  ·
    refine ⟨94503019887857483413551013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126004026517143311218068017 94503019887857483413551013)
    ·
      refine ⟨17719316228973278140040815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94503019887857483413551013 17719316228973278140040815)
      ·
        refine ⟨26578974343459917210061223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17719316228973278140040815 26578974343459917210061223)
        ·
          refine ⟨39868461515189875815091835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26578974343459917210061223 39868461515189875815091835)
          ·
            refine ⟨59802692272784813722637753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39868461515189875815091835 59802692272784813722637753)
            ·
              refine ⟨44852019204588610291978315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59802692272784813722637753 44852019204588610291978315)
              ·
                refine ⟨67278028806882915437967473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44852019204588610291978315 67278028806882915437967473)
                ·
                  refine ⟨50458521605162186578475605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67278028806882915437967473 50458521605162186578475605)
                  ·
                    refine ⟨591310800060494373966511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50458521605162186578475605 591310800060494373966511)
                    ·
                      rfl

theorem cell23_3454721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3454721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454721 prefixEnd_3454721 := by exact prefixLift 3454721
  have htrace : WordTrace (prefixWord ++ tailWord_3454721) baseStart_3454721 baseEnd_3454721 := by
    simpa [prefixWord, tailWord_3454721, baseEnd_3454721] using wordTrace_append hprefix tailTrace_3454721
  have hstable : (prefixWord ++ tailWord_3454721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454721).length < 2 ^ (prefixWord ++ tailWord_3454721).sum := by decide
  have hdescent : baseEnd_3454721 < baseStart_3454721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454772 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3454772 : Nat := 118140960795 + 3454772 * 2 ^ 59
def prefixEnd_3454772 : Nat := 4983230072969 + 3 ^ 40 * 3454772 * 2
def baseEnd_3454772 : Nat := 591319529231620807453933

theorem tailTrace_3454772 : CollatzResearch.WordTrace tailWord_3454772 prefixEnd_3454772 591319529231620807453933 := by
  unfold tailWord_3454772
  simp only [CollatzResearch.WordTrace]
  refine ⟨63002943319979273464087285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84003924426639031285449713 63002943319979273464087285)
  ·
    refine ⟨5906525936248056887258183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63002943319979273464087285 5906525936248056887258183)
    ·
      refine ⟨8859788904372085330887275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5906525936248056887258183 8859788904372085330887275)
      ·
        refine ⟨13289683356558127996330913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8859788904372085330887275 13289683356558127996330913)
        ·
          refine ⟨9967262517418595997248185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13289683356558127996330913 9967262517418595997248185)
          ·
            refine ⟨7475446888063946997936139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9967262517418595997248185 7475446888063946997936139)
            ·
              refine ⟨11213170332095920496904209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475446888063946997936139 11213170332095920496904209)
              ·
                refine ⟨8409877749071940372678157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11213170332095920496904209 8409877749071940372678157)
                ·
                  refine ⟨3153704155901977639754309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8409877749071940372678157 3153704155901977639754309)
                  ·
                    refine ⟨591319529231620807453933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153704155901977639754309 591319529231620807453933)
                    ·
                      rfl

theorem cell23_3454772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3454772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454772 prefixEnd_3454772 := by exact prefixLift 3454772
  have htrace : WordTrace (prefixWord ++ tailWord_3454772) baseStart_3454772 baseEnd_3454772 := by
    simpa [prefixWord, tailWord_3454772, baseEnd_3454772] using wordTrace_append hprefix tailTrace_3454772
  have hstable : (prefixWord ++ tailWord_3454772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454772).length < 2 ^ (prefixWord ++ tailWord_3454772).sum := by decide
  have hdescent : baseEnd_3454772 < baseStart_3454772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454782 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3454782 : Nat := 118140960795 + 3454782 * 2 ^ 59
def prefixEnd_3454782 : Nat := 4983230072969 + 3 ^ 40 * 3454782 * 2
def baseEnd_3454782 : Nat := 1773963722501407383236753

theorem tailTrace_3454782 : CollatzResearch.WordTrace tailWord_3454782 prefixEnd_3454782 1773963722501407383236753 := by
  unfold tailWord_3454782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15750781421240289829504825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84004167579948212424025733 15750781421240289829504825)
  ·
    refine ⟨11813086065930217372128619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15750781421240289829504825 11813086065930217372128619)
    ·
      refine ⟨17719629098895326058192929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11813086065930217372128619 17719629098895326058192929)
      ·
        refine ⟨13289721824171494543644697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17719629098895326058192929 13289721824171494543644697)
        ·
          refine ⟨9967291368128620907733523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13289721824171494543644697 9967291368128620907733523)
          ·
            refine ⟨14950937052192931361600285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9967291368128620907733523 14950937052192931361600285)
            ·
              refine ⟨5606601394572349260600107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14950937052192931361600285 5606601394572349260600107)
              ·
                refine ⟨8409902091858523890900161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606601394572349260600107 8409902091858523890900161)
                ·
                  refine ⟨6307426568893892918175121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8409902091858523890900161 6307426568893892918175121)
                  ·
                    refine ⟨4730569926670419688631341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6307426568893892918175121 4730569926670419688631341)
                    ·
                      refine ⟨1773963722501407383236753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4730569926670419688631341 1773963722501407383236753)
                      ·
                        rfl

theorem cell23_3454782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3454782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454782 prefixEnd_3454782 := by exact prefixLift 3454782
  have htrace : WordTrace (prefixWord ++ tailWord_3454782) baseStart_3454782 baseEnd_3454782 := by
    simpa [prefixWord, tailWord_3454782, baseEnd_3454782] using wordTrace_append hprefix tailTrace_3454782
  have hstable : (prefixWord ++ tailWord_3454782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454782).length < 2 ^ (prefixWord ++ tailWord_3454782).sum := by decide
  have hdescent : baseEnd_3454782 < baseStart_3454782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454848 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_3454848 : Nat := 118140960795 + 3454848 * 2 ^ 59
def prefixEnd_3454848 : Nat := 4983230072969 + 3 ^ 40 * 3454848 * 2
def baseEnd_3454848 : Nat := 1773997612224604125011449

theorem tailTrace_3454848 : CollatzResearch.WordTrace tailWord_3454848 prefixEnd_3454848 1773997612224604125011449 := by
  unfold tailWord_3454848
  simp only [CollatzResearch.WordTrace]
  refine ⟨63004329293841605953970599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84005772391788807938627465 63004329293841605953970599)
  ·
    refine ⟨94506493940762408930955899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63004329293841605953970599 94506493940762408930955899)
    ·
      refine ⟨141759740911143613396433849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94506493940762408930955899 141759740911143613396433849)
      ·
        refine ⟨106319805683357710047325387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141759740911143613396433849 106319805683357710047325387)
        ·
          refine ⟨159479708525036565070988081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106319805683357710047325387 159479708525036565070988081)
          ·
            refine ⟨119609781393777423803241061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159479708525036565070988081 119609781393777423803241061)
            ·
              refine ⟨22426834011333266963107699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119609781393777423803241061 22426834011333266963107699)
              ·
                refine ⟨33640251016999900444661549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22426834011333266963107699 33640251016999900444661549)
                ·
                  refine ⟨12615094131374962666748081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33640251016999900444661549 12615094131374962666748081)
                  ·
                    refine ⟨9461320598531222000061061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12615094131374962666748081 9461320598531222000061061)
                    ·
                      refine ⟨1773997612224604125011449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9461320598531222000061061 1773997612224604125011449)
                      ·
                        rfl

theorem cell23_3454848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_3454848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454848 prefixEnd_3454848 := by exact prefixLift 3454848
  have htrace : WordTrace (prefixWord ++ tailWord_3454848) baseStart_3454848 baseEnd_3454848 := by
    simpa [prefixWord, tailWord_3454848, baseEnd_3454848] using wordTrace_append hprefix tailTrace_3454848
  have hstable : (prefixWord ++ tailWord_3454848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454848).length < 2 ^ (prefixWord ++ tailWord_3454848).sum := by decide
  have hdescent : baseEnd_3454848 < baseStart_3454848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454852 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_3454852 : Nat := 118140960795 + 3454852 * 2 ^ 59
def prefixEnd_3454852 : Nat := 4983230072969 + 3 ^ 40 * 3454852 * 2
def baseEnd_3454852 : Nat := 1773999666147222109361431

theorem tailTrace_3454852 : CollatzResearch.WordTrace tailWord_3454852 prefixEnd_3454852 1773999666147222109361431 := by
  unfold tailWord_3454852
  simp only [CollatzResearch.WordTrace]
  refine ⟨63004402239834360295543405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84005869653112480394057873 63004402239834360295543405)
  ·
    refine ⟨23626650839937885110828777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63004402239834360295543405 23626650839937885110828777)
    ·
      refine ⟨17719988129953413833121583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23626650839937885110828777 17719988129953413833121583)
      ·
        refine ⟨26579982194930120749682375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17719988129953413833121583 26579982194930120749682375)
        ·
          refine ⟨39869973292395181124523563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26579982194930120749682375 39869973292395181124523563)
          ·
            refine ⟨59804959938592771686785345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39869973292395181124523563 59804959938592771686785345)
            ·
              refine ⟨44853719953944578765089009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59804959938592771686785345 44853719953944578765089009)
              ·
                refine ⟨33640289965458434073816757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44853719953944578765089009 33640289965458434073816757)
                ·
                  refine ⟨3153777184261728194420321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33640289965458434073816757 3153777184261728194420321)
                  ·
                    refine ⟨2365332888196296145815241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3153777184261728194420321 2365332888196296145815241)
                    ·
                      refine ⟨1773999666147222109361431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365332888196296145815241 1773999666147222109361431)
                      ·
                        rfl

theorem cell23_3454852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_3454852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454852 prefixEnd_3454852 := by exact prefixLift 3454852
  have htrace : WordTrace (prefixWord ++ tailWord_3454852) baseStart_3454852 baseEnd_3454852 := by
    simpa [prefixWord, tailWord_3454852, baseEnd_3454852] using wordTrace_append hprefix tailTrace_3454852
  have hstable : (prefixWord ++ tailWord_3454852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454852).length < 2 ^ (prefixWord ++ tailWord_3454852).sum := by decide
  have hdescent : baseEnd_3454852 < baseStart_3454852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454898 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3454898 : Nat := 118140960795 + 3454898 * 2 ^ 59
def prefixEnd_3454898 : Nat := 4983230072969 + 3 ^ 40 * 3454898 * 2
def baseEnd_3454898 : Nat := 1774023286257328929386219

theorem tailTrace_3454898 : CollatzResearch.WordTrace tailWord_3454898 prefixEnd_3454898 1774023286257328929386219 := by
  unfold tailWord_3454898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31502620559375517611815337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84006988158334713631507565 31502620559375517611815337)
  ·
    refine ⟨23626965419531638208861503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31502620559375517611815337 23626965419531638208861503)
    ·
      refine ⟨35440448129297457313292255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23626965419531638208861503 35440448129297457313292255)
      ·
        refine ⟨53160672193946185969938383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35440448129297457313292255 53160672193946185969938383)
        ·
          refine ⟨79741008290919278954907575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53160672193946185969938383 79741008290919278954907575)
          ·
            refine ⟨119611512436378918432361363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79741008290919278954907575 119611512436378918432361363)
            ·
              refine ⟨179417268654568377648542045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119611512436378918432361363 179417268654568377648542045)
              ·
                refine ⟨67281475745463141618203267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179417268654568377648542045 67281475745463141618203267)
                ·
                  refine ⟨100922213618194712427304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67281475745463141618203267 100922213618194712427304901)
                  ·
                    refine ⟨18922915053411508580119669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100922213618194712427304901 18922915053411508580119669)
                    ·
                      refine ⟨1774023286257328929386219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18922915053411508580119669 1774023286257328929386219)
                      ·
                        rfl

theorem cell23_3454898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3454898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454898 prefixEnd_3454898 := by exact prefixLift 3454898
  have htrace : WordTrace (prefixWord ++ tailWord_3454898) baseStart_3454898 baseEnd_3454898 := by
    simpa [prefixWord, tailWord_3454898, baseEnd_3454898] using wordTrace_append hprefix tailTrace_3454898
  have hstable : (prefixWord ++ tailWord_3454898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454898).length < 2 ^ (prefixWord ++ tailWord_3454898).sum := by decide
  have hdescent : baseEnd_3454898 < baseStart_3454898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454928 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_3454928 : Nat := 118140960795 + 3454928 * 2 ^ 59
def prefixEnd_3454928 : Nat := 4983230072969 + 3 ^ 40 * 3454928 * 2
def baseEnd_3454928 : Nat := 1774038690676963812011081

theorem tailTrace_3454928 : CollatzResearch.WordTrace tailWord_3454928 prefixEnd_3454928 1774038690676963812011081 := by
  unfold tailWord_3454928
  simp only [CollatzResearch.WordTrace]
  refine ⟨63005788213696692785426719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84007717618262257047235625 63005788213696692785426719)
  ·
    refine ⟨94508682320545039178140079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63005788213696692785426719 94508682320545039178140079)
    ·
      refine ⟨141763023480817558767210119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94508682320545039178140079 141763023480817558767210119)
      ·
        refine ⟨212644535221226338150815179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141763023480817558767210119 212644535221226338150815179)
        ·
          refine ⟨318966802831839507226222769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212644535221226338150815179 318966802831839507226222769)
          ·
            refine ⟨239225102123879630419667077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318966802831839507226222769 239225102123879630419667077)
            ·
              refine ⟨44854706648227430703687577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239225102123879630419667077 44854706648227430703687577)
              ·
                refine ⟨33641029986170573027765683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44854706648227430703687577 33641029986170573027765683)
                ·
                  refine ⟨50461544979255859541648525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33641029986170573027765683 50461544979255859541648525)
                  ·
                    refine ⟨18923079367220947328118197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50461544979255859541648525 18923079367220947328118197)
                    ·
                      refine ⟨1774038690676963812011081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18923079367220947328118197 1774038690676963812011081)
                      ·
                        rfl

theorem cell23_3454928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_3454928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3454928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3454928 prefixEnd_3454928 := by exact prefixLift 3454928
  have htrace : WordTrace (prefixWord ++ tailWord_3454928) baseStart_3454928 baseEnd_3454928 := by
    simpa [prefixWord, tailWord_3454928, baseEnd_3454928] using wordTrace_append hprefix tailTrace_3454928
  have hstable : (prefixWord ++ tailWord_3454928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454928).length < 2 ^ (prefixWord ++ tailWord_3454928).sum := by decide
  have hdescent : baseEnd_3454928 < baseStart_3454928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455055 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 6]
def baseStart_3455055 : Nat := 118140960795 + 3455055 * 2 ^ 59
def prefixEnd_3455055 : Nat := 4983230072969 + 3 ^ 40 * 3455055 * 2
def baseEnd_3455055 : Nat := 197122655857787201680333

theorem tailTrace_3455055 : CollatzResearch.WordTrace tailWord_3455055 prefixEnd_3455055 197122655857787201680333 := by
  unfold tailWord_3455055
  simp only [CollatzResearch.WordTrace]
  refine ⟨126016208497933286260726619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84010805665288857507151079 126016208497933286260726619)
  ·
    refine ⟨189024312746899929391089929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126016208497933286260726619 189024312746899929391089929)
    ·
      refine ⟨141768234560174947043317447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189024312746899929391089929 141768234560174947043317447)
      ·
        refine ⟨212652351840262420564976171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141768234560174947043317447 212652351840262420564976171)
        ·
          refine ⟨318978527760393630847464257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212652351840262420564976171 318978527760393630847464257)
          ·
            refine ⟨239233895820295223135598193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318978527760393630847464257 239233895820295223135598193)
            ·
              refine ⟨179425421865221417351698645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239233895820295223135598193 179425421865221417351698645)
              ·
                refine ⟨4205283324966126969180437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179425421865221417351698645 4205283324966126969180437)
                ·
                  refine ⟨197122655857787201680333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4205283324966126969180437 197122655857787201680333)
                  ·
                    rfl

theorem cell23_3455055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 6].length) (baseStart_3455055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455055 prefixEnd_3455055 := by exact prefixLift 3455055
  have htrace : WordTrace (prefixWord ++ tailWord_3455055) baseStart_3455055 baseEnd_3455055 := by
    simpa [prefixWord, tailWord_3455055, baseEnd_3455055] using wordTrace_append hprefix tailTrace_3455055
  have hstable : (prefixWord ++ tailWord_3455055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455055).length < 2 ^ (prefixWord ++ tailWord_3455055).sum := by decide
  have hdescent : baseEnd_3455055 < baseStart_3455055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455132 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3455132 : Nat := 118140960795 + 3455132 * 2 ^ 59
def prefixEnd_3455132 : Nat := 4983230072969 + 3 ^ 40 * 3455132 * 2
def baseEnd_3455132 : Nat := 591381146910160337953381

theorem tailTrace_3455132 : CollatzResearch.WordTrace tailWord_3455132 prefixEnd_3455132 591381146910160337953381 := by
  unfold tailWord_3455132
  simp only [CollatzResearch.WordTrace]
  refine ⟨63009508459327164205639825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84012677945769552274186433 63009508459327164205639825)
  ·
    refine ⟨47257131344495373154229869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63009508459327164205639825 47257131344495373154229869)
    ·
      refine ⟨17721424254185764932836201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47257131344495373154229869 17721424254185764932836201)
      ·
        refine ⟨13291068190639323699627151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17721424254185764932836201 13291068190639323699627151)
        ·
          refine ⟨19936602285958985549440727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13291068190639323699627151 19936602285958985549440727)
          ·
            refine ⟨29904903428938478324161091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19936602285958985549440727 29904903428938478324161091)
            ·
              refine ⟨44857355143407717486241637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29904903428938478324161091 44857355143407717486241637)
              ·
                refine ⟨8410754089388947028670307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44857355143407717486241637 8410754089388947028670307)
                ·
                  refine ⟨12616131134083420543005461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410754089388947028670307 12616131134083420543005461)
                  ·
                    refine ⟨591381146910160337953381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12616131134083420543005461 591381146910160337953381)
                    ·
                      rfl

theorem cell23_3455132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3455132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455132 prefixEnd_3455132 := by exact prefixLift 3455132
  have htrace : WordTrace (prefixWord ++ tailWord_3455132) baseStart_3455132 baseEnd_3455132 := by
    simpa [prefixWord, tailWord_3455132, baseEnd_3455132] using wordTrace_append hprefix tailTrace_3455132
  have hstable : (prefixWord ++ tailWord_3455132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455132).length < 2 ^ (prefixWord ++ tailWord_3455132).sum := by decide
  have hdescent : baseEnd_3455132 < baseStart_3455132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455133 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_3455133 : Nat := 118140960795 + 3455133 * 2 ^ 59
def prefixEnd_3455133 : Nat := 4983230072969 + 3 ^ 40 * 3455133 * 2
def baseEnd_3455133 : Nat := 1774143954211135509947639

theorem tailTrace_3455133 : CollatzResearch.WordTrace tailWord_3455133 prefixEnd_3455133 1774143954211135509947639 := by
  unfold tailWord_3455133
  simp only [CollatzResearch.WordTrace]
  refine ⟨126019053391650705582066053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84012702261100470388044035 126019053391650705582066053)
  ·
    refine ⟨23628572510934507296637385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126019053391650705582066053 23628572510934507296637385)
    ·
      refine ⟨17721429383200880472478039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23628572510934507296637385 17721429383200880472478039)
      ·
        refine ⟨26582144074801320708717059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17721429383200880472478039 26582144074801320708717059)
        ·
          refine ⟨39873216112201981063075589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26582144074801320708717059 39873216112201981063075589)
          ·
            refine ⟨7476228021037871449326673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39873216112201981063075589 7476228021037871449326673)
            ·
              refine ⟨5607171015778403586995005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7476228021037871449326673 5607171015778403586995005)
              ·
                refine ⟨2102689130916901345123127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5607171015778403586995005 2102689130916901345123127)
                ·
                  refine ⟨3154033696375352017684691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102689130916901345123127 3154033696375352017684691)
                  ·
                    refine ⟨4731050544563028026527037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3154033696375352017684691 4731050544563028026527037)
                    ·
                      refine ⟨1774143954211135509947639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4731050544563028026527037 1774143954211135509947639)
                      ·
                        rfl

theorem cell23_3455133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_3455133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455133 prefixEnd_3455133 := by exact prefixLift 3455133
  have htrace : WordTrace (prefixWord ++ tailWord_3455133) baseStart_3455133 baseEnd_3455133 := by
    simpa [prefixWord, tailWord_3455133, baseEnd_3455133] using wordTrace_append hprefix tailTrace_3455133
  have hstable : (prefixWord ++ tailWord_3455133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455133).length < 2 ^ (prefixWord ++ tailWord_3455133).sum := by decide
  have hdescent : baseEnd_3455133 < baseStart_3455133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455136 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 1, 5]
def baseStart_3455136 : Nat := 118140960795 + 3455136 * 2 ^ 59
def prefixEnd_3455136 : Nat := 4983230072969 + 3 ^ 40 * 3455136 * 2
def baseEnd_3455136 : Nat := 591381831551032999403375

theorem tailTrace_3455136 : CollatzResearch.WordTrace tailWord_3455136 prefixEnd_3455136 591381831551032999403375 := by
  unfold tailWord_3455136
  simp only [CollatzResearch.WordTrace]
  refine ⟨63009581405319918547212631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84012775207093224729616841 63009581405319918547212631)
  ·
    refine ⟨94514372107979877820818947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63009581405319918547212631 94514372107979877820818947)
    ·
      refine ⟨141771558161969816731228421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94514372107979877820818947 141771558161969816731228421)
      ·
        refine ⟨26582167155369340637105329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141771558161969816731228421 26582167155369340637105329)
        ·
          refine ⟨19936625366527005477828997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26582167155369340637105329 19936625366527005477828997)
          ·
            refine ⟨3738117256223813527092937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19936625366527005477828997 3738117256223813527092937)
            ·
              refine ⟨2803587942167860145319703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3738117256223813527092937 2803587942167860145319703)
              ·
                refine ⟨4205381913251790217979555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803587942167860145319703 4205381913251790217979555)
                ·
                  refine ⟨6308072869877685326969333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205381913251790217979555 6308072869877685326969333)
                  ·
                    refine ⟨591381831551032999403375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6308072869877685326969333 591381831551032999403375)
                    ·
                      rfl

theorem cell23_3455136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 5].length) (baseStart_3455136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455136 prefixEnd_3455136 := by exact prefixLift 3455136
  have htrace : WordTrace (prefixWord ++ tailWord_3455136) baseStart_3455136 baseEnd_3455136 := by
    simpa [prefixWord, tailWord_3455136, baseEnd_3455136] using wordTrace_append hprefix tailTrace_3455136
  have hstable : (prefixWord ++ tailWord_3455136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455136).length < 2 ^ (prefixWord ++ tailWord_3455136).sum := by decide
  have hdescent : baseEnd_3455136 < baseStart_3455136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455150 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3455150 : Nat := 118140960795 + 3455150 * 2 ^ 59
def prefixEnd_3455150 : Nat := 4983230072969 + 3 ^ 40 * 3455150 * 2
def baseEnd_3455150 : Nat := 1774152683382261943435061

theorem tailTrace_3455150 : CollatzResearch.WordTrace tailWord_3455150 prefixEnd_3455150 1774152683382261943435061 := by
  unfold tailWord_3455150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15752459179073639685679363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84013115621726078323623269 15752459179073639685679363)
  ·
    refine ⟨23628688768610459528519045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15752459179073639685679363 23628688768610459528519045)
    ·
      refine ⟨4430379144114461161597321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23628688768610459528519045 4430379144114461161597321)
      ·
        refine ⟨3322784358085845871197991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430379144114461161597321 3322784358085845871197991)
        ·
          refine ⟨4984176537128768806796987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322784358085845871197991 4984176537128768806796987)
          ·
            refine ⟨7476264805693153210195481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984176537128768806796987 7476264805693153210195481)
            ·
              refine ⟨5607198604269864907646611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7476264805693153210195481 5607198604269864907646611)
              ·
                refine ⟨8410797906404797361469917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607198604269864907646611 8410797906404797361469917)
                ·
                  refine ⟨3154049214901799010551219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8410797906404797361469917 3154049214901799010551219)
                  ·
                    refine ⟨4731073822352698515826829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3154049214901799010551219 4731073822352698515826829)
                    ·
                      refine ⟨1774152683382261943435061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4731073822352698515826829 1774152683382261943435061)
                      ·
                        rfl

theorem cell23_3455150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3455150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455150 prefixEnd_3455150 := by exact prefixLift 3455150
  have htrace : WordTrace (prefixWord ++ tailWord_3455150) baseStart_3455150 baseEnd_3455150 := by
    simpa [prefixWord, tailWord_3455150, baseEnd_3455150] using wordTrace_append hprefix tailTrace_3455150
  have hstable : (prefixWord ++ tailWord_3455150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455150).length < 2 ^ (prefixWord ++ tailWord_3455150).sum := by decide
  have hdescent : baseEnd_3455150 < baseStart_3455150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455155 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_3455155 : Nat := 118140960795 + 3455155 * 2 ^ 59
def prefixEnd_3455155 : Nat := 4983230072969 + 3 ^ 40 * 3455155 * 2
def baseEnd_3455155 : Nat := 1774155250785534423872537

theorem tailTrace_3455155 : CollatzResearch.WordTrace tailWord_3455155 prefixEnd_3455155 1774155250785534423872537 := by
  unfold tailWord_3455155
  simp only [CollatzResearch.WordTrace]
  refine ⟨126019855797571003339366919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84013237198380668892911279 126019855797571003339366919)
  ·
    refine ⟨189029783696356505009050379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126019855797571003339366919 189029783696356505009050379)
    ·
      refine ⟨283544675544534757513575569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189029783696356505009050379 283544675544534757513575569)
      ·
        refine ⟨212658506658401068135181677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283544675544534757513575569 212658506658401068135181677)
        ·
          refine ⟨79746939996900400550693129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212658506658401068135181677 79746939996900400550693129)
          ·
            refine ⟨59810204997675300413019847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79746939996900400550693129 59810204997675300413019847)
            ·
              refine ⟨89715307496512950619529771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59810204997675300413019847 89715307496512950619529771)
              ·
                refine ⟨134572961244769425929294657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89715307496512950619529771 134572961244769425929294657)
                ·
                  refine ⟨100929720933577069446970993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134572961244769425929294657 100929720933577069446970993)
                  ·
                    refine ⟨75697290700182802085228245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100929720933577069446970993 75697290700182802085228245)
                    ·
                      refine ⟨1774155250785534423872537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75697290700182802085228245 1774155250785534423872537)
                      ·
                        rfl

theorem cell23_3455155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_3455155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455155 prefixEnd_3455155 := by exact prefixLift 3455155
  have htrace : WordTrace (prefixWord ++ tailWord_3455155) baseStart_3455155 baseEnd_3455155 := by
    simpa [prefixWord, tailWord_3455155, baseEnd_3455155] using wordTrace_append hprefix tailTrace_3455155
  have hstable : (prefixWord ++ tailWord_3455155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455155).length < 2 ^ (prefixWord ++ tailWord_3455155).sum := by decide
  have hdescent : baseEnd_3455155 < baseStart_3455155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455166 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3455166 : Nat := 118140960795 + 3455166 * 2 ^ 59
def prefixEnd_3455166 : Nat := 4983230072969 + 3 ^ 40 * 3455166 * 2
def baseEnd_3455166 : Nat := 591386966357577960278329

theorem tailTrace_3455166 : CollatzResearch.WordTrace tailWord_3455166 prefixEnd_3455166 591386966357577960278329 := by
  unfold tailWord_3455166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15752532125066394027252169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84013504667020768145344901 15752532125066394027252169)
  ·
    refine ⟨11814399093799795520439127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15752532125066394027252169 11814399093799795520439127)
    ·
      refine ⟨17721598640699693280658691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11814399093799795520439127 17721598640699693280658691)
      ·
        refine ⟨26582397961049539920988037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17721598640699693280658691 26582397961049539920988037)
        ·
          refine ⟨4984199617696788735185257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26582397961049539920988037 4984199617696788735185257)
          ·
            refine ⟨3738149713272591551388943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984199617696788735185257 3738149713272591551388943)
            ·
              refine ⟨5607224569908887327083415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738149713272591551388943 5607224569908887327083415)
              ·
                refine ⟨8410836854863330990625123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607224569908887327083415 8410836854863330990625123)
                ·
                  refine ⟨12616255282294996485937685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410836854863330990625123 12616255282294996485937685)
                  ·
                    refine ⟨591386966357577960278329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12616255282294996485937685 591386966357577960278329)
                    ·
                      rfl

theorem cell23_3455166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3455166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455166 prefixEnd_3455166 := by exact prefixLift 3455166
  have htrace : WordTrace (prefixWord ++ tailWord_3455166) baseStart_3455166 baseEnd_3455166 := by
    simpa [prefixWord, tailWord_3455166, baseEnd_3455166] using wordTrace_append hprefix tailTrace_3455166
  have hstable : (prefixWord ++ tailWord_3455166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455166).length < 2 ^ (prefixWord ++ tailWord_3455166).sum := by decide
  have hdescent : baseEnd_3455166 < baseStart_3455166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455196 : List Nat := [2, 2, 5, 2, 1, 2, 9]
def baseStart_3455196 : Nat := 118140960795 + 3455196 * 2 ^ 59
def prefixEnd_3455196 : Nat := 4983230072969 + 3 ^ 40 * 3455196 * 2
def baseEnd_3455196 : Nat := 21903411154226774857529

theorem tailTrace_3455196 : CollatzResearch.WordTrace tailWord_3455196 prefixEnd_3455196 21903411154226774857529 := by
  unfold tailWord_3455196
  simp only [CollatzResearch.WordTrace]
  refine ⟨63010675595211233670804721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84014234126948311561072961 63010675595211233670804721)
  ·
    refine ⟨47258006696408425253103541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63010675595211233670804721 47258006696408425253103541)
    ·
      refine ⟨4430438127788289867478457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47258006696408425253103541 4430438127788289867478457)
      ·
        refine ⟨3322828595841217400608843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430438127788289867478457 3322828595841217400608843)
        ·
          refine ⟨4984242893761826100913265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322828595841217400608843 4984242893761826100913265)
          ·
            refine ⟨3738182170321369575684949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984242893761826100913265 3738182170321369575684949)
            ·
              refine ⟨21903411154226774857529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3738182170321369575684949 21903411154226774857529)
              ·
                rfl

theorem cell23_3455196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 9].length) (baseStart_3455196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455196 prefixEnd_3455196 := by exact prefixLift 3455196
  have htrace : WordTrace (prefixWord ++ tailWord_3455196) baseStart_3455196 baseEnd_3455196 := by
    simpa [prefixWord, tailWord_3455196, baseEnd_3455196] using wordTrace_append hprefix tailTrace_3455196
  have hstable : (prefixWord ++ tailWord_3455196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455196).length < 2 ^ (prefixWord ++ tailWord_3455196).sum := by decide
  have hdescent : baseEnd_3455196 < baseStart_3455196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455199 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 5, 3, 2]
def baseStart_3455199 : Nat := 118140960795 + 3455199 * 2 ^ 59
def prefixEnd_3455199 : Nat := 4983230072969 + 3 ^ 40 * 3455199 * 2
def baseEnd_3455199 : Nat := 1774177843934332251722335

theorem tailTrace_3455199 : CollatzResearch.WordTrace tailWord_3455199 prefixEnd_3455199 1774177843934332251722335 := by
  unfold tailWord_3455199
  simp only [CollatzResearch.WordTrace]
  refine ⟨126021460609411598853968651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84014307072941065902645767 126021460609411598853968651)
  ·
    refine ⟨189032190914117398280952977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126021460609411598853968651 189032190914117398280952977)
    ·
      refine ⟨141774143185588048710714733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189032190914117398280952977 141774143185588048710714733)
      ·
        refine ⟨53165303694595518266518025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141774143185588048710714733 53165303694595518266518025)
        ·
          refine ⟨39873977770946638699888519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53165303694595518266518025 39873977770946638699888519)
          ·
            refine ⟨59810966656419958049832779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39873977770946638699888519 59810966656419958049832779)
            ·
              refine ⟨89716449984629937074749169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59810966656419958049832779 89716449984629937074749169)
              ·
                refine ⟨67287337488472452806061877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89716449984629937074749169 67287337488472452806061877)
                ·
                  refine ⟨6308187889544292450568301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67287337488472452806061877 6308187889544292450568301)
                  ·
                    refine ⟨2365570458579109668963113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6308187889544292450568301 2365570458579109668963113)
                    ·
                      refine ⟨1774177843934332251722335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365570458579109668963113 1774177843934332251722335)
                      ·
                        rfl

theorem cell23_3455199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_3455199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455199 prefixEnd_3455199 := by exact prefixLift 3455199
  have htrace : WordTrace (prefixWord ++ tailWord_3455199) baseStart_3455199 baseEnd_3455199 := by
    simpa [prefixWord, tailWord_3455199, baseEnd_3455199] using wordTrace_append hprefix tailTrace_3455199
  have hstable : (prefixWord ++ tailWord_3455199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455199).length < 2 ^ (prefixWord ++ tailWord_3455199).sum := by decide
  have hdescent : baseEnd_3455199 < baseStart_3455199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455207 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3455207 : Nat := 118140960795 + 3455207 * 2 ^ 59
def prefixEnd_3455207 : Nat := 4983230072969 + 3 ^ 40 * 3455207 * 2
def baseEnd_3455207 : Nat := 1774181951779568220422299

theorem tailTrace_3455207 : CollatzResearch.WordTrace tailWord_3455207 prefixEnd_3455207 1774181951779568220422299 := by
  unfold tailWord_3455207
  simp only [CollatzResearch.WordTrace]
  refine ⟨126021752393382616220259875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84014501595588410813506583 126021752393382616220259875)
  ·
    refine ⟨189032628590073924330389813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126021752393382616220259875 189032628590073924330389813)
    ·
      refine ⟨17721808930319430405974045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189032628590073924330389813 17721808930319430405974045)
      ·
        refine ⟨6645678348869786402240267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17721808930319430405974045 6645678348869786402240267)
        ·
          refine ⟨9968517523304679603360401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645678348869786402240267 9968517523304679603360401)
          ·
            refine ⟨7476388142478509702520301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9968517523304679603360401 7476388142478509702520301)
            ·
              refine ⟨2803645553429441138445113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7476388142478509702520301 2803645553429441138445113)
              ·
                refine ⟨2102734165072080853833835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803645553429441138445113 2102734165072080853833835)
                ·
                  refine ⟨3154101247608121280750753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102734165072080853833835 3154101247608121280750753)
                  ·
                    refine ⟨2365575935706090960563065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3154101247608121280750753 2365575935706090960563065)
                    ·
                      refine ⟨1774181951779568220422299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365575935706090960563065 1774181951779568220422299)
                      ·
                        rfl

theorem cell23_3455207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3455207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455207 prefixEnd_3455207 := by exact prefixLift 3455207
  have htrace : WordTrace (prefixWord ++ tailWord_3455207) baseStart_3455207 baseEnd_3455207 := by
    simpa [prefixWord, tailWord_3455207, baseEnd_3455207] using wordTrace_append hprefix tailTrace_3455207
  have hstable : (prefixWord ++ tailWord_3455207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455207).length < 2 ^ (prefixWord ++ tailWord_3455207).sum := by decide
  have hdescent : baseEnd_3455207 < baseStart_3455207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455212 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3455212 : Nat := 118140960795 + 3455212 * 2 ^ 59
def prefixEnd_3455212 : Nat := 4983230072969 + 3 ^ 40 * 3455212 * 2
def baseEnd_3455212 : Nat := 1774184519182840700859775

theorem tailTrace_3455212 : CollatzResearch.WordTrace tailWord_3455212 prefixEnd_3455212 1774184519182840700859775 := by
  unfold tailWord_3455212
  simp only [CollatzResearch.WordTrace]
  refine ⟨63010967379182251037095945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84014623172243001382794593 63010967379182251037095945)
  ·
    refine ⟨47258225534386688277821959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63010967379182251037095945 47258225534386688277821959)
    ·
      refine ⟨70887338301580032416732939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47258225534386688277821959 70887338301580032416732939)
      ·
        refine ⟨106331007452370048625099409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70887338301580032416732939 106331007452370048625099409)
        ·
          refine ⟨79748255589277536468824557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106331007452370048625099409 79748255589277536468824557)
          ·
            refine ⟨29905595845979076175809209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79748255589277536468824557 29905595845979076175809209)
            ·
              refine ⟨22429196884484307131856907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29905595845979076175809209 22429196884484307131856907)
              ·
                refine ⟨33643795326726460697785361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22429196884484307131856907 33643795326726460697785361)
                ·
                  refine ⟨25232846495044845523339021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33643795326726460697785361 25232846495044845523339021)
                  ·
                    refine ⟨9462317435641817071252133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25232846495044845523339021 9462317435641817071252133)
                    ·
                      refine ⟨1774184519182840700859775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9462317435641817071252133 1774184519182840700859775)
                      ·
                        rfl

theorem cell23_3455212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3455212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455212 prefixEnd_3455212 := by exact prefixLift 3455212
  have htrace : WordTrace (prefixWord ++ tailWord_3455212) baseStart_3455212 baseEnd_3455212 := by
    simpa [prefixWord, tailWord_3455212, baseEnd_3455212] using wordTrace_append hprefix tailTrace_3455212
  have hstable : (prefixWord ++ tailWord_3455212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455212).length < 2 ^ (prefixWord ++ tailWord_3455212).sum := by decide
  have hdescent : baseEnd_3455212 < baseStart_3455212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455229 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_3455229 : Nat := 118140960795 + 3455229 * 2 ^ 59
def prefixEnd_3455229 : Nat := 4983230072969 + 3 ^ 40 * 3455229 * 2
def baseEnd_3455229 : Nat := 1774193248353967134347197

theorem tailTrace_3455229 : CollatzResearch.WordTrace tailWord_3455229 prefixEnd_3455229 1774193248353967134347197 := by
  unfold tailWord_3455229
  simp only [CollatzResearch.WordTrace]
  refine ⟨126022554799302913977560741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84015036532868609318373827 126022554799302913977560741)
  ·
    refine ⟨23629229024869296370792639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126022554799302913977560741 23629229024869296370792639)
    ·
      refine ⟨35443843537303944556188959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23629229024869296370792639 35443843537303944556188959)
      ·
        refine ⟨53165765305955916834283439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35443843537303944556188959 53165765305955916834283439)
        ·
          refine ⟨79748647958933875251425159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53165765305955916834283439 79748647958933875251425159)
          ·
            refine ⟨119622971938400812877137739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79748647958933875251425159 119622971938400812877137739)
            ·
              refine ⟨179434457907601219315706609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119622971938400812877137739 179434457907601219315706609)
              ·
                refine ⟨134575843430700914486779957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179434457907601219315706609 134575843430700914486779957)
                ·
                  refine ⟨12616485321628210733135621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134575843430700914486779957 12616485321628210733135621)
                  ·
                    refine ⟨2365590997805289512462929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12616485321628210733135621 2365590997805289512462929)
                    ·
                      refine ⟨1774193248353967134347197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365590997805289512462929 1774193248353967134347197)
                      ·
                        rfl

theorem cell23_3455229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_3455229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455229 prefixEnd_3455229 := by exact prefixLift 3455229
  have htrace : WordTrace (prefixWord ++ tailWord_3455229) baseStart_3455229 baseEnd_3455229 := by
    simpa [prefixWord, tailWord_3455229, baseEnd_3455229] using wordTrace_append hprefix tailTrace_3455229
  have hstable : (prefixWord ++ tailWord_3455229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455229).length < 2 ^ (prefixWord ++ tailWord_3455229).sum := by decide
  have hdescent : baseEnd_3455229 < baseStart_3455229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455232 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_3455232 : Nat := 118140960795 + 3455232 * 2 ^ 59
def prefixEnd_3455232 : Nat := 4983230072969 + 3 ^ 40 * 3455232 * 2
def baseEnd_3455232 : Nat := 1774194788795930622609683

theorem tailTrace_3455232 : CollatzResearch.WordTrace tailWord_3455232 prefixEnd_3455232 1774194788795930622609683 := by
  unfold tailWord_3455232
  simp only [CollatzResearch.WordTrace]
  refine ⟨63011332109146022744959975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84015109478861363659946633 63011332109146022744959975)
  ·
    refine ⟨94516998163719034117439963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63011332109146022744959975 94516998163719034117439963)
    ·
      refine ⟨141775497245578551176159945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94516998163719034117439963 141775497245578551176159945)
      ·
        refine ⟨106331622934183913382119959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141775497245578551176159945 106331622934183913382119959)
        ·
          refine ⟨159497434401275870073179939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106331622934183913382119959 159497434401275870073179939)
          ·
            refine ⟨239246151601913805109769909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159497434401275870073179939 239246151601913805109769909)
            ·
              refine ⟨22429326712679419229040929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239246151601913805109769909 22429326712679419229040929)
              ·
                refine ⟨16821995034509564421780697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22429326712679419229040929 16821995034509564421780697)
                ·
                  refine ⟨12616496275882173316335523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16821995034509564421780697 12616496275882173316335523)
                  ·
                    refine ⟨18924744413823259974503285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12616496275882173316335523 18924744413823259974503285)
                    ·
                      refine ⟨1774194788795930622609683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18924744413823259974503285 1774194788795930622609683)
                      ·
                        rfl

theorem cell23_3455232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_3455232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455232 prefixEnd_3455232 := by exact prefixLift 3455232
  have htrace : WordTrace (prefixWord ++ tailWord_3455232) baseStart_3455232 baseEnd_3455232 := by
    simpa [prefixWord, tailWord_3455232, baseEnd_3455232] using wordTrace_append hprefix tailTrace_3455232
  have hstable : (prefixWord ++ tailWord_3455232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455232).length < 2 ^ (prefixWord ++ tailWord_3455232).sum := by decide
  have hdescent : baseEnd_3455232 < baseStart_3455232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455246 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3455246 : Nat := 118140960795 + 3455246 * 2 ^ 59
def prefixEnd_3455246 : Nat := 4983230072969 + 3 ^ 40 * 3455246 * 2
def baseEnd_3455246 : Nat := 1774201977525093567834619

theorem tailTrace_3455246 : CollatzResearch.WordTrace tailWord_3455246 prefixEnd_3455246 1774201977525093567834619 := by
  unfold tailWord_3455246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15752896855030165735116199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84015449893494217253953061 15752896855030165735116199)
  ·
    refine ⟨23629345282545248602674299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15752896855030165735116199 23629345282545248602674299)
    ·
      refine ⟨35444017923817872904011449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23629345282545248602674299 35444017923817872904011449)
      ·
        refine ⟨26583013442863404678008587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35444017923817872904011449 26583013442863404678008587)
        ·
          refine ⟨39874520164295107017012881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26583013442863404678008587 39874520164295107017012881)
          ·
            refine ⟨29905890123221330262759661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39874520164295107017012881 29905890123221330262759661)
            ·
              refine ⟨11214708796207998848534873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29905890123221330262759661 11214708796207998848534873)
              ·
                refine ⟨8411031597155999136401155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11214708796207998848534873 8411031597155999136401155)
                ·
                  refine ⟨12616547395733998704601733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411031597155999136401155 12616547395733998704601733)
                  ·
                    refine ⟨2365602636700124757112825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12616547395733998704601733 2365602636700124757112825)
                    ·
                      refine ⟨1774201977525093567834619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365602636700124757112825 1774201977525093567834619)
                      ·
                        rfl

theorem cell23_3455246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3455246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455246 prefixEnd_3455246 := by exact prefixLift 3455246
  have htrace : WordTrace (prefixWord ++ tailWord_3455246) baseStart_3455246 baseEnd_3455246 := by
    simpa [prefixWord, tailWord_3455246, baseEnd_3455246] using wordTrace_append hprefix tailTrace_3455246
  have hstable : (prefixWord ++ tailWord_3455246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455246).length < 2 ^ (prefixWord ++ tailWord_3455246).sum := by decide
  have hdescent : baseEnd_3455246 < baseStart_3455246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455263 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 2, 2, 2]
def baseStart_3455263 : Nat := 118140960795 + 3455263 * 2 ^ 59
def prefixEnd_3455263 : Nat := 4983230072969 + 3 ^ 40 * 3455263 * 2
def baseEnd_3455263 : Nat := 1774210706696220001322041

theorem tailTrace_3455263 : CollatzResearch.WordTrace tailWord_3455263 prefixEnd_3455263 1774210706696220001322041 := by
  unfold tailWord_3455263
  simp only [CollatzResearch.WordTrace]
  refine ⟨126023794881179737784298443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84015863254119825189532295 126023794881179737784298443)
  ·
    refine ⟨189035692321769606676447665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126023794881179737784298443 189035692321769606676447665)
    ·
      refine ⟨141776769241327205007335749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189035692321769606676447665 141776769241327205007335749)
      ·
        refine ⟨26583144232748850938875453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141776769241327205007335749 26583144232748850938875453)
        ·
          refine ⟨9968679087280819102078295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26583144232748850938875453 9968679087280819102078295)
          ·
            refine ⟨14953018630921228653117443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968679087280819102078295 14953018630921228653117443)
            ·
              refine ⟨22429527946381842979676165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14953018630921228653117443 22429527946381842979676165)
              ·
                refine ⟨4205536489946595558689281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22429527946381842979676165 4205536489946595558689281)
                ·
                  refine ⟨3154152367459946669016961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205536489946595558689281 3154152367459946669016961)
                  ·
                    refine ⟨2365614275594960001762721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3154152367459946669016961 2365614275594960001762721)
                    ·
                      refine ⟨1774210706696220001322041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365614275594960001762721 1774210706696220001322041)
                      ·
                        rfl

theorem cell23_3455263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_3455263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455263 prefixEnd_3455263 := by exact prefixLift 3455263
  have htrace : WordTrace (prefixWord ++ tailWord_3455263) baseStart_3455263 baseEnd_3455263 := by
    simpa [prefixWord, tailWord_3455263, baseEnd_3455263] using wordTrace_append hprefix tailTrace_3455263
  have hstable : (prefixWord ++ tailWord_3455263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455263).length < 2 ^ (prefixWord ++ tailWord_3455263).sum := by decide
  have hdescent : baseEnd_3455263 < baseStart_3455263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455299 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 2, 5]
def baseStart_3455299 : Nat := 118140960795 + 3455299 * 2 ^ 59
def prefixEnd_3455299 : Nat := 4983230072969 + 3 ^ 40 * 3455299 * 2
def baseEnd_3455299 : Nat := 591409730666593953490625

theorem tailTrace_3455299 : CollatzResearch.WordTrace tailWord_3455299 prefixEnd_3455299 591409730666593953490625 := by
  unfold tailWord_3455299
  simp only [CollatzResearch.WordTrace]
  refine ⟨126025107909049315932608951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84016738606032877288405967 126025107909049315932608951)
  ·
    refine ⟨189037661863573973898913427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126025107909049315932608951 189037661863573973898913427)
    ·
      refine ⟨283556492795360960848370141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189037661863573973898913427 283556492795360960848370141)
      ·
        refine ⟨106333684798260360318138803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283556492795360960848370141 106333684798260360318138803)
        ·
          refine ⟨159500527197390540477208205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106333684798260360318138803 159500527197390540477208205)
          ·
            refine ⟨59812697699021452678953077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159500527197390540477208205 59812697699021452678953077)
            ·
              refine ⟨5607440409283261188651851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59812697699021452678953077 5607440409283261188651851)
              ·
                refine ⟨8411160613924891782977777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607440409283261188651851 8411160613924891782977777)
                ·
                  refine ⟨6308370460443668837233333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8411160613924891782977777 6308370460443668837233333)
                  ·
                    refine ⟨591409730666593953490625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6308370460443668837233333 591409730666593953490625)
                    ·
                      rfl

theorem cell23_3455299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 5].length) (baseStart_3455299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455299 prefixEnd_3455299 := by exact prefixLift 3455299
  have htrace : WordTrace (prefixWord ++ tailWord_3455299) baseStart_3455299 baseEnd_3455299 := by
    simpa [prefixWord, tailWord_3455299, baseEnd_3455299] using wordTrace_append hprefix tailTrace_3455299
  have hstable : (prefixWord ++ tailWord_3455299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455299).length < 2 ^ (prefixWord ++ tailWord_3455299).sum := by decide
  have hdescent : baseEnd_3455299 < baseStart_3455299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455319 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_3455319 : Nat := 118140960795 + 3455319 * 2 ^ 59
def prefixEnd_3455319 : Nat := 4983230072969 + 3 ^ 40 * 3455319 * 2
def baseEnd_3455319 : Nat := 1774239461612871782221783

theorem tailTrace_3455319 : CollatzResearch.WordTrace tailWord_3455319 prefixEnd_3455319 1774239461612871782221783 := by
  unfold tailWord_3455319
  simp only [CollatzResearch.WordTrace]
  refine ⟨126025837368976859348337011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84017224912651239565558007 126025837368976859348337011)
  ·
    refine ⟨189038756053465289022505517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126025837368976859348337011 189038756053465289022505517)
    ·
      refine ⟨70889533520049483383439569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189038756053465289022505517 70889533520049483383439569)
      ·
        refine ⟨53167150140037112537579677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70889533520049483383439569 53167150140037112537579677)
        ·
          refine ⟨19937681302513917201592379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53167150140037112537579677 19937681302513917201592379)
          ·
            refine ⟨29906521953770875802388569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19937681302513917201592379 29906521953770875802388569)
            ·
              refine ⟨22429891465328156851791427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29906521953770875802388569 22429891465328156851791427)
              ·
                refine ⟨33644837197992235277687141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22429891465328156851791427 33644837197992235277687141)
                ·
                  refine ⟨6308406974623544114566339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33644837197992235277687141 6308406974623544114566339)
                  ·
                    refine ⟨9462610461935316171849509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6308406974623544114566339 9462610461935316171849509)
                    ·
                      refine ⟨1774239461612871782221783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9462610461935316171849509 1774239461612871782221783)
                      ·
                        rfl

theorem cell23_3455319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_3455319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455319 prefixEnd_3455319 := by exact prefixLift 3455319
  have htrace : WordTrace (prefixWord ++ tailWord_3455319) baseStart_3455319 baseEnd_3455319 := by
    simpa [prefixWord, tailWord_3455319, baseEnd_3455319] using wordTrace_append hprefix tailTrace_3455319
  have hstable : (prefixWord ++ tailWord_3455319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455319).length < 2 ^ (prefixWord ++ tailWord_3455319).sum := by decide
  have hdescent : baseEnd_3455319 < baseStart_3455319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455339 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 3]
def baseStart_3455339 : Nat := 118140960795 + 3455339 * 2 ^ 59
def prefixEnd_3455339 : Nat := 4983230072969 + 3 ^ 40 * 3455339 * 2
def baseEnd_3455339 : Nat := 1774249731225961703971691

theorem tailTrace_3455339 : CollatzResearch.WordTrace tailWord_3455339 prefixEnd_3455339 1774249731225961703971691 := by
  unfold tailWord_3455339
  simp only [CollatzResearch.WordTrace]
  refine ⟨126026566828904402764065071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84017711219269601842710047 126026566828904402764065071)
  ·
    refine ⟨189039850243356604146097607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126026566828904402764065071 189039850243356604146097607)
    ·
      refine ⟨283559775365034906219146411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189039850243356604146097607 283559775365034906219146411)
      ·
        refine ⟨425339663047552359328719617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283559775365034906219146411 425339663047552359328719617)
        ·
          refine ⟨319004747285664269496539713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425339663047552359328719617 319004747285664269496539713)
          ·
            refine ⟨239253560464248202122404785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319004747285664269496539713 239253560464248202122404785)
            ·
              refine ⟨179440170348186151591803589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239253560464248202122404785 179440170348186151591803589)
              ·
                refine ⟨33645031940284903423463173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179440170348186151591803589 33645031940284903423463173)
                ·
                  refine ⟨6308443488803419391899345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33645031940284903423463173 6308443488803419391899345)
                  ·
                    refine ⟨4731332616602564543924509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6308443488803419391899345 4731332616602564543924509)
                    ·
                      refine ⟨1774249731225961703971691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4731332616602564543924509 1774249731225961703971691)
                      ·
                        rfl

theorem cell23_3455339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 3].length) (baseStart_3455339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455339 prefixEnd_3455339 := by exact prefixLift 3455339
  have htrace : WordTrace (prefixWord ++ tailWord_3455339) baseStart_3455339 baseEnd_3455339 := by
    simpa [prefixWord, tailWord_3455339, baseEnd_3455339] using wordTrace_append hprefix tailTrace_3455339
  have hstable : (prefixWord ++ tailWord_3455339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455339).length < 2 ^ (prefixWord ++ tailWord_3455339).sum := by decide
  have hdescent : baseEnd_3455339 < baseStart_3455339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455346 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3455346 : Nat := 118140960795 + 3455346 * 2 ^ 59
def prefixEnd_3455346 : Nat := 4983230072969 + 3 ^ 40 * 3455346 * 2
def baseEnd_3455346 : Nat := 591417775196847725528053

theorem tailTrace_3455346 : CollatzResearch.WordTrace tailWord_3455346 prefixEnd_3455346 591417775196847725528053 := by
  unfold tailWord_3455346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31506705534969760739892473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84017881426586028639713261 31506705534969760739892473)
  ·
    refine ⟨23630029151227320554919355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31506705534969760739892473 23630029151227320554919355)
    ·
      refine ⟨35445043726840980832379033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23630029151227320554919355 35445043726840980832379033)
      ·
        refine ⟨26583782795130735624284275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35445043726840980832379033 26583782795130735624284275)
        ·
          refine ⟨39875674192696103436426413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26583782795130735624284275 39875674192696103436426413)
          ·
            refine ⟨14953377822261038788659905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39875674192696103436426413 14953377822261038788659905)
            ·
              refine ⟨11215033366695779091494929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14953377822261038788659905 11215033366695779091494929)
              ·
                refine ⟨8411275025021834318621197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11215033366695779091494929 8411275025021834318621197)
                ·
                  refine ⟨3154228134383187869482949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8411275025021834318621197 3154228134383187869482949)
                  ·
                    refine ⟨591417775196847725528053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154228134383187869482949 591417775196847725528053)
                    ·
                      rfl

theorem cell23_3455346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3455346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455346 prefixEnd_3455346 := by exact prefixLift 3455346
  have htrace : WordTrace (prefixWord ++ tailWord_3455346) baseStart_3455346 baseEnd_3455346 := by
    simpa [prefixWord, tailWord_3455346, baseEnd_3455346] using wordTrace_append hprefix tailTrace_3455346
  have hstable : (prefixWord ++ tailWord_3455346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455346).length < 2 ^ (prefixWord ++ tailWord_3455346).sum := by decide
  have hdescent : baseEnd_3455346 < baseStart_3455346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455352 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_3455352 : Nat := 118140960795 + 3455352 * 2 ^ 59
def prefixEnd_3455352 : Nat := 4983230072969 + 3 ^ 40 * 3455352 * 2
def baseEnd_3455352 : Nat := 1774256406474470153109131

theorem tailTrace_3455352 : CollatzResearch.WordTrace tailWord_3455352 prefixEnd_3455352 1774256406474470153109131 := by
  unfold tailWord_3455352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63013520488928652992144155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84018027318571537322858873 63013520488928652992144155)
  ·
    refine ⟨94520280733392979488216233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63013520488928652992144155 94520280733392979488216233)
    ·
      refine ⟨70890210550044734616162175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94520280733392979488216233 70890210550044734616162175)
      ·
        refine ⟨106335315825067101924243263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70890210550044734616162175 106335315825067101924243263)
        ·
          refine ⟨159502973737600652886364895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106335315825067101924243263 159502973737600652886364895)
          ·
            refine ⟨239254460606400979329547343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159502973737600652886364895 239254460606400979329547343)
            ·
              refine ⟨358881690909601468994321015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239254460606400979329547343 358881690909601468994321015)
              ·
                refine ⟨538322536364402203491481523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358881690909601468994321015 538322536364402203491481523)
                ·
                  refine ⟨807483804546603305237222285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538322536364402203491481523 807483804546603305237222285)
                  ·
                    refine ⟨302806426704976239463958357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807483804546603305237222285 302806426704976239463958357)
                    ·
                      refine ⟨1774256406474470153109131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 302806426704976239463958357 1774256406474470153109131)
                      ·
                        rfl

theorem cell23_3455352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_3455352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455352 prefixEnd_3455352 := by exact prefixLift 3455352
  have htrace : WordTrace (prefixWord ++ tailWord_3455352) baseStart_3455352 baseEnd_3455352 := by
    simpa [prefixWord, tailWord_3455352, baseEnd_3455352] using wordTrace_append hprefix tailTrace_3455352
  have hstable : (prefixWord ++ tailWord_3455352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455352).length < 2 ^ (prefixWord ++ tailWord_3455352).sum := by decide
  have hdescent : baseEnd_3455352 < baseStart_3455352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455380 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3455380 : Nat := 118140960795 + 3455380 * 2 ^ 59
def prefixEnd_3455380 : Nat := 4983230072969 + 3 ^ 40 * 3455380 * 2
def baseEnd_3455380 : Nat := 591423594644265347853001

theorem tailTrace_3455380 : CollatzResearch.WordTrace tailWord_3455380 prefixEnd_3455380 591423594644265347853001 := by
  unfold tailWord_3455380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63014031110877933383153797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84018708147837244510871729 63014031110877933383153797)
  ·
    refine ⟨11815130833289612509341337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63014031110877933383153797 11815130833289612509341337)
    ·
      refine ⟨8861348124967209382006003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11815130833289612509341337 8861348124967209382006003)
      ·
        refine ⟨13292022187450814073009005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861348124967209382006003 13292022187450814073009005)
        ·
          refine ⟨4984508320294055277378377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13292022187450814073009005 4984508320294055277378377)
          ·
            refine ⟨3738381240220541458033783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984508320294055277378377 3738381240220541458033783)
            ·
              refine ⟨5607571860330812187050675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738381240220541458033783 5607571860330812187050675)
              ·
                refine ⟨8411357790496218280576013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607571860330812187050675 8411357790496218280576013)
                ·
                  refine ⟨3154259171436081855216005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8411357790496218280576013 3154259171436081855216005)
                  ·
                    refine ⟨591423594644265347853001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154259171436081855216005 591423594644265347853001)
                    ·
                      rfl

theorem cell23_3455380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3455380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455380 prefixEnd_3455380 := by exact prefixLift 3455380
  have htrace : WordTrace (prefixWord ++ tailWord_3455380) baseStart_3455380 baseEnd_3455380 := by
    simpa [prefixWord, tailWord_3455380, baseEnd_3455380] using wordTrace_append hprefix tailTrace_3455380
  have hstable : (prefixWord ++ tailWord_3455380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455380).length < 2 ^ (prefixWord ++ tailWord_3455380).sum := by decide
  have hdescent : baseEnd_3455380 < baseStart_3455380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455393 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 6]
def baseStart_3455393 : Nat := 118140960795 + 3455393 * 2 ^ 59
def prefixEnd_3455393 : Nat := 4983230072969 + 3 ^ 40 * 3455393 * 2
def baseEnd_3455393 : Nat := 197141939909033832521827

theorem tailTrace_3455393 : CollatzResearch.WordTrace tailWord_3455393 prefixEnd_3455393 197141939909033832521827 := by
  unfold tailWord_3455393
  simp only [CollatzResearch.WordTrace]
  refine ⟨126028536370708769986530833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84019024247139179991020555 126028536370708769986530833)
  ·
    refine ⟨94521402278031577489898125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126028536370708769986530833 94521402278031577489898125)
    ·
      refine ⟨35445525854261841558711797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94521402278031577489898125 35445525854261841558711797)
      ·
        refine ⟨3323018048837047646129231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35445525854261841558711797 3323018048837047646129231)
        ·
          refine ⟨4984527073255571469193847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323018048837047646129231 4984527073255571469193847)
          ·
            refine ⟨7476790609883357203790771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984527073255571469193847 7476790609883357203790771)
            ·
              refine ⟨11215185914825035805686157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7476790609883357203790771 11215185914825035805686157)
              ·
                refine ⟨4205694718059388427132309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11215185914825035805686157 4205694718059388427132309)
                ·
                  refine ⟨197141939909033832521827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4205694718059388427132309 197141939909033832521827)
                  ·
                    rfl

theorem cell23_3455393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 6].length) (baseStart_3455393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455393 prefixEnd_3455393 := by exact prefixLift 3455393
  have htrace : WordTrace (prefixWord ++ tailWord_3455393) baseStart_3455393 baseEnd_3455393 := by
    simpa [prefixWord, tailWord_3455393, baseEnd_3455393] using wordTrace_append hprefix tailTrace_3455393
  have hstable : (prefixWord ++ tailWord_3455393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455393).length < 2 ^ (prefixWord ++ tailWord_3455393).sum := by decide
  have hdescent : baseEnd_3455393 < baseStart_3455393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455396 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_3455396 : Nat := 118140960795 + 3455396 * 2 ^ 59
def prefixEnd_3455396 : Nat := 4983230072969 + 3 ^ 40 * 3455396 * 2
def baseEnd_3455396 : Nat := 1774278999623267980958929

theorem tailTrace_3455396 : CollatzResearch.WordTrace tailWord_3455396 prefixEnd_3455396 1774278999623267980958929 := by
  unfold tailWord_3455396
  simp only [CollatzResearch.WordTrace]
  refine ⟨63014322894848950749445021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84019097193131934332593361 63014322894848950749445021)
  ·
    refine ⟨23630371085568356531041883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63014322894848950749445021 23630371085568356531041883)
    ·
      refine ⟨35445556628352534796562825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23630371085568356531041883 35445556628352534796562825)
      ·
        refine ⟨26584167471264401097422119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35445556628352534796562825 26584167471264401097422119)
        ·
          refine ⟨39876251206896601646133179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26584167471264401097422119 39876251206896601646133179)
          ·
            refine ⟨59814376810344902469199769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39876251206896601646133179 59814376810344902469199769)
            ·
              refine ⟨44860782607758676851899827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59814376810344902469199769 44860782607758676851899827)
              ·
                refine ⟨67291173911638015277849741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44860782607758676851899827 67291173911638015277849741)
                ·
                  refine ⟨25234190216864255729193653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67291173911638015277849741 25234190216864255729193653)
                  ·
                    refine ⟨2365705332831023974611905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25234190216864255729193653 2365705332831023974611905)
                    ·
                      refine ⟨1774278999623267980958929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365705332831023974611905 1774278999623267980958929)
                      ·
                        rfl

theorem cell23_3455396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_3455396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455396 prefixEnd_3455396 := by exact prefixLift 3455396
  have htrace : WordTrace (prefixWord ++ tailWord_3455396) baseStart_3455396 baseEnd_3455396 := by
    simpa [prefixWord, tailWord_3455396, baseEnd_3455396] using wordTrace_append hprefix tailTrace_3455396
  have hstable : (prefixWord ++ tailWord_3455396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455396).length < 2 ^ (prefixWord ++ tailWord_3455396).sum := by decide
  have hdescent : baseEnd_3455396 < baseStart_3455396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455439 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_3455439 : Nat := 118140960795 + 3455439 * 2 ^ 59
def prefixEnd_3455439 : Nat := 4983230072969 + 3 ^ 40 * 3455439 * 2
def baseEnd_3455439 : Nat := 1774301079291411312721231

theorem tailTrace_3455439 : CollatzResearch.WordTrace tailWord_3455439 prefixEnd_3455439 1774301079291411312721231 := by
  unfold tailWord_3455439
  simp only [CollatzResearch.WordTrace]
  refine ⟨126030214128542119842705371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84020142752361413228470247 126030214128542119842705371)
  ·
    refine ⟨189045321192813179764058057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126030214128542119842705371 189045321192813179764058057)
    ·
      refine ⟨141783990894609884823043543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189045321192813179764058057 141783990894609884823043543)
      ·
        refine ⟨212675986341914827234565315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141783990894609884823043543 212675986341914827234565315)
        ·
          refine ⟨319013979512872240851847973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212675986341914827234565315 319013979512872240851847973)
          ·
            refine ⟨59815121158663545159721495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319013979512872240851847973 59815121158663545159721495)
            ·
              refine ⟨89722681737995317739582243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59815121158663545159721495 89722681737995317739582243)
              ·
                refine ⟨134584022606992976609373365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89722681737995317739582243 134584022606992976609373365)
                ·
                  refine ⟨12617252119405591557128753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134584022606992976609373365 12617252119405591557128753)
                  ·
                    refine ⟨9462939089554193667846565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12617252119405591557128753 9462939089554193667846565)
                    ·
                      refine ⟨1774301079291411312721231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9462939089554193667846565 1774301079291411312721231)
                      ·
                        rfl

theorem cell23_3455439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_3455439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455439 prefixEnd_3455439 := by exact prefixLift 3455439
  have htrace : WordTrace (prefixWord ++ tailWord_3455439) baseStart_3455439 baseEnd_3455439 := by
    simpa [prefixWord, tailWord_3455439, baseEnd_3455439] using wordTrace_append hprefix tailTrace_3455439
  have hstable : (prefixWord ++ tailWord_3455439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455439).length < 2 ^ (prefixWord ++ tailWord_3455439).sum := by decide
  have hdescent : baseEnd_3455439 < baseStart_3455439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455453 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3455453 : Nat := 118140960795 + 3455453 * 2 ^ 59
def prefixEnd_3455453 : Nat := 4983230072969 + 3 ^ 40 * 3455453 * 2
def baseEnd_3455453 : Nat := 591436089340191419315389

theorem tailTrace_3455453 : CollatzResearch.WordTrace tailWord_3455453 prefixEnd_3455453 591436089340191419315389 := by
  unfold tailWord_3455453
  simp only [CollatzResearch.WordTrace]
  refine ⟨126030724750491400233715013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84020483166994266822476675 126030724750491400233715013)
  ·
    refine ⟨23630760890717137543821565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126030724750491400233715013 23630760890717137543821565)
    ·
      refine ⟨8861535334018926578933087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23630760890717137543821565 8861535334018926578933087)
      ·
        refine ⟨13292303001028389868399631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861535334018926578933087 13292303001028389868399631)
        ·
          refine ⟨19938454501542584802599447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13292303001028389868399631 19938454501542584802599447)
          ·
            refine ⟨29907681752313877203899171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19938454501542584802599447 29907681752313877203899171)
            ·
              refine ⟨44861522628470815805848757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29907681752313877203899171 44861522628470815805848757)
              ·
                refine ⟨4205767746419138981798321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44861522628470815805848757 4205767746419138981798321)
                ·
                  refine ⟨3154325809814354236348741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205767746419138981798321 3154325809814354236348741)
                  ·
                    refine ⟨591436089340191419315389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154325809814354236348741 591436089340191419315389)
                    ·
                      rfl

theorem cell23_3455453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3455453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455453 prefixEnd_3455453 := by exact prefixLift 3455453
  have htrace : WordTrace (prefixWord ++ tailWord_3455453) baseStart_3455453 baseEnd_3455453 := by
    simpa [prefixWord, tailWord_3455453, baseEnd_3455453] using wordTrace_append hprefix tailTrace_3455453
  have hstable : (prefixWord ++ tailWord_3455453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455453).length < 2 ^ (prefixWord ++ tailWord_3455453).sum := by decide
  have hdescent : baseEnd_3455453 < baseStart_3455453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455456 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_3455456 : Nat := 118140960795 + 3455456 * 2 ^ 59
def prefixEnd_3455456 : Nat := 4983230072969 + 3 ^ 40 * 3455456 * 2
def baseEnd_3455456 : Nat := 1774309808462537746208653

theorem tailTrace_3455456 : CollatzResearch.WordTrace tailWord_3455456 prefixEnd_3455456 1774309808462537746208653 := by
  unfold tailWord_3455456
  simp only [CollatzResearch.WordTrace]
  refine ⟨63015417084740265873037111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84020556112987021164049481 63015417084740265873037111)
  ·
    refine ⟨94523125627110398809555667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63015417084740265873037111 94523125627110398809555667)
    ·
      refine ⟨141784688440665598214333501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94523125627110398809555667 141784688440665598214333501)
      ·
        refine ⟨53169258165249599330375063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141784688440665598214333501 53169258165249599330375063)
        ·
          refine ⟨79753887247874398995562595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53169258165249599330375063 79753887247874398995562595)
          ·
            refine ⟨119630830871811598493343893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79753887247874398995562595 119630830871811598493343893)
            ·
              refine ⟨5607695197116168679375495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119630830871811598493343893 5607695197116168679375495)
              ·
                refine ⟨8411542795674253019063243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607695197116168679375495 8411542795674253019063243)
                ·
                  refine ⟨12617314193511379528594865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411542795674253019063243 12617314193511379528594865)
                  ·
                    refine ⟨9462985645133534646446149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12617314193511379528594865 9462985645133534646446149)
                    ·
                      refine ⟨1774309808462537746208653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9462985645133534646446149 1774309808462537746208653)
                      ·
                        rfl

theorem cell23_3455456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_3455456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455456 prefixEnd_3455456 := by exact prefixLift 3455456
  have htrace : WordTrace (prefixWord ++ tailWord_3455456) baseStart_3455456 baseEnd_3455456 := by
    simpa [prefixWord, tailWord_3455456, baseEnd_3455456] using wordTrace_append hprefix tailTrace_3455456
  have hstable : (prefixWord ++ tailWord_3455456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455456).length < 2 ^ (prefixWord ++ tailWord_3455456).sum := by decide
  have hdescent : baseEnd_3455456 < baseStart_3455456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455463 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3455463 : Nat := 118140960795 + 3455463 * 2 ^ 59
def prefixEnd_3455463 : Nat := 4983230072969 + 3 ^ 40 * 3455463 * 2
def baseEnd_3455463 : Nat := 1774313402827119218821121

theorem tailTrace_3455463 : CollatzResearch.WordTrace tailWord_3455463 prefixEnd_3455463 1774313402827119218821121 := by
  unfold tailWord_3455463
  simp only [CollatzResearch.WordTrace]
  refine ⟨126031089480455171941579043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84020726320303447961052695 126031089480455171941579043)
  ·
    refine ⟨189046634220682757912368565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126031089480455171941579043 189046634220682757912368565)
    ·
      refine ⟨17723121958189008554284553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189046634220682757912368565 17723121958189008554284553)
      ·
        refine ⟨13292341468641756415713415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17723121958189008554284553 13292341468641756415713415)
        ·
          refine ⟨19938512202962634623570123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13292341468641756415713415 19938512202962634623570123)
          ·
            refine ⟨29907768304443951935355185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19938512202962634623570123 29907768304443951935355185)
            ·
              refine ⟨22430826228332963951516389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29907768304443951935355185 22430826228332963951516389)
              ·
                refine ⟨4205779917812430740909323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22430826228332963951516389 4205779917812430740909323)
                ·
                  refine ⟨6308669876718646111363985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205779917812430740909323 6308669876718646111363985)
                  ·
                    refine ⟨4731502407538984583522989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6308669876718646111363985 4731502407538984583522989)
                    ·
                      refine ⟨1774313402827119218821121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4731502407538984583522989 1774313402827119218821121)
                      ·
                        rfl

theorem cell23_3455463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3455463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455463 prefixEnd_3455463 := by exact prefixLift 3455463
  have htrace : WordTrace (prefixWord ++ tailWord_3455463) baseStart_3455463 baseEnd_3455463 := by
    simpa [prefixWord, tailWord_3455463, baseEnd_3455463] using wordTrace_append hprefix tailTrace_3455463
  have hstable : (prefixWord ++ tailWord_3455463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455463).length < 2 ^ (prefixWord ++ tailWord_3455463).sum := by decide
  have hdescent : baseEnd_3455463 < baseStart_3455463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455567 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 2, 2, 2]
def baseStart_3455567 : Nat := 118140960795 + 3455567 * 2 ^ 59
def prefixEnd_3455567 : Nat := 4983230072969 + 3 ^ 40 * 3455567 * 2
def baseEnd_3455567 : Nat := 1774366804815186811920643

theorem tailTrace_3455567 : CollatzResearch.WordTrace tailWord_3455567 prefixEnd_3455567 1774366804815186811920643 := by
  unfold tailWord_3455567
  simp only [CollatzResearch.WordTrace]
  refine ⟨126034882672078397703364955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84023255114718931802243303 126034882672078397703364955)
  ·
    refine ⟨189052324008117596555047433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126034882672078397703364955 189052324008117596555047433)
    ·
      refine ⟨141789243006088197416285575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189052324008117596555047433 141789243006088197416285575)
      ·
        refine ⟨212683864509132296124428363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141789243006088197416285575 212683864509132296124428363)
        ·
          refine ⟨319025796763698444186642545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212683864509132296124428363 319025796763698444186642545)
          ·
            refine ⟨239269347572773833139981909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319025796763698444186642545 239269347572773833139981909)
            ·
              refine ⟨2803937666868443357109163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 239269347572773833139981909 2803937666868443357109163)
              ·
                refine ⟨4205906500302665035663745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803937666868443357109163 4205906500302665035663745)
                ·
                  refine ⟨3154429875226998776747809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205906500302665035663745 3154429875226998776747809)
                  ·
                    refine ⟨2365822406420249082560857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3154429875226998776747809 2365822406420249082560857)
                    ·
                      refine ⟨1774366804815186811920643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365822406420249082560857 1774366804815186811920643)
                      ·
                        rfl

theorem cell23_3455567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 2, 2].length) (baseStart_3455567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455567 prefixEnd_3455567 := by exact prefixLift 3455567
  have htrace : WordTrace (prefixWord ++ tailWord_3455567) baseStart_3455567 baseEnd_3455567 := by
    simpa [prefixWord, tailWord_3455567, baseEnd_3455567] using wordTrace_append hprefix tailTrace_3455567
  have hstable : (prefixWord ++ tailWord_3455567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455567).length < 2 ^ (prefixWord ++ tailWord_3455567).sum := by decide
  have hdescent : baseEnd_3455567 < baseStart_3455567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455596 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3455596 : Nat := 118140960795 + 3455596 * 2 ^ 59
def prefixEnd_3455596 : Nat := 4983230072969 + 3 ^ 40 * 3455596 * 2
def baseEnd_3455596 : Nat := 1774381695754167198458009

theorem tailTrace_3455596 : CollatzResearch.WordTrace tailWord_3455596 prefixEnd_3455596 1774381695754167198458009 := by
  unfold tailWord_3455596
  simp only [CollatzResearch.WordTrace]
  refine ⟨63017970194486667828085321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84023960259315557104113761 63017970194486667828085321)
  ·
    refine ⟨47263477645865000871063991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63017970194486667828085321 47263477645865000871063991)
    ·
      refine ⟨70895216468797501306595987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47263477645865000871063991 70895216468797501306595987)
      ·
        refine ⟨106342824703196251959893981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70895216468797501306595987 106342824703196251959893981)
        ·
          refine ⟨39878559263698594484960243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106342824703196251959893981 39878559263698594484960243)
          ·
            refine ⟨59817838895547891727440365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39878559263698594484960243 59817838895547891727440365)
            ·
              refine ⟨22431689585830459397790137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59817838895547891727440365 22431689585830459397790137)
              ·
                refine ⟨16823767189372844548342603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22431689585830459397790137 16823767189372844548342603)
                ·
                  refine ⟨25235650784059266822513905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16823767189372844548342603 25235650784059266822513905)
                  ·
                    refine ⟨18926738088044450116885429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25235650784059266822513905 18926738088044450116885429)
                    ·
                      refine ⟨1774381695754167198458009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18926738088044450116885429 1774381695754167198458009)
                      ·
                        rfl

theorem cell23_3455596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3455596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455596 prefixEnd_3455596 := by exact prefixLift 3455596
  have htrace : WordTrace (prefixWord ++ tailWord_3455596) baseStart_3455596 baseEnd_3455596 := by
    simpa [prefixWord, tailWord_3455596, baseEnd_3455596] using wordTrace_append hprefix tailTrace_3455596
  have hstable : (prefixWord ++ tailWord_3455596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455596).length < 2 ^ (prefixWord ++ tailWord_3455596).sum := by decide
  have hdescent : baseEnd_3455596 < baseStart_3455596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455663 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 6]
def baseStart_3455663 : Nat := 118140960795 + 3455663 * 2 ^ 59
def prefixEnd_3455663 : Nat := 4983230072969 + 3 ^ 40 * 3455663 * 2
def baseEnd_3455663 : Nat := 197157344328668715146689

theorem tailTrace_3455663 : CollatzResearch.WordTrace tailWord_3455663 prefixEnd_3455663 197157344328668715146689 := by
  unfold tailWord_3455663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126038384079730606098859643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84025589386487070732573095 126038384079730606098859643)
  ·
    refine ⟨189057576119595909148289465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126038384079730606098859643 189057576119595909148289465)
    ·
      refine ⟨141793182089696931861217099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189057576119595909148289465 141793182089696931861217099)
      ·
        refine ⟨212689773134545397791825649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141793182089696931861217099 212689773134545397791825649)
        ·
          refine ⟨159517329850909048343869237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212689773134545397791825649 159517329850909048343869237)
          ·
            refine ⟨14954749673522723282237741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159517329850909048343869237 14954749673522723282237741)
            ·
              refine ⟨5608031127571021230839153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14954749673522723282237741 5608031127571021230839153)
              ·
                refine ⟨4206023345678265923129365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608031127571021230839153 4206023345678265923129365)
                ·
                  refine ⟨197157344328668715146689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4206023345678265923129365 197157344328668715146689)
                  ·
                    rfl

theorem cell23_3455663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 6].length) (baseStart_3455663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455663 prefixEnd_3455663 := by exact prefixLift 3455663
  have htrace : WordTrace (prefixWord ++ tailWord_3455663) baseStart_3455663 baseEnd_3455663 := by
    simpa [prefixWord, tailWord_3455663, baseEnd_3455663] using wordTrace_append hprefix tailTrace_3455663
  have hstable : (prefixWord ++ tailWord_3455663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455663).length < 2 ^ (prefixWord ++ tailWord_3455663).sum := by decide
  have hdescent : baseEnd_3455663 < baseStart_3455663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455680 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 6]
def baseStart_3455680 : Nat := 118140960795 + 3455680 * 2 ^ 59
def prefixEnd_3455680 : Nat := 4983230072969 + 3 ^ 40 * 3455680 * 2
def baseEnd_3455680 : Nat := 197158314236571652200847

theorem tailTrace_3455680 : CollatzResearch.WordTrace tailWord_3455680 prefixEnd_3455680 197158314236571652200847 := by
  unfold tailWord_3455680
  simp only [CollatzResearch.WordTrace]
  refine ⟨63019502060334509001114247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84026002747112678668152329 63019502060334509001114247)
  ·
    refine ⟨94529253090501763501671371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63019502060334509001114247 94529253090501763501671371)
    ·
      refine ⟨141793879635752645252507057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94529253090501763501671371 141793879635752645252507057)
      ·
        refine ⟨106345409726814483939380293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141793879635752645252507057 106345409726814483939380293)
        ·
          refine ⟨19939764323777715738633805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106345409726814483939380293 19939764323777715738633805)
          ·
            refine ⟨7477411621416643401987677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19939764323777715738633805 7477411621416643401987677)
            ·
              refine ⟨2804029358031241275745379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7477411621416643401987677 2804029358031241275745379)
              ·
                refine ⟨4206044037046861913618069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804029358031241275745379 4206044037046861913618069)
                ·
                  refine ⟨197158314236571652200847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4206044037046861913618069 197158314236571652200847)
                  ·
                    rfl

theorem cell23_3455680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 6].length) (baseStart_3455680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455680 prefixEnd_3455680 := by exact prefixLift 3455680
  have htrace : WordTrace (prefixWord ++ tailWord_3455680) baseStart_3455680 baseEnd_3455680 := by
    simpa [prefixWord, tailWord_3455680, baseEnd_3455680] using wordTrace_append hprefix tailTrace_3455680
  have hstable : (prefixWord ++ tailWord_3455680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455680).length < 2 ^ (prefixWord ++ tailWord_3455680).sum := by decide
  have hdescent : baseEnd_3455680 < baseStart_3455680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455701 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_3455701 : Nat := 118140960795 + 3455701 * 2 ^ 59
def prefixEnd_3455701 : Nat := 4983230072969 + 3 ^ 40 * 3455701 * 2
def baseEnd_3455701 : Nat := 591478537074296429215009

theorem tailTrace_3455701 : CollatzResearch.WordTrace tailWord_3455701 prefixEnd_3455701 591478537074296429215009 := by
  unfold tailWord_3455701
  simp only [CollatzResearch.WordTrace]
  refine ⟨126039770053592938588742957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84026513369061959059161971 126039770053592938588742957)
  ·
    refine ⟨47264913770097351970778609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126039770053592938588742957 47264913770097351970778609)
    ·
      refine ⟨35448685327573013978083957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47264913770097351970778609 35448685327573013978083957)
      ·
        refine ⟨3323314249459970060445371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35448685327573013978083957 3323314249459970060445371)
        ·
          refine ⟨4984971374189955090668057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323314249459970060445371 4984971374189955090668057)
          ·
            refine ⟨3738728530642466318001043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984971374189955090668057 3738728530642466318001043)
            ·
              refine ⟨5608092795963699477001565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738728530642466318001043 5608092795963699477001565)
              ·
                refine ⟨2103034798486387303875587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5608092795963699477001565 2103034798486387303875587)
                ·
                  refine ⟨3154552197729580955813381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103034798486387303875587 3154552197729580955813381)
                  ·
                    refine ⟨591478537074296429215009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154552197729580955813381 591478537074296429215009)
                    ·
                      rfl

theorem cell23_3455701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_3455701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455701 prefixEnd_3455701 := by exact prefixLift 3455701
  have htrace : WordTrace (prefixWord ++ tailWord_3455701) baseStart_3455701 baseEnd_3455701 := by
    simpa [prefixWord, tailWord_3455701, baseEnd_3455701] using wordTrace_append hprefix tailTrace_3455701
  have hstable : (prefixWord ++ tailWord_3455701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455701).length < 2 ^ (prefixWord ++ tailWord_3455701).sum := by decide
  have hdescent : baseEnd_3455701 < baseStart_3455701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455717 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 2, 3, 2]
def baseStart_3455717 : Nat := 118140960795 + 3455717 * 2 ^ 59
def prefixEnd_3455717 : Nat := 4983230072969 + 3 ^ 40 * 3455717 * 2
def baseEnd_3455717 : Nat := 1774443826913361225044953

theorem tailTrace_3455717 : CollatzResearch.WordTrace tailWord_3455717 prefixEnd_3455717 1774443826913361225044953 := by
  unfold tailWord_3455717
  simp only [CollatzResearch.WordTrace]
  refine ⟨126040353621534973321325405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84026902414356648880883603 126040353621534973321325405)
  ·
    refine ⟨47265132608075614995497027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126040353621534973321325405 47265132608075614995497027)
    ·
      refine ⟨70897698912113422493245541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47265132608075614995497027 70897698912113422493245541)
      ·
        refine ⟨13293318546021266717483539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70897698912113422493245541 13293318546021266717483539)
        ·
          refine ⟨19939977819031900076225309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13293318546021266717483539 19939977819031900076225309)
          ·
            refine ⟨7477491682136962528584491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19939977819031900076225309 7477491682136962528584491)
            ·
              refine ⟨11216237523205443792876737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477491682136962528584491 11216237523205443792876737)
              ·
                refine ⟨8412178142404082844657553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11216237523205443792876737 8412178142404082844657553)
                ·
                  refine ⟨6309133606803062133493165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412178142404082844657553 6309133606803062133493165)
                  ·
                    refine ⟨2365925102551148300059937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6309133606803062133493165 2365925102551148300059937)
                    ·
                      refine ⟨1774443826913361225044953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365925102551148300059937 1774443826913361225044953)
                      ·
                        rfl

theorem cell23_3455717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_3455717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455717 prefixEnd_3455717 := by exact prefixLift 3455717
  have htrace : WordTrace (prefixWord ++ tailWord_3455717) baseStart_3455717 baseEnd_3455717 := by
    simpa [prefixWord, tailWord_3455717, baseEnd_3455717] using wordTrace_append hprefix tailTrace_3455717
  have hstable : (prefixWord ++ tailWord_3455717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455717).length < 2 ^ (prefixWord ++ tailWord_3455717).sum := by decide
  have hdescent : baseEnd_3455717 < baseStart_3455717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455743 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_3455743 : Nat := 118140960795 + 3455743 * 2 ^ 59
def prefixEnd_3455743 : Nat := 4983230072969 + 3 ^ 40 * 3455743 * 2
def baseEnd_3455743 : Nat := 1774457177410378123319833

theorem tailTrace_3455743 : CollatzResearch.WordTrace tailWord_3455743 prefixEnd_3455743 1774457177410378123319833 := by
  unfold tailWord_3455743
  simp only [CollatzResearch.WordTrace]
  refine ⟨126041301919440779761771883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84027534612960519841181255 126041301919440779761771883)
  ·
    refine ⟨189061952879161169642657825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126041301919440779761771883 189061952879161169642657825)
    ·
      refine ⟨141796464659370877231993369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189061952879161169642657825 141796464659370877231993369)
      ·
        refine ⟨106347348494528157923995027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141796464659370877231993369 106347348494528157923995027)
        ·
          refine ⟨159521022741792236885992541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106347348494528157923995027 159521022741792236885992541)
          ·
            refine ⟨59820383528172088832247203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159521022741792236885992541 59820383528172088832247203)
            ·
              refine ⟨89730575292258133248370805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59820383528172088832247203 89730575292258133248370805)
              ·
                refine ⟨8412241433649199992034763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89730575292258133248370805 8412241433649199992034763)
                ·
                  refine ⟨12618362150473799988052145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412241433649199992034763 12618362150473799988052145)
                  ·
                    refine ⟨9463771612855349991039109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12618362150473799988052145 9463771612855349991039109)
                    ·
                      refine ⟨1774457177410378123319833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9463771612855349991039109 1774457177410378123319833)
                      ·
                        rfl

theorem cell23_3455743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_3455743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455743 prefixEnd_3455743 := by exact prefixLift 3455743
  have htrace : WordTrace (prefixWord ++ tailWord_3455743) baseStart_3455743 baseEnd_3455743 := by
    simpa [prefixWord, tailWord_3455743, baseEnd_3455743] using wordTrace_append hprefix tailTrace_3455743
  have hstable : (prefixWord ++ tailWord_3455743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455743).length < 2 ^ (prefixWord ++ tailWord_3455743).sum := by decide
  have hdescent : baseEnd_3455743 < baseStart_3455743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455767 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3455767 : Nat := 118140960795 + 3455767 * 2 ^ 59
def prefixEnd_3455767 : Nat := 4983230072969 + 3 ^ 40 * 3455767 * 2
def baseEnd_3455767 : Nat := 1774469500946086029419723

theorem tailTrace_3455767 : CollatzResearch.WordTrace tailWord_3455767 prefixEnd_3455767 1774469500946086029419723 := by
  unfold tailWord_3455767
  simp only [CollatzResearch.WordTrace]
  refine ⟨126042177271353831860645555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84028118180902554573763703 126042177271353831860645555)
  ·
    refine ⟨189063265907030747790968333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126042177271353831860645555 189063265907030747790968333)
    ·
      refine ⟨70898724715136530421613125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189063265907030747790968333 70898724715136530421613125)
      ·
        refine ⟨13293510884088099454052461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70898724715136530421613125 13293510884088099454052461)
        ·
          refine ⟨4985066581533037295269673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13293510884088099454052461 4985066581533037295269673)
          ·
            refine ⟨3738799936149777971452255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4985066581533037295269673 3738799936149777971452255)
            ·
              refine ⟨5608199904224666957178383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738799936149777971452255 5608199904224666957178383)
              ·
                refine ⟨8412299856337000435767575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608199904224666957178383 8412299856337000435767575)
                ·
                  refine ⟨12618449784505500653651363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412299856337000435767575 12618449784505500653651363)
                  ·
                    refine ⟨18927674676758250980477045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12618449784505500653651363 18927674676758250980477045)
                    ·
                      refine ⟨1774469500946086029419723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18927674676758250980477045 1774469500946086029419723)
                      ·
                        rfl

theorem cell23_3455767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3455767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455767 prefixEnd_3455767 := by exact prefixLift 3455767
  have htrace : WordTrace (prefixWord ++ tailWord_3455767) baseStart_3455767 baseEnd_3455767 := by
    simpa [prefixWord, tailWord_3455767, baseEnd_3455767] using wordTrace_append hprefix tailTrace_3455767
  have hstable : (prefixWord ++ tailWord_3455767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455767).length < 2 ^ (prefixWord ++ tailWord_3455767).sum := by decide
  have hdescent : baseEnd_3455767 < baseStart_3455767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455797 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3455797 : Nat := 118140960795 + 3455797 * 2 ^ 59
def prefixEnd_3455797 : Nat := 4983230072969 + 3 ^ 40 * 3455797 * 2
def baseEnd_3455797 : Nat := 1774484905365720912044585

theorem tailTrace_3455797 : CollatzResearch.WordTrace tailWord_3455797 prefixEnd_3455797 1774484905365720912044585 := by
  unfold tailWord_3455797
  simp only [CollatzResearch.WordTrace]
  refine ⟨126043271461245146984237645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84028847640830097989491763 126043271461245146984237645)
  ·
    refine ⟨47266226797966930119089117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126043271461245146984237645 47266226797966930119089117)
    ·
      refine ⟨17724835049237598794658419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47266226797966930119089117 17724835049237598794658419)
      ·
        refine ⟨26587252573856398191987629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17724835049237598794658419 26587252573856398191987629)
        ·
          refine ⟨9970219715196149321995361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26587252573856398191987629 9970219715196149321995361)
          ·
            refine ⟨7477664786397111991496521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9970219715196149321995361 7477664786397111991496521)
            ·
              refine ⟨5608248589797833993622391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7477664786397111991496521 5608248589797833993622391)
              ·
                refine ⟨8412372884696750990433587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608248589797833993622391 8412372884696750990433587)
                ·
                  refine ⟨12618559327045126485650381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412372884696750990433587 12618559327045126485650381)
                  ·
                    refine ⟨4731959747641922432118893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12618559327045126485650381 4731959747641922432118893)
                    ·
                      refine ⟨1774484905365720912044585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4731959747641922432118893 1774484905365720912044585)
                      ·
                        rfl

theorem cell23_3455797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3455797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455797 prefixEnd_3455797 := by exact prefixLift 3455797
  have htrace : WordTrace (prefixWord ++ tailWord_3455797) baseStart_3455797 baseEnd_3455797 := by
    simpa [prefixWord, tailWord_3455797, baseEnd_3455797] using wordTrace_append hprefix tailTrace_3455797
  have hstable : (prefixWord ++ tailWord_3455797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455797).length < 2 ^ (prefixWord ++ tailWord_3455797).sum := by decide
  have hdescent : baseEnd_3455797 < baseStart_3455797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455807 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 3, 3, 2]
def baseStart_3455807 : Nat := 118140960795 + 3455807 * 2 ^ 59
def prefixEnd_3455807 : Nat := 4983230072969 + 3 ^ 40 * 3455807 * 2
def baseEnd_3455807 : Nat := 1774490040172265872919539

theorem tailTrace_3455807 : CollatzResearch.WordTrace tailWord_3455807 prefixEnd_3455807 1774490040172265872919539 := by
  unfold tailWord_3455807
  simp only [CollatzResearch.WordTrace]
  refine ⟨126043636191208918692101675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84029090794139279128067783 126043636191208918692101675)
  ·
    refine ⟨189065454286813378038152513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126043636191208918692101675 189065454286813378038152513)
    ·
      refine ⟨141799090715110033528614385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189065454286813378038152513 141799090715110033528614385)
      ·
        refine ⟨106349318036332525146460789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141799090715110033528614385 106349318036332525146460789)
        ·
          refine ⟨9970248565906174232480699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106349318036332525146460789 9970248565906174232480699)
          ·
            refine ⟨14955372848859261348721049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970248565906174232480699 14955372848859261348721049)
            ·
              refine ⟨11216529636644446011540787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14955372848859261348721049 11216529636644446011540787)
              ·
                refine ⟨16824794454966669017311181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11216529636644446011540787 16824794454966669017311181)
                ·
                  refine ⟨6309297920612500881491693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16824794454966669017311181 6309297920612500881491693)
                  ·
                    refine ⟨2365986720229687830559385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6309297920612500881491693 2365986720229687830559385)
                    ·
                      refine ⟨1774490040172265872919539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365986720229687830559385 1774490040172265872919539)
                      ·
                        rfl

theorem cell23_3455807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_3455807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455807 prefixEnd_3455807 := by exact prefixLift 3455807
  have htrace : WordTrace (prefixWord ++ tailWord_3455807) baseStart_3455807 baseEnd_3455807 := by
    simpa [prefixWord, tailWord_3455807, baseEnd_3455807] using wordTrace_append hprefix tailTrace_3455807
  have hstable : (prefixWord ++ tailWord_3455807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455807).length < 2 ^ (prefixWord ++ tailWord_3455807).sum := by decide
  have hdescent : baseEnd_3455807 < baseStart_3455807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455824 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 1, 3, 2]
def baseStart_3455824 : Nat := 118140960795 + 3455824 * 2 ^ 59
def prefixEnd_3455824 : Nat := 4983230072969 + 3 ^ 40 * 3455824 * 2
def baseEnd_3455824 : Nat := 1774498769343392306406961

theorem tailTrace_3455824 : CollatzResearch.WordTrace tailWord_3455824 prefixEnd_3455824 1774498769343392306406961 := by
  unfold tailWord_3455824
  simp only [CollatzResearch.WordTrace]
  refine ⟨63022128116073665297735263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84029504154764887063647017 63022128116073665297735263)
  ·
    refine ⟨94533192174110497946602895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63022128116073665297735263 94533192174110497946602895)
    ·
      refine ⟨141799788261165746919904343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94533192174110497946602895 141799788261165746919904343)
      ·
        refine ⟨212699682391748620379856515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141799788261165746919904343 212699682391748620379856515)
        ·
          refine ⟨319049523587622930569784773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212699682391748620379856515 319049523587622930569784773)
          ·
            refine ⟨59821785672679299481834645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319049523587622930569784773 59821785672679299481834645)
            ·
              refine ⟨2804146203406842163210999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59821785672679299481834645 2804146203406842163210999)
              ·
                refine ⟨4206219305110263244816499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804146203406842163210999 4206219305110263244816499)
                ·
                  refine ⟨6309328957665394867224749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206219305110263244816499 6309328957665394867224749)
                  ·
                    refine ⟨2365998359124523075209281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6309328957665394867224749 2365998359124523075209281)
                    ·
                      refine ⟨1774498769343392306406961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2365998359124523075209281 1774498769343392306406961)
                      ·
                        rfl

theorem cell23_3455824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 3, 2].length) (baseStart_3455824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455824 prefixEnd_3455824 := by exact prefixLift 3455824
  have htrace : WordTrace (prefixWord ++ tailWord_3455824) baseStart_3455824 baseEnd_3455824 := by
    simpa [prefixWord, tailWord_3455824, baseEnd_3455824] using wordTrace_append hprefix tailTrace_3455824
  have hstable : (prefixWord ++ tailWord_3455824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455824).length < 2 ^ (prefixWord ++ tailWord_3455824).sum := by decide
  have hdescent : baseEnd_3455824 < baseStart_3455824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455877 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 5]
def baseStart_3455877 : Nat := 118140960795 + 3455877 * 2 ^ 59
def prefixEnd_3455877 : Nat := 4983230072969 + 3 ^ 40 * 3455877 * 2
def baseEnd_3455877 : Nat := 197169553757564511004913

theorem tailTrace_3455877 : CollatzResearch.WordTrace tailWord_3455877 prefixEnd_3455877 197169553757564511004913 := by
  unfold tailWord_3455877
  simp only [CollatzResearch.WordTrace]
  refine ⟨126046189300955320647149885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84030792867303547098099923 126046189300955320647149885)
  ·
    refine ⟨47267320987858245242681207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126046189300955320647149885 47267320987858245242681207)
    ·
      refine ⟨70900981481787367864021811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47267320987858245242681207 70900981481787367864021811)
      ·
        refine ⟨106351472222681051796032717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70900981481787367864021811 106351472222681051796032717)
        ·
          refine ⟨39881802083505394423512269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106351472222681051796032717 39881802083505394423512269)
          ·
            refine ⟨14955675781314522908817101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39881802083505394423512269 14955675781314522908817101)
            ·
              refine ⟨5608378417992946090806413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14955675781314522908817101 5608378417992946090806413)
              ·
                refine ⟨2103141906747354784052405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5608378417992946090806413 2103141906747354784052405)
                ·
                  refine ⟨197169553757564511004913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103141906747354784052405 197169553757564511004913)
                  ·
                    rfl

theorem cell23_3455877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_3455877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455877 prefixEnd_3455877 := by exact prefixLift 3455877
  have htrace : WordTrace (prefixWord ++ tailWord_3455877) baseStart_3455877 baseEnd_3455877 := by
    simpa [prefixWord, tailWord_3455877, baseEnd_3455877] using wordTrace_append hprefix tailTrace_3455877
  have hstable : (prefixWord ++ tailWord_3455877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455877).length < 2 ^ (prefixWord ++ tailWord_3455877).sum := by decide
  have hdescent : baseEnd_3455877 < baseStart_3455877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455924 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3455924 : Nat := 118140960795 + 3455924 * 2 ^ 59
def prefixEnd_3455924 : Nat := 4983230072969 + 3 ^ 40 * 3455924 * 2
def baseEnd_3455924 : Nat := 591516705802947305052167

theorem tailTrace_3455924 : CollatzResearch.WordTrace tailWord_3455924 prefixEnd_3455924 591516705802947305052167 := by
  unfold tailWord_3455924
  simp only [CollatzResearch.WordTrace]
  refine ⟨63023951765892523837055413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84031935687856698449407217 63023951765892523837055413)
  ·
    refine ⟨5908495478052424109723945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63023951765892523837055413 5908495478052424109723945)
    ·
      refine ⟨4431371608539318082292959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5908495478052424109723945 4431371608539318082292959)
      ·
        refine ⟨6647057412808977123439439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431371608539318082292959 6647057412808977123439439)
        ·
          refine ⟨9970586119213465685159159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647057412808977123439439 9970586119213465685159159)
          ·
            refine ⟨14955879178820198527738739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970586119213465685159159 14955879178820198527738739)
            ·
              refine ⟨22433818768230297791608109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14955879178820198527738739 22433818768230297791608109)
              ·
                refine ⟨8412682038086361671853041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22433818768230297791608109 8412682038086361671853041)
                ·
                  refine ⟨6309511528564771253889781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412682038086361671853041 6309511528564771253889781)
                  ·
                    refine ⟨591516705802947305052167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6309511528564771253889781 591516705802947305052167)
                    ·
                      rfl

theorem cell23_3455924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3455924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455924 prefixEnd_3455924 := by exact prefixLift 3455924
  have htrace : WordTrace (prefixWord ++ tailWord_3455924) baseStart_3455924 baseEnd_3455924 := by
    simpa [prefixWord, tailWord_3455924, baseEnd_3455924] using wordTrace_append hprefix tailTrace_3455924
  have hstable : (prefixWord ++ tailWord_3455924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455924).length < 2 ^ (prefixWord ++ tailWord_3455924).sum := by decide
  have hdescent : baseEnd_3455924 < baseStart_3455924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455947 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 3]
def baseStart_3455947 : Nat := 118140960795 + 3455947 * 2 ^ 59
def prefixEnd_3455947 : Nat := 4983230072969 + 3 ^ 40 * 3455947 * 2
def baseEnd_3455947 : Nat := 1774561927463895325168895

theorem tailTrace_3455947 : CollatzResearch.WordTrace tailWord_3455947 prefixEnd_3455947 1774561927463895325168895 := by
  unfold tailWord_3455947
  simp only [CollatzResearch.WordTrace]
  refine ⟨126048742410701722602198095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84032494940467815068132063 126048742410701722602198095)
  ·
    refine ⟨189073113616052583903297143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126048742410701722602198095 189073113616052583903297143)
    ·
      refine ⟨283609670424078875854945715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189073113616052583903297143 283609670424078875854945715)
      ·
        refine ⟨425414505636118313782418573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283609670424078875854945715 425414505636118313782418573)
        ·
          refine ⟨159530439613544367668406965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425414505636118313782418573 159530439613544367668406965)
          ·
            refine ⟨14955978713769784468913153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159530439613544367668406965 14955978713769784468913153)
            ·
              refine ⟨11216984035327338351684865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14955978713769784468913153 11216984035327338351684865)
              ·
                refine ⟨8412738026495503763763649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11216984035327338351684865 8412738026495503763763649)
                ·
                  refine ⟨6309553519871627822822737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412738026495503763763649 6309553519871627822822737)
                  ·
                    refine ⟨4732165139903720867117053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6309553519871627822822737 4732165139903720867117053)
                    ·
                      refine ⟨1774561927463895325168895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4732165139903720867117053 1774561927463895325168895)
                      ·
                        rfl

theorem cell23_3455947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 3].length) (baseStart_3455947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3455947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3455947 prefixEnd_3455947 := by exact prefixLift 3455947
  have htrace : WordTrace (prefixWord ++ tailWord_3455947) baseStart_3455947 baseEnd_3455947 := by
    simpa [prefixWord, tailWord_3455947, baseEnd_3455947] using wordTrace_append hprefix tailTrace_3455947
  have hstable : (prefixWord ++ tailWord_3455947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455947).length < 2 ^ (prefixWord ++ tailWord_3455947).sum := by decide
  have hdescent : baseEnd_3455947 < baseStart_3455947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456011 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 1, 1, 3]
def baseStart_3456011 : Nat := 118140960795 + 3456011 * 2 ^ 59
def prefixEnd_3456011 : Nat := 4983230072969 + 3 ^ 40 * 3456011 * 2
def baseEnd_3456011 : Nat := 1774594790225783074768601

theorem tailTrace_3456011 : CollatzResearch.WordTrace tailWord_3456011 prefixEnd_3456011 1774594790225783074768601 := by
  unfold tailWord_3456011
  simp only [CollatzResearch.WordTrace]
  refine ⟨126051076682469861532527887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84034051121646574355018591 126051076682469861532527887)
  ·
    refine ⟨189076615023704792298791831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126051076682469861532527887 189076615023704792298791831)
    ·
      refine ⟨283614922535557188448187747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189076615023704792298791831 283614922535557188448187747)
      ·
        refine ⟨425422383803335782672281621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283614922535557188448187747 425422383803335782672281621)
        ·
          refine ⟨19941674240781364812763201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 425422383803335782672281621 19941674240781364812763201)
          ·
            refine ⟨14956255680586023609572401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19941674240781364812763201 14956255680586023609572401)
            ·
              refine ⟨11217191760439517707179301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14956255680586023609572401 11217191760439517707179301)
              ·
                refine ⟨2103223455082409570096119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11217191760439517707179301 2103223455082409570096119)
                ·
                  refine ⟨3154835182623614355144179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103223455082409570096119 3154835182623614355144179)
                  ·
                    refine ⟨4732252773935421532716269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3154835182623614355144179 4732252773935421532716269)
                    ·
                      refine ⟨1774594790225783074768601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4732252773935421532716269 1774594790225783074768601)
                      ·
                        rfl

theorem cell23_3456011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 1, 3].length) (baseStart_3456011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456011 prefixEnd_3456011 := by exact prefixLift 3456011
  have htrace : WordTrace (prefixWord ++ tailWord_3456011) baseStart_3456011 baseEnd_3456011 := by
    simpa [prefixWord, tailWord_3456011, baseEnd_3456011] using wordTrace_append hprefix tailTrace_3456011
  have hstable : (prefixWord ++ tailWord_3456011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456011).length < 2 ^ (prefixWord ++ tailWord_3456011).sum := by decide
  have hdescent : baseEnd_3456011 < baseStart_3456011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456034 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_3456034 : Nat := 118140960795 + 3456034 * 2 ^ 59
def prefixEnd_3456034 : Nat := 4983230072969 + 3 ^ 40 * 3456034 * 2
def baseEnd_3456034 : Nat := 1774606600280836484780995

theorem tailTrace_3456034 : CollatzResearch.WordTrace tailWord_3456034 prefixEnd_3456034 1774606600280836484780995 := by
  unfold tailWord_3456034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31512978890346634115153789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84034610374257690973743437 31512978890346634115153789)
  ·
    refine ⟨11817367083879987793182671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31512978890346634115153789 11817367083879987793182671)
    ·
      refine ⟨17726050625819981689774007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817367083879987793182671 17726050625819981689774007)
      ·
        refine ⟨26589075938729972534661011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17726050625819981689774007 26589075938729972534661011)
        ·
          refine ⟨39883613908094958801991517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26589075938729972534661011 39883613908094958801991517)
          ·
            refine ⟨14956355215535609550746819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39883613908094958801991517 14956355215535609550746819)
            ·
              refine ⟨22434532823303414326120229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14956355215535609550746819 22434532823303414326120229)
              ·
                refine ⟨4206474904369390186147543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22434532823303414326120229 4206474904369390186147543)
                ·
                  refine ⟨6309712356554085279221315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206474904369390186147543 6309712356554085279221315)
                  ·
                    refine ⟨9464568534831127918831973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6309712356554085279221315 9464568534831127918831973)
                    ·
                      refine ⟨1774606600280836484780995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9464568534831127918831973 1774606600280836484780995)
                      ·
                        rfl

theorem cell23_3456034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_3456034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456034 prefixEnd_3456034 := by exact prefixLift 3456034
  have htrace : WordTrace (prefixWord ++ tailWord_3456034) baseStart_3456034 baseEnd_3456034 := by
    simpa [prefixWord, tailWord_3456034, baseEnd_3456034] using wordTrace_append hprefix tailTrace_3456034
  have hstable : (prefixWord ++ tailWord_3456034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456034).length < 2 ^ (prefixWord ++ tailWord_3456034).sum := by decide
  have hdescent : baseEnd_3456034 < baseStart_3456034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456054 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3456054 : Nat := 118140960795 + 3456054 * 2 ^ 59
def prefixEnd_3456054 : Nat := 4983230072969 + 3 ^ 40 * 3456054 * 2
def baseEnd_3456054 : Nat := 1774616869893926406530903

theorem tailTrace_3456054 : CollatzResearch.WordTrace tailWord_3456054 prefixEnd_3456054 1774616869893926406530903 := by
  unfold tailWord_3456054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878290313832129992271451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84035096680876053250895477 7878290313832129992271451)
  ·
    refine ⟨11817435470748194988407177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7878290313832129992271451 11817435470748194988407177)
    ·
      refine ⟨8863076603061146241305383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11817435470748194988407177 8863076603061146241305383)
      ·
        refine ⟨13294614904591719361958075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863076603061146241305383 13294614904591719361958075)
        ·
          refine ⟨19941922356887579042937113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13294614904591719361958075 19941922356887579042937113)
          ·
            refine ⟨14956441767665684282202835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19941922356887579042937113 14956441767665684282202835)
            ·
              refine ⟨22434662651498526423304253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14956441767665684282202835 22434662651498526423304253)
              ·
                refine ⟨8412998494311947408739095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22434662651498526423304253 8412998494311947408739095)
                ·
                  refine ⟨12619497741467921113108643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412998494311947408739095 12619497741467921113108643)
                  ·
                    refine ⟨18929246612201881669662965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12619497741467921113108643 18929246612201881669662965)
                    ·
                      refine ⟨1774616869893926406530903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18929246612201881669662965 1774616869893926406530903)
                      ·
                        rfl

theorem cell23_3456054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3456054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456054 prefixEnd_3456054 := by exact prefixLift 3456054
  have htrace : WordTrace (prefixWord ++ tailWord_3456054) baseStart_3456054 baseEnd_3456054 := by
    simpa [prefixWord, tailWord_3456054, baseEnd_3456054] using wordTrace_append hprefix tailTrace_3456054
  have hstable : (prefixWord ++ tailWord_3456054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456054).length < 2 ^ (prefixWord ++ tailWord_3456054).sum := by decide
  have hdescent : baseEnd_3456054 < baseStart_3456054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456057 : List Nat := [1, 2, 1, 5, 2, 3, 9]
def baseStart_3456057 : Nat := 118140960795 + 3456057 * 2 ^ 59
def prefixEnd_3456057 : Nat := 4983230072969 + 3 ^ 40 * 3456057 * 2
def baseEnd_3456057 : Nat := 21908869263406048083869

theorem tailTrace_3456057 : CollatzResearch.WordTrace tailWord_3456057 prefixEnd_3456057 21908869263406048083869 := by
  unfold tailWord_3456057
  simp only [CollatzResearch.WordTrace]
  refine ⟨126052754440303211388702425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84035169626868807592468283 126052754440303211388702425)
  ·
    refine ⟨94539565830227408541526819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126052754440303211388702425 94539565830227408541526819)
    ·
      refine ⟨141809348745341112812290229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94539565830227408541526819 141809348745341112812290229)
      ·
        refine ⟨13294626444875729326152209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141809348745341112812290229 13294626444875729326152209)
        ·
          refine ⟨9970969833656796994614157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13294626444875729326152209 9970969833656796994614157)
          ·
            refine ⟨3739113687621298872980309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9970969833656796994614157 3739113687621298872980309)
            ·
              refine ⟨21908869263406048083869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3739113687621298872980309 21908869263406048083869)
              ·
                rfl

theorem cell23_3456057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 9].length) (baseStart_3456057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456057 prefixEnd_3456057 := by exact prefixLift 3456057
  have htrace : WordTrace (prefixWord ++ tailWord_3456057) baseStart_3456057 baseEnd_3456057 := by
    simpa [prefixWord, tailWord_3456057, baseEnd_3456057] using wordTrace_append hprefix tailTrace_3456057
  have hstable : (prefixWord ++ tailWord_3456057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456057).length < 2 ^ (prefixWord ++ tailWord_3456057).sum := by decide
  have hdescent : baseEnd_3456057 < baseStart_3456057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456118 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3456118 : Nat := 118140960795 + 3456118 * 2 ^ 59
def prefixEnd_3456118 : Nat := 4983230072969 + 3 ^ 40 * 3456118 * 2
def baseEnd_3456118 : Nat := 1774649732655814156130609

theorem tailTrace_3456118 : CollatzResearch.WordTrace tailWord_3456118 prefixEnd_3456118 1774649732655814156130609 := by
  unfold tailWord_3456118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878436205817638675417063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84036652862054812537782005 7878436205817638675417063)
  ·
    refine ⟨11817654308726458013125595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7878436205817638675417063 11817654308726458013125595)
    ·
      refine ⟨17726481463089687019688393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817654308726458013125595 17726481463089687019688393)
      ·
        refine ⟨13294861097317265264766295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17726481463089687019688393 13294861097317265264766295)
        ·
          refine ⟨19942291645975897897149443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13294861097317265264766295 19942291645975897897149443)
          ·
            refine ⟨29913437468963846845724165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19942291645975897897149443 29913437468963846845724165)
            ·
              refine ⟨5608769525430721283573281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29913437468963846845724165 5608769525430721283573281)
              ·
                refine ⟨4206577144073040962679961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608769525430721283573281 4206577144073040962679961)
                ·
                  refine ⟨3154932858054780722009971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4206577144073040962679961 3154932858054780722009971)
                  ·
                    refine ⟨4732399287082171083014957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3154932858054780722009971 4732399287082171083014957)
                    ·
                      refine ⟨1774649732655814156130609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4732399287082171083014957 1774649732655814156130609)
                      ·
                        rfl

theorem cell23_3456118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3456118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456118 prefixEnd_3456118 := by exact prefixLift 3456118
  have htrace : WordTrace (prefixWord ++ tailWord_3456118) baseStart_3456118 baseEnd_3456118 := by
    simpa [prefixWord, tailWord_3456118, baseEnd_3456118] using wordTrace_append hprefix tailTrace_3456118
  have hstable : (prefixWord ++ tailWord_3456118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456118).length < 2 ^ (prefixWord ++ tailWord_3456118).sum := by decide
  have hdescent : baseEnd_3456118 < baseStart_3456118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456124 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_3456124 : Nat := 118140960795 + 3456124 * 2 ^ 59
def prefixEnd_3456124 : Nat := 4983230072969 + 3 ^ 40 * 3456124 * 2
def baseEnd_3456124 : Nat := 1774652813539741132655581

theorem tailTrace_3456124 : CollatzResearch.WordTrace tailWord_3456124 prefixEnd_3456124 1774652813539741132655581 := by
  unfold tailWord_3456124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63027599065530240915695713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84036798754040321220927617 63027599065530240915695713)
  ·
    refine ⟨47270699299147680686771785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63027599065530240915695713 47270699299147680686771785)
    ·
      refine ⟨35453024474360760515078839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47270699299147680686771785 35453024474360760515078839)
      ·
        refine ⟨53179536711541140772618259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35453024474360760515078839 53179536711541140772618259)
        ·
          refine ⟨79769305067311711158927389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53179536711541140772618259 79769305067311711158927389)
          ·
            refine ⟨29913489400241891684597771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79769305067311711158927389 29913489400241891684597771)
            ·
              refine ⟨44870234100362837526896657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29913489400241891684597771 44870234100362837526896657)
              ·
                refine ⟨33652675575272128145172493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44870234100362837526896657 33652675575272128145172493)
                ·
                  refine ⟨12619753340727048054439685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33652675575272128145172493 12619753340727048054439685)
                  ·
                    refine ⟨2366203751386321510207441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12619753340727048054439685 2366203751386321510207441)
                    ·
                      refine ⟨1774652813539741132655581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366203751386321510207441 1774652813539741132655581)
                      ·
                        rfl

theorem cell23_3456124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_3456124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456124 prefixEnd_3456124 := by exact prefixLift 3456124
  have htrace : WordTrace (prefixWord ++ tailWord_3456124) baseStart_3456124 baseEnd_3456124 := by
    simpa [prefixWord, tailWord_3456124, baseEnd_3456124] using wordTrace_append hprefix tailTrace_3456124
  have hstable : (prefixWord ++ tailWord_3456124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456124).length < 2 ^ (prefixWord ++ tailWord_3456124).sum := by decide
  have hdescent : baseEnd_3456124 < baseStart_3456124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456137 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_3456137 : Nat := 118140960795 + 3456137 * 2 ^ 59
def prefixEnd_3456137 : Nat := 4983230072969 + 3 ^ 40 * 3456137 * 2
def baseEnd_3456137 : Nat := 1774659488788249581793021

theorem tailTrace_3456137 : CollatzResearch.WordTrace tailWord_3456137 prefixEnd_3456137 1774659488788249581793021 := by
  unfold tailWord_3456137
  simp only [CollatzResearch.WordTrace]
  refine ⟨126055672280013385051614665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84037114853342256701076443 126055672280013385051614665)
  ·
    refine ⟨94541754210010038788710999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126055672280013385051614665 94541754210010038788710999)
    ·
      refine ⟨141812631315015058183066499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94541754210010038788710999 141812631315015058183066499)
      ·
        refine ⟨212718946972522587274599749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141812631315015058183066499 212718946972522587274599749)
        ·
          refine ⟨39884802557347985113987453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212718946972522587274599749 39884802557347985113987453)
          ·
            refine ⟨14956800959005494417745295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39884802557347985113987453 14956800959005494417745295)
            ·
              refine ⟨22435201438508241626617943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14956800959005494417745295 22435201438508241626617943)
              ·
                refine ⟨33652802157762362439926915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22435201438508241626617943 33652802157762362439926915)
                ·
                  refine ⟨50479203236643543659890373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33652802157762362439926915 50479203236643543659890373)
                  ·
                    refine ⟨9464850606870664436229445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50479203236643543659890373 9464850606870664436229445)
                    ·
                      refine ⟨1774659488788249581793021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9464850606870664436229445 1774659488788249581793021)
                      ·
                        rfl

theorem cell23_3456137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_3456137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456137 prefixEnd_3456137 := by exact prefixLift 3456137
  have htrace : WordTrace (prefixWord ++ tailWord_3456137) baseStart_3456137 baseEnd_3456137 := by
    simpa [prefixWord, tailWord_3456137, baseEnd_3456137] using wordTrace_append hprefix tailTrace_3456137
  have hstable : (prefixWord ++ tailWord_3456137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456137).length < 2 ^ (prefixWord ++ tailWord_3456137).sum := by decide
  have hdescent : baseEnd_3456137 < baseStart_3456137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456158 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_3456158 : Nat := 118140960795 + 3456158 * 2 ^ 59
def prefixEnd_3456158 : Nat := 4983230072969 + 3 ^ 40 * 3456158 * 2
def baseEnd_3456158 : Nat := 1774670271881993999630425

theorem tailTrace_3456158 : CollatzResearch.WordTrace tailWord_3456158 prefixEnd_3456158 1774670271881993999630425 := by
  unfold tailWord_3456158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757054776617163204766141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84037625475291537092086085 15757054776617163204766141)
  ·
    refine ⟨5908895541231436201787303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15757054776617163204766141 5908895541231436201787303)
    ·
      refine ⟨8863343311847154302680955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908895541231436201787303 8863343311847154302680955)
      ·
        refine ⟨13295014967770731454021433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863343311847154302680955 13295014967770731454021433)
        ·
          refine ⟨9971261225828048590516075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13295014967770731454021433 9971261225828048590516075)
          ·
            refine ⟨14956891838742072885774113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9971261225828048590516075 14956891838742072885774113)
            ·
              refine ⟨11217668879056554664330585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14956891838742072885774113 11217668879056554664330585)
              ·
                refine ⟨8413251659292415998247939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11217668879056554664330585 8413251659292415998247939)
                ·
                  refine ⟨12619877488938623997371909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8413251659292415998247939 12619877488938623997371909)
                  ·
                    refine ⟨2366227029175991999507233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12619877488938623997371909 2366227029175991999507233)
                    ·
                      refine ⟨1774670271881993999630425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366227029175991999507233 1774670271881993999630425)
                      ·
                        rfl

theorem cell23_3456158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_3456158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456158 prefixEnd_3456158 := by exact prefixLift 3456158
  have htrace : WordTrace (prefixWord ++ tailWord_3456158) baseStart_3456158 baseEnd_3456158 := by
    simpa [prefixWord, tailWord_3456158, baseEnd_3456158] using wordTrace_append hprefix tailTrace_3456158
  have hstable : (prefixWord ++ tailWord_3456158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456158).length < 2 ^ (prefixWord ++ tailWord_3456158).sum := by decide
  have hdescent : baseEnd_3456158 < baseStart_3456158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456162 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_3456162 : Nat := 118140960795 + 3456162 * 2 ^ 59
def prefixEnd_3456162 : Nat := 4983230072969 + 3 ^ 40 * 3456162 * 2
def baseEnd_3456162 : Nat := 1774672325804611983980407

theorem tailTrace_3456162 : CollatzResearch.WordTrace tailWord_3456162 prefixEnd_3456162 1774672325804611983980407 := by
  unfold tailWord_3456162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31514146026230703580318685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84037722736615209547516493 31514146026230703580318685)
  ·
    refine ⟨11817804759836513842619507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31514146026230703580318685 11817804759836513842619507)
    ·
      refine ⟨17726707139754770763929261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817804759836513842619507 17726707139754770763929261)
      ·
        refine ⟨6647515177408039036473473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17726707139754770763929261 6647515177408039036473473)
        ·
          refine ⟨4985636383056029277355105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6647515177408039036473473 4985636383056029277355105)
          ·
            refine ⟨3739227287292021958016329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4985636383056029277355105 3739227287292021958016329)
            ·
              refine ⟨2804420465469016468512247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739227287292021958016329 2804420465469016468512247)
              ·
                refine ⟨4206630698203524702768371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804420465469016468512247 4206630698203524702768371)
                ·
                  refine ⟨6309946047305287054152557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206630698203524702768371 6309946047305287054152557)
                  ·
                    refine ⟨2366229767739482645307209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6309946047305287054152557 2366229767739482645307209)
                    ·
                      refine ⟨1774672325804611983980407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366229767739482645307209 1774672325804611983980407)
                      ·
                        rfl

theorem cell23_3456162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_3456162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456162 prefixEnd_3456162 := by exact prefixLift 3456162
  have htrace : WordTrace (prefixWord ++ tailWord_3456162) baseStart_3456162 baseEnd_3456162 := by
    simpa [prefixWord, tailWord_3456162, baseEnd_3456162] using wordTrace_append hprefix tailTrace_3456162
  have hstable : (prefixWord ++ tailWord_3456162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456162).length < 2 ^ (prefixWord ++ tailWord_3456162).sum := by decide
  have hdescent : baseEnd_3456162 < baseStart_3456162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456184 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 2, 5, 2]
def baseStart_3456184 : Nat := 118140960795 + 3456184 * 2 ^ 59
def prefixEnd_3456184 : Nat := 4983230072969 + 3 ^ 40 * 3456184 * 2
def baseEnd_3456184 : Nat := 1774683622379010897905305

theorem tailTrace_3456184 : CollatzResearch.WordTrace tailWord_3456184 prefixEnd_3456184 1774683622379010897905305 := by
  unfold tailWord_3456184
  simp only [CollatzResearch.WordTrace]
  refine ⟨63028693255421556039287803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84038257673895408052383737 63028693255421556039287803)
  ·
    refine ⟨94543039883132334058931705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63028693255421556039287803 94543039883132334058931705)
    ·
      refine ⟨70907279912349250544198779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94543039883132334058931705 70907279912349250544198779)
      ·
        refine ⟨106360919868523875816298169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70907279912349250544198779 106360919868523875816298169)
        ·
          refine ⟨79770689901392906862223627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106360919868523875816298169 79770689901392906862223627)
          ·
            refine ⟨119656034852089360293335441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79770689901392906862223627 119656034852089360293335441)
            ·
              refine ⟨89742026139067020220001581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119656034852089360293335441 89742026139067020220001581)
              ·
                refine ⟨33653259802150132582500593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89742026139067020220001581 33653259802150132582500593)
                ·
                  refine ⟨25239944851612599436875445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33653259802150132582500593 25239944851612599436875445)
                  ·
                    refine ⟨2366244829838681197207073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25239944851612599436875445 2366244829838681197207073)
                    ·
                      refine ⟨1774683622379010897905305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366244829838681197207073 1774683622379010897905305)
                      ·
                        rfl

theorem cell23_3456184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_3456184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456184 prefixEnd_3456184 := by exact prefixLift 3456184
  have htrace : WordTrace (prefixWord ++ tailWord_3456184) baseStart_3456184 baseEnd_3456184 := by
    simpa [prefixWord, tailWord_3456184, baseEnd_3456184] using wordTrace_append hprefix tailTrace_3456184
  have hstable : (prefixWord ++ tailWord_3456184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456184).length < 2 ^ (prefixWord ++ tailWord_3456184).sum := by decide
  have hdescent : baseEnd_3456184 < baseStart_3456184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456217 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3456217 : Nat := 118140960795 + 3456217 * 2 ^ 59
def prefixEnd_3456217 : Nat := 4983230072969 + 3 ^ 40 * 3456217 * 2
def baseEnd_3456217 : Nat := 1774700567240609268792653

theorem tailTrace_3456217 : CollatzResearch.WordTrace tailWord_3456217 prefixEnd_3456217 1774700567240609268792653 := by
  unfold tailWord_3456217
  simp only [CollatzResearch.WordTrace]
  refine ⟨126058590119723558714526905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84039060079815705809684603 126058590119723558714526905)
  ·
    refine ⟨94543942589792669035895179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126058590119723558714526905 94543942589792669035895179)
    ·
      refine ⟨141815913884689003553842769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94543942589792669035895179 141815913884689003553842769)
      ·
        refine ⟨106361935413516752665382077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141815913884689003553842769 106361935413516752665382077)
        ·
          refine ⟨39885725780068782249518279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106361935413516752665382077 39885725780068782249518279)
          ·
            refine ⟨59828588670103173374277419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39885725780068782249518279 59828588670103173374277419)
            ·
              refine ⟨89742883005154760061416129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59828588670103173374277419 89742883005154760061416129)
              ·
                refine ⟨67307162253866070046062097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89742883005154760061416129 67307162253866070046062097)
                ·
                  refine ⟨50480371690399552534546573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67307162253866070046062097 50480371690399552534546573)
                  ·
                    refine ⟨18930139383899832200454965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50480371690399552534546573 18930139383899832200454965)
                    ·
                      refine ⟨1774700567240609268792653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18930139383899832200454965 1774700567240609268792653)
                      ·
                        rfl

theorem cell23_3456217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3456217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456217 prefixEnd_3456217 := by exact prefixLift 3456217
  have htrace : WordTrace (prefixWord ++ tailWord_3456217) baseStart_3456217 baseEnd_3456217 := by
    simpa [prefixWord, tailWord_3456217, baseEnd_3456217] using wordTrace_append hprefix tailTrace_3456217
  have hstable : (prefixWord ++ tailWord_3456217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456217).length < 2 ^ (prefixWord ++ tailWord_3456217).sum := by decide
  have hdescent : baseEnd_3456217 < baseStart_3456217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456304 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_3456304 : Nat := 118140960795 + 3456304 * 2 ^ 59
def prefixEnd_3456304 : Nat := 4983230072969 + 3 ^ 40 * 3456304 * 2
def baseEnd_3456304 : Nat := 1774745240057550428404753

theorem tailTrace_3456304 : CollatzResearch.WordTrace tailWord_3456304 prefixEnd_3456304 1774745240057550428404753 := by
  unfold tailWord_3456304
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030881635204186286471983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84041175513605581715295977 63030881635204186286471983)
  ·
    refine ⟨94546322452806279429707975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63030881635204186286471983 94546322452806279429707975)
    ·
      refine ⟨141819483679209419144561963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94546322452806279429707975 141819483679209419144561963)
      ·
        refine ⟨212729225518814128716842945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141819483679209419144561963 212729225518814128716842945)
        ·
          refine ⟨159546919139110596537632209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212729225518814128716842945 159546919139110596537632209)
          ·
            refine ⟨119660189354332947403224157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159546919139110596537632209 119660189354332947403224157)
            ·
              refine ⟨44872571007874855276209059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119660189354332947403224157 44872571007874855276209059)
              ·
                refine ⟨67308856511812282914313589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44872571007874855276209059 67308856511812282914313589)
                ·
                  refine ⟨6310205297982401523216899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67308856511812282914313589 6310205297982401523216899)
                  ·
                    refine ⟨9465307946973602284825349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6310205297982401523216899 9465307946973602284825349)
                    ·
                      refine ⟨1774745240057550428404753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9465307946973602284825349 1774745240057550428404753)
                      ·
                        rfl

theorem cell23_3456304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_3456304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456304 prefixEnd_3456304 := by exact prefixLift 3456304
  have htrace : WordTrace (prefixWord ++ tailWord_3456304) baseStart_3456304 baseEnd_3456304 := by
    simpa [prefixWord, tailWord_3456304, baseEnd_3456304] using wordTrace_append hprefix tailTrace_3456304
  have hstable : (prefixWord ++ tailWord_3456304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456304).length < 2 ^ (prefixWord ++ tailWord_3456304).sum := by decide
  have hdescent : baseEnd_3456304 < baseStart_3456304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456308 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_3456308 : Nat := 118140960795 + 3456308 * 2 ^ 59
def prefixEnd_3456308 : Nat := 4983230072969 + 3 ^ 40 * 3456308 * 2
def baseEnd_3456308 : Nat := 1774747293980168412754735

theorem tailTrace_3456308 : CollatzResearch.WordTrace tailWord_3456308 prefixEnd_3456308 1774747293980168412754735 := by
  unfold tailWord_3456308
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030954581196940628044789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84041272774929254170726385 63030954581196940628044789)
  ·
    refine ⟨5909151991987213183879199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63030954581196940628044789 5909151991987213183879199)
    ·
      refine ⟨8863727987980819775818799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5909151991987213183879199 8863727987980819775818799)
      ·
        refine ⟨13295591981971229663728199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863727987980819775818799 13295591981971229663728199)
        ·
          refine ⟨19943387972956844495592299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295591981971229663728199 19943387972956844495592299)
          ·
            refine ⟨29915081959435266743388449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19943387972956844495592299 29915081959435266743388449)
            ·
              refine ⟨22436311469576450057541337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29915081959435266743388449 22436311469576450057541337)
              ·
                refine ⟨16827233602182337543156003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22436311469576450057541337 16827233602182337543156003)
                ·
                  refine ⟨25240850403273506314734005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16827233602182337543156003 25240850403273506314734005)
                  ·
                    refine ⟨2366329725306891217006313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25240850403273506314734005 2366329725306891217006313)
                    ·
                      refine ⟨1774747293980168412754735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366329725306891217006313 1774747293980168412754735)
                      ·
                        rfl

theorem cell23_3456308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_3456308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456308 prefixEnd_3456308 := by exact prefixLift 3456308
  have htrace : WordTrace (prefixWord ++ tailWord_3456308) baseStart_3456308 baseEnd_3456308 := by
    simpa [prefixWord, tailWord_3456308, baseEnd_3456308] using wordTrace_append hprefix tailTrace_3456308
  have hstable : (prefixWord ++ tailWord_3456308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456308).length < 2 ^ (prefixWord ++ tailWord_3456308).sum := by decide
  have hdescent : baseEnd_3456308 < baseStart_3456308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456338 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_3456338 : Nat := 118140960795 + 3456338 * 2 ^ 59
def prefixEnd_3456338 : Nat := 4983230072969 + 3 ^ 40 * 3456338 * 2
def baseEnd_3456338 : Nat := 1774762698399803295379597

theorem tailTrace_3456338 : CollatzResearch.WordTrace tailWord_3456338 prefixEnd_3456338 1774762698399803295379597 := by
  unfold tailWord_3456338
  simp only [CollatzResearch.WordTrace]
  refine ⟨31515750838071299094920417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84042002234856797586454445 31515750838071299094920417)
  ·
    refine ⟨23636813128553474321190313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31515750838071299094920417 23636813128553474321190313)
    ·
      refine ⟨17727609846415105740892735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23636813128553474321190313 17727609846415105740892735)
      ·
        refine ⟨26591414769622658611339103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17727609846415105740892735 26591414769622658611339103)
        ·
          refine ⟨39887122154433987917008655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26591414769622658611339103 39887122154433987917008655)
          ·
            refine ⟨59830683231650981875512983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39887122154433987917008655 59830683231650981875512983)
            ·
              refine ⟨89746024847476472813269475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59830683231650981875512983 89746024847476472813269475)
              ·
                refine ⟨134619037271214709219904213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89746024847476472813269475 134619037271214709219904213)
                ·
                  refine ⟨3155133686044094747341505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134619037271214709219904213 3155133686044094747341505)
                  ·
                    refine ⟨2366350264533071060506129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3155133686044094747341505 2366350264533071060506129)
                    ·
                      refine ⟨1774762698399803295379597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366350264533071060506129 1774762698399803295379597)
                      ·
                        rfl

theorem cell23_3456338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_3456338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456338 prefixEnd_3456338 := by exact prefixLift 3456338
  have htrace : WordTrace (prefixWord ++ tailWord_3456338) baseStart_3456338 baseEnd_3456338 := by
    simpa [prefixWord, tailWord_3456338, baseEnd_3456338] using wordTrace_append hprefix tailTrace_3456338
  have hstable : (prefixWord ++ tailWord_3456338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456338).length < 2 ^ (prefixWord ++ tailWord_3456338).sum := by decide
  have hdescent : baseEnd_3456338 < baseStart_3456338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456349 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3456349 : Nat := 118140960795 + 3456349 * 2 ^ 59
def prefixEnd_3456349 : Nat := 4983230072969 + 3 ^ 40 * 3456349 * 2
def baseEnd_3456349 : Nat := 1774768346687002752342047

theorem tailTrace_3456349 : CollatzResearch.WordTrace tailWord_3456349 prefixEnd_3456349 1774768346687002752342047 := by
  unfold tailWord_3456349
  simp only [CollatzResearch.WordTrace]
  refine ⟨126063404555245345258332101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84042269703496896838888067 126063404555245345258332101)
  ·
    refine ⟨23636888354108502235937269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126063404555245345258332101 23636888354108502235937269)
    ·
      refine ⟨2215958283197672084619119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23636888354108502235937269 2215958283197672084619119)
      ·
        refine ⟨3323937424796508126928679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215958283197672084619119 3323937424796508126928679)
        ·
          refine ⟨4985906137194762190393019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323937424796508126928679 4985906137194762190393019)
          ·
            refine ⟨7478859205792143285589529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985906137194762190393019 7478859205792143285589529)
            ·
              refine ⟨5609144404344107464192147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7478859205792143285589529 5609144404344107464192147)
              ·
                refine ⟨8413716606516161196288221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609144404344107464192147 8413716606516161196288221)
                ·
                  refine ⟨3155143727443560448608083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8413716606516161196288221 3155143727443560448608083)
                  ·
                    refine ⟨4732715591165340672912125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155143727443560448608083 4732715591165340672912125)
                    ·
                      refine ⟨1774768346687002752342047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4732715591165340672912125 1774768346687002752342047)
                      ·
                        rfl

theorem cell23_3456349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3456349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456349 prefixEnd_3456349 := by exact prefixLift 3456349
  have htrace : WordTrace (prefixWord ++ tailWord_3456349) baseStart_3456349 baseEnd_3456349 := by
    simpa [prefixWord, tailWord_3456349, baseEnd_3456349] using wordTrace_append hprefix tailTrace_3456349
  have hstable : (prefixWord ++ tailWord_3456349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456349).length < 2 ^ (prefixWord ++ tailWord_3456349).sum := by decide
  have hdescent : baseEnd_3456349 < baseStart_3456349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456355 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 3, 2, 2]
def baseStart_3456355 : Nat := 118140960795 + 3456355 * 2 ^ 59
def prefixEnd_3456355 : Nat := 4983230072969 + 3 ^ 40 * 3456355 * 2
def baseEnd_3456355 : Nat := 1774771427570929728867019

theorem tailTrace_3456355 : CollatzResearch.WordTrace tailWord_3456355 prefixEnd_3456355 1774771427570929728867019 := by
  unfold tailWord_3456355
  simp only [CollatzResearch.WordTrace]
  refine ⟨126063623393223608283050519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84042415595482405522033679 126063623393223608283050519)
  ·
    refine ⟨189095435089835412424575779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126063623393223608283050519 189095435089835412424575779)
    ·
      refine ⟨283643152634753118636863669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189095435089835412424575779 283643152634753118636863669)
      ·
        refine ⟨26591545559508104872205969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283643152634753118636863669 26591545559508104872205969)
        ·
          refine ⟨19943659169631078654154477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26591545559508104872205969 19943659169631078654154477)
          ·
            refine ⟨7478872188611654495307929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19943659169631078654154477 7478872188611654495307929)
            ·
              refine ⟨5609154141458740871480947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7478872188611654495307929 5609154141458740871480947)
              ·
                refine ⟨8413731212188111307221421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609154141458740871480947 8413731212188111307221421)
                ·
                  refine ⟨3155149204570541740208033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8413731212188111307221421 3155149204570541740208033)
                  ·
                    refine ⟨2366361903427906305156025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3155149204570541740208033 2366361903427906305156025)
                    ·
                      refine ⟨1774771427570929728867019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366361903427906305156025 1774771427570929728867019)
                      ·
                        rfl

theorem cell23_3456355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_3456355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456355 prefixEnd_3456355 := by exact prefixLift 3456355
  have htrace : WordTrace (prefixWord ++ tailWord_3456355) baseStart_3456355 baseEnd_3456355 := by
    simpa [prefixWord, tailWord_3456355, baseEnd_3456355] using wordTrace_append hprefix tailTrace_3456355
  have hstable : (prefixWord ++ tailWord_3456355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456355).length < 2 ^ (prefixWord ++ tailWord_3456355).sum := by decide
  have hdescent : baseEnd_3456355 < baseStart_3456355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456365 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_3456365 : Nat := 118140960795 + 3456365 * 2 ^ 59
def prefixEnd_3456365 : Nat := 4983230072969 + 3 ^ 40 * 3456365 * 2
def baseEnd_3456365 : Nat := 591592187459158229913991

theorem tailTrace_3456365 : CollatzResearch.WordTrace tailWord_3456365 prefixEnd_3456365 591592187459158229913991 := by
  unfold tailWord_3456365
  simp only [CollatzResearch.WordTrace]
  refine ⟨126063988123187379990914549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84042658748791586660609699 126063988123187379990914549)
  ·
    refine ⟨11818498886548816874148239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126063988123187379990914549 11818498886548816874148239)
    ·
      refine ⟨17727748329823225311222359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11818498886548816874148239 17727748329823225311222359)
      ·
        refine ⟨26591622494734837966833539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17727748329823225311222359 26591622494734837966833539)
        ·
          refine ⟨39887433742102256950250309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26591622494734837966833539 39887433742102256950250309)
          ·
            refine ⟨7478893826644173178171933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39887433742102256950250309 7478893826644173178171933)
            ·
              refine ⟨2804585184991564941814475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7478893826644173178171933 2804585184991564941814475)
              ·
                refine ⟨4206877777487347412721713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804585184991564941814475 4206877777487347412721713)
                ·
                  refine ⟨3155158333115510559541285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4206877777487347412721713 3155158333115510559541285)
                  ·
                    refine ⟨591592187459158229913991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155158333115510559541285 591592187459158229913991)
                    ·
                      rfl

theorem cell23_3456365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_3456365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456365 prefixEnd_3456365 := by exact prefixLift 3456365
  have htrace : WordTrace (prefixWord ++ tailWord_3456365) baseStart_3456365 baseEnd_3456365 := by
    simpa [prefixWord, tailWord_3456365, baseEnd_3456365] using wordTrace_append hprefix tailTrace_3456365
  have hstable : (prefixWord ++ tailWord_3456365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456365).length < 2 ^ (prefixWord ++ tailWord_3456365).sum := by decide
  have hdescent : baseEnd_3456365 < baseStart_3456365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456371 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 3]
def baseStart_3456371 : Nat := 118140960795 + 3456371 * 2 ^ 59
def prefixEnd_3456371 : Nat := 4983230072969 + 3 ^ 40 * 3456371 * 2
def baseEnd_3456371 : Nat := 1774779643261401666266945

theorem tailTrace_3456371 : CollatzResearch.WordTrace tailWord_3456371 prefixEnd_3456371 1774779643261401666266945 := by
  unfold tailWord_3456371
  simp only [CollatzResearch.WordTrace]
  refine ⟨126064206961165643015632967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84042804640777095343755311 126064206961165643015632967)
  ·
    refine ⟨189096310441748464523449451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126064206961165643015632967 189096310441748464523449451)
    ·
      refine ⟨283644465662622696785174177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189096310441748464523449451 283644465662622696785174177)
      ·
        refine ⟨212733349246967022588880633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283644465662622696785174177 212733349246967022588880633)
        ·
          refine ⟨159550011935225266941660475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212733349246967022588880633 159550011935225266941660475)
          ·
            refine ⟨239325017902837900412490713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159550011935225266941660475 239325017902837900412490713)
            ·
              refine ⟨179493763427128425309368035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239325017902837900412490713 179493763427128425309368035)
              ·
                refine ⟨269240645140692637964052053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179493763427128425309368035 269240645140692637964052053)
                ·
                  refine ⟨3155163810242491851141235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 269240645140692637964052053 3155163810242491851141235)
                  ·
                    refine ⟨4732745715363737776711853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155163810242491851141235 4732745715363737776711853)
                    ·
                      refine ⟨1774779643261401666266945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4732745715363737776711853 1774779643261401666266945)
                      ·
                        rfl

theorem cell23_3456371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_3456371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456371 prefixEnd_3456371 := by exact prefixLift 3456371
  have htrace : WordTrace (prefixWord ++ tailWord_3456371) baseStart_3456371 baseEnd_3456371 := by
    simpa [prefixWord, tailWord_3456371, baseEnd_3456371] using wordTrace_append hprefix tailTrace_3456371
  have hstable : (prefixWord ++ tailWord_3456371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456371).length < 2 ^ (prefixWord ++ tailWord_3456371).sum := by decide
  have hdescent : baseEnd_3456371 < baseStart_3456371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456388 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_3456388 : Nat := 118140960795 + 3456388 * 2 ^ 59
def prefixEnd_3456388 : Nat := 4983230072969 + 3 ^ 40 * 3456388 * 2
def baseEnd_3456388 : Nat := 1774788372432528099754367

theorem tailTrace_3456388 : CollatzResearch.WordTrace tailWord_3456388 prefixEnd_3456388 1774788372432528099754367 := by
  unfold tailWord_3456388
  simp only [CollatzResearch.WordTrace]
  refine ⟨63032413501052027459500909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84043218001402703279334545 63032413501052027459500909)
  ·
    refine ⟨23637155062894510297312841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63032413501052027459500909 23637155062894510297312841)
    ·
      refine ⟨17727866297170882722984631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23637155062894510297312841 17727866297170882722984631)
      ·
        refine ⟨26591799445756324084476947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17727866297170882722984631 26591799445756324084476947)
        ·
          refine ⟨39887699168634486126715421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26591799445756324084476947 39887699168634486126715421)
          ·
            refine ⟨14957887188237932297518283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39887699168634486126715421 14957887188237932297518283)
            ·
              refine ⟨22436830782356898446277425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14957887188237932297518283 22436830782356898446277425)
              ·
                refine ⟨16827623086767673834708069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22436830782356898446277425 16827623086767673834708069)
                ·
                  refine ⟨3155179328768938844007763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16827623086767673834708069 3155179328768938844007763)
                  ·
                    refine ⟨4732768993153408266011645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155179328768938844007763 4732768993153408266011645)
                    ·
                      refine ⟨1774788372432528099754367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4732768993153408266011645 1774788372432528099754367)
                      ·
                        rfl

theorem cell23_3456388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_3456388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456388 prefixEnd_3456388 := by exact prefixLift 3456388
  have htrace : WordTrace (prefixWord ++ tailWord_3456388) baseStart_3456388 baseEnd_3456388 := by
    simpa [prefixWord, tailWord_3456388, baseEnd_3456388] using wordTrace_append hprefix tailTrace_3456388
  have hstable : (prefixWord ++ tailWord_3456388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456388).length < 2 ^ (prefixWord ++ tailWord_3456388).sum := by decide
  have hdescent : baseEnd_3456388 < baseStart_3456388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456488 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_3456488 : Nat := 118140960795 + 3456488 * 2 ^ 59
def prefixEnd_3456488 : Nat := 4983230072969 + 3 ^ 40 * 3456488 * 2
def baseEnd_3456488 : Nat := 1774839720497977708503907

theorem tailTrace_3456488 : CollatzResearch.WordTrace tailWord_3456488 prefixEnd_3456488 1774839720497977708503907 := by
  unfold tailWord_3456488
  simp only [CollatzResearch.WordTrace]
  refine ⟨63034237150870885998821059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84045649534494514665094745 63034237150870885998821059)
  ·
    refine ⟨94551355726306328998231589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63034237150870885998821059 94551355726306328998231589)
    ·
      refine ⟨17728379198682436687168423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94551355726306328998231589 17728379198682436687168423)
      ·
        refine ⟨26592568798023655030752635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17728379198682436687168423 26592568798023655030752635)
        ·
          refine ⟨39888853197035482546128953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26592568798023655030752635 39888853197035482546128953)
          ·
            refine ⟨29916639897776611909596715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39888853197035482546128953 29916639897776611909596715)
            ·
              refine ⟨44874959846664917864395073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29916639897776611909596715 44874959846664917864395073)
              ·
                refine ⟨33656219884998688398296305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44874959846664917864395073 33656219884998688398296305)
                ·
                  refine ⟨25242164913749016298722229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33656219884998688398296305 25242164913749016298722229)
                  ·
                    refine ⟨2366452960663970278005209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25242164913749016298722229 2366452960663970278005209)
                    ·
                      refine ⟨1774839720497977708503907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366452960663970278005209 1774839720497977708503907)
                      ·
                        rfl

theorem cell23_3456488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_3456488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456488 prefixEnd_3456488 := by exact prefixLift 3456488
  have htrace : WordTrace (prefixWord ++ tailWord_3456488) baseStart_3456488 baseEnd_3456488 := by
    simpa [prefixWord, tailWord_3456488, baseEnd_3456488] using wordTrace_append hprefix tailTrace_3456488
  have hstable : (prefixWord ++ tailWord_3456488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456488).length < 2 ^ (prefixWord ++ tailWord_3456488).sum := by decide
  have hdescent : baseEnd_3456488 < baseStart_3456488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456498 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3456498 : Nat := 118140960795 + 3456498 * 2 ^ 59
def prefixEnd_3456498 : Nat := 4983230072969 + 3 ^ 40 * 3456498 * 2
def baseEnd_3456498 : Nat := 591614951768174223126287

theorem tailTrace_3456498 : CollatzResearch.WordTrace tailWord_3456498 prefixEnd_3456498 591614951768174223126287 := by
  unfold tailWord_3456498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31517209757926385926376537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84045892687803695803670765 31517209757926385926376537)
  ·
    refine ⟨23637907318444789444782403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31517209757926385926376537 23637907318444789444782403)
    ·
      refine ⟨35456860977667184167173605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23637907318444789444782403 35456860977667184167173605)
      ·
        refine ⟨6648161433312597031345051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35456860977667184167173605 6648161433312597031345051)
        ·
          refine ⟨9972242149968895547017577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6648161433312597031345051 9972242149968895547017577)
          ·
            refine ⟨7479181612476671660263183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9972242149968895547017577 7479181612476671660263183)
            ·
              refine ⟨11218772418715007490394775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479181612476671660263183 11218772418715007490394775)
              ·
                refine ⟨16828158628072511235592163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11218772418715007490394775 16828158628072511235592163)
                ·
                  refine ⟨25242237942108766853388245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16828158628072511235592163 25242237942108766853388245)
                  ·
                    refine ⟨591614951768174223126287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25242237942108766853388245 591614951768174223126287)
                    ·
                      rfl

theorem cell23_3456498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3456498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456498 prefixEnd_3456498 := by exact prefixLift 3456498
  have htrace : WordTrace (prefixWord ++ tailWord_3456498) baseStart_3456498 baseEnd_3456498 := by
    simpa [prefixWord, tailWord_3456498, baseEnd_3456498] using wordTrace_append hprefix tailTrace_3456498
  have hstable : (prefixWord ++ tailWord_3456498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456498).length < 2 ^ (prefixWord ++ tailWord_3456498).sum := by decide
  have hdescent : baseEnd_3456498 < baseStart_3456498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456558 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_3456558 : Nat := 118140960795 + 3456558 * 2 ^ 59
def prefixEnd_3456558 : Nat := 4983230072969 + 3 ^ 40 * 3456558 * 2
def baseEnd_3456558 : Nat := 197208407127088048292065

theorem tailTrace_3456558 : CollatzResearch.WordTrace tailWord_3456558 prefixEnd_3456558 197208407127088048292065 := by
  unfold tailWord_3456558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758878426436021744086291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84047351607658782635126885 15758878426436021744086291)
  ·
    refine ⟨23638317639654032616129437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15758878426436021744086291 23638317639654032616129437)
    ·
      refine ⟨8864369114870262231048539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23638317639654032616129437 8864369114870262231048539)
      ·
        refine ⟨13296553672305393346572809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8864369114870262231048539 13296553672305393346572809)
        ·
          refine ⟨9972415254229045009929607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13296553672305393346572809 9972415254229045009929607)
          ·
            refine ⟨14958622881343567514894411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972415254229045009929607 14958622881343567514894411)
            ·
              refine ⟨22437934322015351272341617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14958622881343567514894411 22437934322015351272341617)
              ·
                refine ⟨16828450741511513454256213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22437934322015351272341617 16828450741511513454256213)
                ·
                  refine ⟨197208407127088048292065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16828450741511513454256213 197208407127088048292065)
                  ·
                    rfl

theorem cell23_3456558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_3456558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456558 prefixEnd_3456558 := by exact prefixLift 3456558
  have htrace : WordTrace (prefixWord ++ tailWord_3456558) baseStart_3456558 baseEnd_3456558 := by
    simpa [prefixWord, tailWord_3456558, baseEnd_3456558] using wordTrace_append hprefix tailTrace_3456558
  have hstable : (prefixWord ++ tailWord_3456558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456558).length < 2 ^ (prefixWord ++ tailWord_3456558).sum := by decide
  have hdescent : baseEnd_3456558 < baseStart_3456558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456591 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_3456591 : Nat := 118140960795 + 3456591 * 2 ^ 59
def prefixEnd_3456591 : Nat := 4983230072969 + 3 ^ 40 * 3456591 * 2
def baseEnd_3456591 : Nat := 1774892609005390805515933

theorem tailTrace_3456591 : CollatzResearch.WordTrace tailWord_3456591 prefixEnd_3456591 1774892609005390805515933 := by
  unfold tailWord_3456591
  simp only [CollatzResearch.WordTrace]
  refine ⟨126072231020368620588641627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84048154013579080392427751 126072231020368620588641627)
  ·
    refine ⟨189108346530552930882962441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126072231020368620588641627 189108346530552930882962441)
    ·
      refine ⟨141831259897914698162221831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189108346530552930882962441 141831259897914698162221831)
      ·
        refine ⟨212746889846872047243332747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141831259897914698162221831 212746889846872047243332747)
        ·
          refine ⟨319120334770308070864999121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212746889846872047243332747 319120334770308070864999121)
          ·
            refine ⟨239340251077731053148749341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319120334770308070864999121 239340251077731053148749341)
            ·
              refine ⟨89752594154149144930781003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239340251077731053148749341 89752594154149144930781003)
              ·
                refine ⟨134628891231223717396171505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89752594154149144930781003 134628891231223717396171505)
                ·
                  refine ⟨100971668423417788047128629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134628891231223717396171505 100971668423417788047128629)
                  ·
                    refine ⟨9466093914695417629418309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100971668423417788047128629 9466093914695417629418309)
                    ·
                      refine ⟨1774892609005390805515933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9466093914695417629418309 1774892609005390805515933)
                      ·
                        rfl

theorem cell23_3456591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_3456591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456591 prefixEnd_3456591 := by exact prefixLift 3456591
  have htrace : WordTrace (prefixWord ++ tailWord_3456591) baseStart_3456591 baseEnd_3456591 := by
    simpa [prefixWord, tailWord_3456591, baseEnd_3456591] using wordTrace_append hprefix tailTrace_3456591
  have hstable : (prefixWord ++ tailWord_3456591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456591).length < 2 ^ (prefixWord ++ tailWord_3456591).sum := by decide
  have hdescent : baseEnd_3456591 < baseStart_3456591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456601 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_3456601 : Nat := 118140960795 + 3456601 * 2 ^ 59
def prefixEnd_3456601 : Nat := 4983230072969 + 3 ^ 40 * 3456601 * 2
def baseEnd_3456601 : Nat := 591632581270645255463629

theorem tailTrace_3456601 : CollatzResearch.WordTrace tailWord_3456601 prefixEnd_3456601 591632581270645255463629 := by
  unfold tailWord_3456601
  simp only [CollatzResearch.WordTrace]
  refine ⟨126072595750332392296505657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84048397166888261531003771 126072595750332392296505657)
  ·
    refine ⟨94554446812749294222379243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126072595750332392296505657 94554446812749294222379243)
    ·
      refine ⟨141831670219123941333568865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94554446812749294222379243 141831670219123941333568865)
      ·
        refine ⟨106373752664342956000176649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141831670219123941333568865 106373752664342956000176649)
        ·
          refine ⟨79780314498257217000132487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106373752664342956000176649 79780314498257217000132487)
          ·
            refine ⟨119670471747385825500198731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79780314498257217000132487 119670471747385825500198731)
            ·
              refine ⟨179505707621078738250298097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119670471747385825500198731 179505707621078738250298097)
              ·
                refine ⟨134629280715809053687723573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179505707621078738250298097 134629280715809053687723573)
                ·
                  refine ⟨12621495067107098783224085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134629280715809053687723573 12621495067107098783224085)
                  ·
                    refine ⟨591632581270645255463629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12621495067107098783224085 591632581270645255463629)
                    ·
                      rfl

theorem cell23_3456601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_3456601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456601 prefixEnd_3456601 := by exact prefixLift 3456601
  have htrace : WordTrace (prefixWord ++ tailWord_3456601) baseStart_3456601 baseEnd_3456601 := by
    simpa [prefixWord, tailWord_3456601, baseEnd_3456601] using wordTrace_append hprefix tailTrace_3456601
  have hstable : (prefixWord ++ tailWord_3456601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456601).length < 2 ^ (prefixWord ++ tailWord_3456601).sum := by decide
  have hdescent : baseEnd_3456601 < baseStart_3456601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456612 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_3456612 : Nat := 118140960795 + 3456612 * 2 ^ 59
def prefixEnd_3456612 : Nat := 4983230072969 + 3 ^ 40 * 3456612 * 2
def baseEnd_3456612 : Nat := 1774903392099135223353337

theorem tailTrace_3456612 : CollatzResearch.WordTrace tailWord_3456612 prefixEnd_3456612 1774903392099135223353337 := by
  unfold tailWord_3456612
  simp only [CollatzResearch.WordTrace]
  refine ⟨63036498476646270587578045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84048664635528360783437393 63036498476646270587578045)
  ·
    refine ⟨23638686928742351470341767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63036498476646270587578045 23638686928742351470341767)
    ·
      refine ⟨35458030393113527205512651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23638686928742351470341767 35458030393113527205512651)
      ·
        refine ⟨53187045589670290808268977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35458030393113527205512651 53187045589670290808268977)
        ·
          refine ⟨39890284192252718106201733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53187045589670290808268977 39890284192252718106201733)
          ·
            refine ⟨7479428286047384644912825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39890284192252718106201733 7479428286047384644912825)
            ·
              refine ⟨5609571214535538483684619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7479428286047384644912825 5609571214535538483684619)
              ·
                refine ⟨8414356821803307725526929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609571214535538483684619 8414356821803307725526929)
                ·
                  refine ⟨6310767616352480794145197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414356821803307725526929 6310767616352480794145197)
                  ·
                    refine ⟨2366537856132180297804449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6310767616352480794145197 2366537856132180297804449)
                    ·
                      refine ⟨1774903392099135223353337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366537856132180297804449 1774903392099135223353337)
                      ·
                        rfl

theorem cell23_3456612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_3456612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456612 prefixEnd_3456612 := by exact prefixLift 3456612
  have htrace : WordTrace (prefixWord ++ tailWord_3456612) baseStart_3456612 baseEnd_3456612 := by
    simpa [prefixWord, tailWord_3456612, baseEnd_3456612] using wordTrace_append hprefix tailTrace_3456612
  have hstable : (prefixWord ++ tailWord_3456612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456612).length < 2 ^ (prefixWord ++ tailWord_3456612).sum := by decide
  have hdescent : baseEnd_3456612 < baseStart_3456612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456618 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3456618 : Nat := 118140960795 + 3456618 * 2 ^ 59
def prefixEnd_3456618 : Nat := 4983230072969 + 3 ^ 40 * 3456618 * 2
def baseEnd_3456618 : Nat := 591635490994354066626103

theorem tailTrace_3456618 : CollatzResearch.WordTrace tailWord_3456618 prefixEnd_3456618 591635490994354066626103 := by
  unfold tailWord_3456618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31518303947817701049968627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84048810527513869466583005 31518303947817701049968627)
  ·
    refine ⟨47277455921726551574952941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31518303947817701049968627 47277455921726551574952941)
    ·
      refine ⟨17729045970647456840607353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47277455921726551574952941 17729045970647456840607353)
      ·
        refine ⟨13296784477985592630455515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17729045970647456840607353 13296784477985592630455515)
        ·
          refine ⟨19945176716978388945683273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13296784477985592630455515 19945176716978388945683273)
          ·
            refine ⟨14958882537733791709262455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19945176716978388945683273 14958882537733791709262455)
            ·
              refine ⟨22438323806600687563893683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14958882537733791709262455 22438323806600687563893683)
              ·
                refine ⟨33657485709901031345840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22438323806600687563893683 33657485709901031345840525)
                ·
                  refine ⟨12621557141212886754690197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33657485709901031345840525 12621557141212886754690197)
                  ·
                    refine ⟨591635490994354066626103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12621557141212886754690197 591635490994354066626103)
                    ·
                      rfl

theorem cell23_3456618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3456618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456618 prefixEnd_3456618 := by exact prefixLift 3456618
  have htrace : WordTrace (prefixWord ++ tailWord_3456618) baseStart_3456618 baseEnd_3456618 := by
    simpa [prefixWord, tailWord_3456618, baseEnd_3456618] using wordTrace_append hprefix tailTrace_3456618
  have hstable : (prefixWord ++ tailWord_3456618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456618).length < 2 ^ (prefixWord ++ tailWord_3456618).sum := by decide
  have hdescent : baseEnd_3456618 < baseStart_3456618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456635 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 2, 4]
def baseStart_3456635 : Nat := 118140960795 + 3456635 * 2 ^ 59
def prefixEnd_3456635 : Nat := 4983230072969 + 3 ^ 40 * 3456635 * 2
def baseEnd_3456635 : Nat := 591638400718062877788577

theorem tailTrace_3456635 : CollatzResearch.WordTrace tailWord_3456635 prefixEnd_3456635 591638400718062877788577 := by
  unfold tailWord_3456635
  simp only [CollatzResearch.WordTrace]
  refine ⟨126073835832209216103243359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84049223888139477402162239 126073835832209216103243359)
  ·
    refine ⟨189110753748313824154865039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126073835832209216103243359 189110753748313824154865039)
    ·
      refine ⟨283666130622470736232297559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189110753748313824154865039 283666130622470736232297559)
      ·
        refine ⟨425499195933706104348446339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283666130622470736232297559 425499195933706104348446339)
        ·
          refine ⟨638248793900559156522669509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425499195933706104348446339 638248793900559156522669509)
          ·
            refine ⟨119671648856354841848000533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 638248793900559156522669509 119671648856354841848000533)
            ·
              refine ⟨5609608540141633211625025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119671648856354841848000533 5609608540141633211625025)
              ·
                refine ⟨4207206405106224908718769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609608540141633211625025 4207206405106224908718769)
                ·
                  refine ⟨3155404803829668681539077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207206405106224908718769 3155404803829668681539077)
                  ·
                    refine ⟨591638400718062877788577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155404803829668681539077 591638400718062877788577)
                    ·
                      rfl

theorem cell23_3456635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 4].length) (baseStart_3456635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456635 prefixEnd_3456635 := by exact prefixLift 3456635
  have htrace : WordTrace (prefixWord ++ tailWord_3456635) baseStart_3456635 baseEnd_3456635 := by
    simpa [prefixWord, tailWord_3456635, baseEnd_3456635] using wordTrace_append hprefix tailTrace_3456635
  have hstable : (prefixWord ++ tailWord_3456635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456635).length < 2 ^ (prefixWord ++ tailWord_3456635).sum := by decide
  have hdescent : baseEnd_3456635 < baseStart_3456635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456675 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 3]
def baseStart_3456675 : Nat := 118140960795 + 3456675 * 2 ^ 59
def prefixEnd_3456675 : Nat := 4983230072969 + 3 ^ 40 * 3456675 * 2
def baseEnd_3456675 : Nat := 1774935741380368476865547

theorem tailTrace_3456675 : CollatzResearch.WordTrace tailWord_3456675 prefixEnd_3456675 1774935741380368476865547 := by
  unfold tailWord_3456675
  simp only [CollatzResearch.WordTrace]
  refine ⟨126075294752064302934699479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84050196501376201956466319 126075294752064302934699479)
  ·
    refine ⟨189112942128096454402049219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126075294752064302934699479 189112942128096454402049219)
    ·
      refine ⟨283669413192144681603073829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189112942128096454402049219 283669413192144681603073829)
      ·
        refine ⟨53188014973527127800576343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283669413192144681603073829 53188014973527127800576343)
        ·
          refine ⟨79782022460290691700864515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53188014973527127800576343 79782022460290691700864515)
          ·
            refine ⟨119673033690436037551296773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79782022460290691700864515 119673033690436037551296773)
            ·
              refine ⟨22438693816956757040868145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119673033690436037551296773 22438693816956757040868145)
              ·
                refine ⟨16829020362717567780651109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22438693816956757040868145 16829020362717567780651109)
                ·
                  refine ⟨3155441318009543958872083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16829020362717567780651109 3155441318009543958872083)
                  ·
                    refine ⟨4733161977014315938308125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155441318009543958872083 4733161977014315938308125)
                    ·
                      refine ⟨1774935741380368476865547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4733161977014315938308125 1774935741380368476865547)
                      ·
                        rfl

theorem cell23_3456675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_3456675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456675 prefixEnd_3456675 := by exact prefixLift 3456675
  have htrace : WordTrace (prefixWord ++ tailWord_3456675) baseStart_3456675 baseEnd_3456675 := by
    simpa [prefixWord, tailWord_3456675, baseEnd_3456675] using wordTrace_append hprefix tailTrace_3456675
  have hstable : (prefixWord ++ tailWord_3456675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456675).length < 2 ^ (prefixWord ++ tailWord_3456675).sum := by decide
  have hdescent : baseEnd_3456675 < baseStart_3456675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456676 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_3456676 : Nat := 118140960795 + 3456676 * 2 ^ 59
def prefixEnd_3456676 : Nat := 4983230072969 + 3 ^ 40 * 3456676 * 2
def baseEnd_3456676 : Nat := 1774936254861022972953043

theorem tailTrace_3456676 : CollatzResearch.WordTrace tailWord_3456676 prefixEnd_3456676 1774936254861022972953043 := by
  unfold tailWord_3456676
  simp only [CollatzResearch.WordTrace]
  refine ⟨63037665612530340052742941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84050220816707120070323921 63037665612530340052742941)
  ·
    refine ⟨23639124604698877519778603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63037665612530340052742941 23639124604698877519778603)
    ·
      refine ⟨35458686907048316279667905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23639124604698877519778603 35458686907048316279667905)
      ·
        refine ⟨26594015180286237209750929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35458686907048316279667905 26594015180286237209750929)
        ·
          refine ⟨19945511385214677907313197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26594015180286237209750929 19945511385214677907313197)
          ·
            refine ⟨7479566769455504215242449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19945511385214677907313197 7479566769455504215242449)
            ·
              refine ⟨5609675077091628161431837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7479566769455504215242449 5609675077091628161431837)
              ·
                refine ⟨2103628153909360560536939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5609675077091628161431837 2103628153909360560536939)
                ·
                  refine ⟨3155442230864040840805409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103628153909360560536939 3155442230864040840805409)
                  ·
                    refine ⟨2366581673148030630604057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3155442230864040840805409 2366581673148030630604057)
                    ·
                      refine ⟨1774936254861022972953043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366581673148030630604057 1774936254861022972953043)
                      ·
                        rfl

theorem cell23_3456676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_3456676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456676 prefixEnd_3456676 := by exact prefixLift 3456676
  have htrace : WordTrace (prefixWord ++ tailWord_3456676) baseStart_3456676 baseEnd_3456676 := by
    simpa [prefixWord, tailWord_3456676, baseEnd_3456676] using wordTrace_append hprefix tailTrace_3456676
  have hstable : (prefixWord ++ tailWord_3456676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456676).length < 2 ^ (prefixWord ++ tailWord_3456676).sum := by decide
  have hdescent : baseEnd_3456676 < baseStart_3456676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456686 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3456686 : Nat := 118140960795 + 3456686 * 2 ^ 59
def prefixEnd_3456686 : Nat := 4983230072969 + 3 ^ 40 * 3456686 * 2
def baseEnd_3456686 : Nat := 591647129889189311275999

theorem tailTrace_3456686 : CollatzResearch.WordTrace tailWord_3456686 prefixEnd_3456686 591647129889189311275999 := by
  unfold tailWord_3456686
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759461994378056476668739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84050463970016301208899941 15759461994378056476668739)
  ·
    refine ⟨23639192991567084715003109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15759461994378056476668739 23639192991567084715003109)
    ·
      refine ⟨4432348685918828384063083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23639192991567084715003109 4432348685918828384063083)
      ·
        refine ⟨6648523028878242576094625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4432348685918828384063083 6648523028878242576094625)
        ·
          refine ⟨4986392271658681932070969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6648523028878242576094625 4986392271658681932070969)
          ·
            refine ⟨3739794203744011449053227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4986392271658681932070969 3739794203744011449053227)
            ·
              refine ⟨5609691305616017173579841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739794203744011449053227 5609691305616017173579841)
              ·
                refine ⟨4207268479212012880184881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609691305616017173579841 4207268479212012880184881)
                ·
                  refine ⟨3155451359409009660138661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207268479212012880184881 3155451359409009660138661)
                  ·
                    refine ⟨591647129889189311275999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155451359409009660138661 591647129889189311275999)
                    ·
                      rfl

theorem cell23_3456686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3456686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456686 prefixEnd_3456686 := by exact prefixLift 3456686
  have htrace : WordTrace (prefixWord ++ tailWord_3456686) baseStart_3456686 baseEnd_3456686 := by
    simpa [prefixWord, tailWord_3456686, baseEnd_3456686] using wordTrace_append hprefix tailTrace_3456686
  have hstable : (prefixWord ++ tailWord_3456686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456686).length < 2 ^ (prefixWord ++ tailWord_3456686).sum := by decide
  have hdescent : baseEnd_3456686 < baseStart_3456686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456749 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3456749 : Nat := 118140960795 + 3456749 * 2 ^ 59
def prefixEnd_3456749 : Nat := 4983230072969 + 3 ^ 40 * 3456749 * 2
def baseEnd_3456749 : Nat := 1774973738948801187340207

theorem tailTrace_3456749 : CollatzResearch.WordTrace tailWord_3456749 prefixEnd_3456749 1774973738948801187340207 := by
  unfold tailWord_3456749
  simp only [CollatzResearch.WordTrace]
  refine ⟨126077993753796213572893301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84051995835864142381928867 126077993753796213572893301)
  ·
    refine ⟨11819811914418395022458747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126077993753796213572893301 11819811914418395022458747)
    ·
      refine ⟨17729717871627592533688121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11819811914418395022458747 17729717871627592533688121)
      ·
        refine ⟨13297288403720694400266091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17729717871627592533688121 13297288403720694400266091)
        ·
          refine ⟨19945932605581041600399137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297288403720694400266091 19945932605581041600399137)
          ·
            refine ⟨14959449454185781200299353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19945932605581041600399137 14959449454185781200299353)
            ·
              refine ⟨11219587090639335900224515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14959449454185781200299353 11219587090639335900224515)
              ·
                refine ⟨16829380635959003850336773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11219587090639335900224515 16829380635959003850336773)
                ·
                  refine ⟨3155508869242313221938145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16829380635959003850336773 3155508869242313221938145)
                  ·
                    refine ⟨2366631651931734916453609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3155508869242313221938145 2366631651931734916453609)
                    ·
                      refine ⟨1774973738948801187340207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366631651931734916453609 1774973738948801187340207)
                      ·
                        rfl

theorem cell23_3456749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3456749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456749 prefixEnd_3456749 := by exact prefixLift 3456749
  have htrace : WordTrace (prefixWord ++ tailWord_3456749) baseStart_3456749 baseEnd_3456749 := by
    simpa [prefixWord, tailWord_3456749, baseEnd_3456749] using wordTrace_append hprefix tailTrace_3456749
  have hstable : (prefixWord ++ tailWord_3456749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456749).length < 2 ^ (prefixWord ++ tailWord_3456749).sum := by decide
  have hdescent : baseEnd_3456749 < baseStart_3456749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456755 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 5]
def baseStart_3456755 : Nat := 118140960795 + 3456755 * 2 ^ 59
def prefixEnd_3456755 : Nat := 4983230072969 + 3 ^ 40 * 3456755 * 2
def baseEnd_3456755 : Nat := 197219646648080907096131

theorem tailTrace_3456755 : CollatzResearch.WordTrace tailWord_3456755 prefixEnd_3456755 197219646648080907096131 := by
  unfold tailWord_3456755
  simp only [CollatzResearch.WordTrace]
  refine ⟨126078212591774476597611719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84052141727849651065074479 126078212591774476597611719)
  ·
    refine ⟨189117318887661714896417579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126078212591774476597611719 189117318887661714896417579)
    ·
      refine ⟨283675978331492572344626369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189117318887661714896417579 283675978331492572344626369)
      ·
        refine ⟨212756983748619429258469777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283675978331492572344626369 212756983748619429258469777)
        ·
          refine ⟨159567737811464571943852333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212756983748619429258469777 159567737811464571943852333)
          ·
            refine ⟨59837901679299214478944625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159567737811464571943852333 59837901679299214478944625)
            ·
              refine ⟨44878426259474410859208469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59837901679299214478944625 44878426259474410859208469)
              ·
                refine ⟨2103676230912863009025397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44878426259474410859208469 2103676230912863009025397)
                ·
                  refine ⟨197219646648080907096131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103676230912863009025397 197219646648080907096131)
                  ·
                    rfl

theorem cell23_3456755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 5].length) (baseStart_3456755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456755 prefixEnd_3456755 := by exact prefixLift 3456755
  have htrace : WordTrace (prefixWord ++ tailWord_3456755) baseStart_3456755 baseEnd_3456755 := by
    simpa [prefixWord, tailWord_3456755, baseEnd_3456755] using wordTrace_append hprefix tailTrace_3456755
  have hstable : (prefixWord ++ tailWord_3456755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456755).length < 2 ^ (prefixWord ++ tailWord_3456755).sum := by decide
  have hdescent : baseEnd_3456755 < baseStart_3456755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456849 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 1, 4]
def baseStart_3456849 : Nat := 118140960795 + 3456849 * 2 ^ 59
def prefixEnd_3456849 : Nat := 4983230072969 + 3 ^ 40 * 3456849 * 2
def baseEnd_3456849 : Nat := 591675029004750265363249

theorem tailTrace_3456849 : CollatzResearch.WordTrace tailWord_3456849 prefixEnd_3456849 591675029004750265363249 := by
  unfold tailWord_3456849
  simp only [CollatzResearch.WordTrace]
  refine ⟨126081641053433930651533601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84054427368955953767689067 126081641053433930651533601)
  ·
    refine ⟨94561230790075447988650201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126081641053433930651533601 94561230790075447988650201)
    ·
      refine ⟨70920923092556585991487651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94561230790075447988650201 70920923092556585991487651)
      ·
        refine ⟨106381384638834878987231477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70920923092556585991487651 106381384638834878987231477)
        ·
          refine ⟨9973254809890769905052951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106381384638834878987231477 9973254809890769905052951)
          ·
            refine ⟨14959882214836154857579427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9973254809890769905052951 14959882214836154857579427)
            ·
              refine ⟨22439823322254232286369141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14959882214836154857579427 22439823322254232286369141)
              ·
                refine ⟨2103733436461334276847107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22439823322254232286369141 2103733436461334276847107)
                ·
                  refine ⟨3155600154692001415270661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103733436461334276847107 3155600154692001415270661)
                  ·
                    refine ⟨591675029004750265363249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155600154692001415270661 591675029004750265363249)
                    ·
                      rfl

theorem cell23_3456849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_3456849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456849 prefixEnd_3456849 := by exact prefixLift 3456849
  have htrace : WordTrace (prefixWord ++ tailWord_3456849) baseStart_3456849 baseEnd_3456849 := by
    simpa [prefixWord, tailWord_3456849, baseEnd_3456849] using wordTrace_append hprefix tailTrace_3456849
  have hstable : (prefixWord ++ tailWord_3456849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456849).length < 2 ^ (prefixWord ++ tailWord_3456849).sum := by decide
  have hdescent : baseEnd_3456849 < baseStart_3456849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456866 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3456866 : Nat := 118140960795 + 3456866 * 2 ^ 59
def prefixEnd_3456866 : Nat := 4983230072969 + 3 ^ 40 * 3456866 * 2
def baseEnd_3456866 : Nat := 591677938728459076525723

theorem tailTrace_3456866 : CollatzResearch.WordTrace tailWord_3456866 prefixEnd_3456866 591677938728459076525723 := by
  unfold tailWord_3456866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31520565273593085638725613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84054840729581561703268301 31520565273593085638725613)
  ·
    refine ⟨11820211977597407114522105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31520565273593085638725613 11820211977597407114522105)
    ·
      refine ⟨8865158983198055335891579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11820211977597407114522105 8865158983198055335891579)
      ·
        refine ⟨13297738474797083003837369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865158983198055335891579 13297738474797083003837369)
        ·
          refine ⟨9973303856097812252878027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13297738474797083003837369 9973303856097812252878027)
          ·
            refine ⟨14959955784146718379317041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9973303856097812252878027 14959955784146718379317041)
            ·
              refine ⟨11219966838110038784487781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14959955784146718379317041 11219966838110038784487781)
              ·
                refine ⟨2103743782145632272091459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11219966838110038784487781 2103743782145632272091459)
                ·
                  refine ⟨3155615673218448408137189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103743782145632272091459 3155615673218448408137189)
                  ·
                    refine ⟨591677938728459076525723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155615673218448408137189 591677938728459076525723)
                    ·
                      rfl

theorem cell23_3456866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3456866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456866 prefixEnd_3456866 := by exact prefixLift 3456866
  have htrace : WordTrace (prefixWord ++ tailWord_3456866) baseStart_3456866 baseEnd_3456866 := by
    simpa [prefixWord, tailWord_3456866, baseEnd_3456866] using wordTrace_append hprefix tailTrace_3456866
  have hstable : (prefixWord ++ tailWord_3456866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456866).length < 2 ^ (prefixWord ++ tailWord_3456866).sum := by decide
  have hdescent : baseEnd_3456866 < baseStart_3456866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456905 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_3456905 : Nat := 118140960795 + 3456905 * 2 ^ 59
def prefixEnd_3456905 : Nat := 4983230072969 + 3 ^ 40 * 3456905 * 2
def baseEnd_3456905 : Nat := 591684613976967525663163

theorem tailTrace_3456905 : CollatzResearch.WordTrace tailWord_3456905 prefixEnd_3456905 591684613976967525663163 := by
  unfold tailWord_3456905
  simp only [CollatzResearch.WordTrace]
  refine ⟨126083683541231052215572169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84055789027487368143714779 126083683541231052215572169)
  ·
    refine ⟨94562762655923289161679127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126083683541231052215572169 94562762655923289161679127)
    ·
      refine ⟨141844143983884933742518691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94562762655923289161679127 141844143983884933742518691)
      ·
        refine ⟨212766215975827400613778037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141844143983884933742518691 212766215975827400613778037)
        ·
          refine ⟨19946832747733818807541691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212766215975827400613778037 19946832747733818807541691)
          ·
            refine ⟨29920249121600728211312537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19946832747733818807541691 29920249121600728211312537)
            ·
              refine ⟨22440186841200546158484403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29920249121600728211312537 22440186841200546158484403)
              ·
                refine ⟨33660280261800819237726605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22440186841200546158484403 33660280261800819237726605)
                ·
                  refine ⟨12622605098175307214147477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33660280261800819237726605 12622605098175307214147477)
                  ·
                    refine ⟨591684613976967525663163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12622605098175307214147477 591684613976967525663163)
                    ·
                      rfl

theorem cell23_3456905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_3456905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456905 prefixEnd_3456905 := by exact prefixLift 3456905
  have htrace : WordTrace (prefixWord ++ tailWord_3456905) baseStart_3456905 baseEnd_3456905 := by
    simpa [prefixWord, tailWord_3456905, baseEnd_3456905] using wordTrace_append hprefix tailTrace_3456905
  have hstable : (prefixWord ++ tailWord_3456905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456905).length < 2 ^ (prefixWord ++ tailWord_3456905).sum := by decide
  have hdescent : baseEnd_3456905 < baseStart_3456905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456915 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 3]
def baseStart_3456915 : Nat := 118140960795 + 3456915 * 2 ^ 59
def prefixEnd_3456915 : Nat := 4983230072969 + 3 ^ 40 * 3456915 * 2
def baseEnd_3456915 : Nat := 1775058976737447537864443

theorem tailTrace_3456915 : CollatzResearch.WordTrace tailWord_3456915 prefixEnd_3456915 1775058976737447537864443 := by
  unfold tailWord_3456915
  simp only [CollatzResearch.WordTrace]
  refine ⟨126084048271194823923436199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84056032180796549282290799 126084048271194823923436199)
  ·
    refine ⟨189126072406792235885154299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126084048271194823923436199 189126072406792235885154299)
    ·
      refine ⟨283689108610188353827731449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189126072406792235885154299 283689108610188353827731449)
      ·
        refine ⟨212766831457641265370798587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283689108610188353827731449 212766831457641265370798587)
        ·
          refine ⟨319150247186461898056197881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212766831457641265370798587 319150247186461898056197881)
          ·
            refine ⟨239362685389846423542148411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319150247186461898056197881 239362685389846423542148411)
            ·
              refine ⟨359044028084769635313222617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239362685389846423542148411 359044028084769635313222617)
              ·
                refine ⟨269283021063577226484916963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359044028084769635313222617 269283021063577226484916963)
                ·
                  refine ⟨403924531595365839727375445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269283021063577226484916963 403924531595365839727375445)
                  ·
                    refine ⟨4733490604633193434305181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 403924531595365839727375445 4733490604633193434305181)
                    ·
                      refine ⟨1775058976737447537864443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4733490604633193434305181 1775058976737447537864443)
                      ·
                        rfl

theorem cell23_3456915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_3456915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456915 prefixEnd_3456915 := by exact prefixLift 3456915
  have htrace : WordTrace (prefixWord ++ tailWord_3456915) baseStart_3456915 baseEnd_3456915 := by
    simpa [prefixWord, tailWord_3456915, baseEnd_3456915] using wordTrace_append hprefix tailTrace_3456915
  have hstable : (prefixWord ++ tailWord_3456915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456915).length < 2 ^ (prefixWord ++ tailWord_3456915).sum := by decide
  have hdescent : baseEnd_3456915 < baseStart_3456915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456916 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_3456916 : Nat := 118140960795 + 3456916 * 2 ^ 59
def prefixEnd_3456916 : Nat := 4983230072969 + 3 ^ 40 * 3456916 * 2
def baseEnd_3456916 : Nat := 1775059490218102033951939

theorem tailTrace_3456916 : CollatzResearch.WordTrace tailWord_3456916 prefixEnd_3456916 1775059490218102033951939 := by
  unfold tailWord_3456916
  simp only [CollatzResearch.WordTrace]
  refine ⟨63042042372095600547111301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84056056496127467396148401 63042042372095600547111301)
  ·
    refine ⟨11820382944767925102583369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63042042372095600547111301 11820382944767925102583369)
    ·
      refine ⟨8865287208575943826937527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11820382944767925102583369 8865287208575943826937527)
      ·
        refine ⟨13297930812863915740406291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865287208575943826937527 13297930812863915740406291)
        ·
          refine ⟨19946896219295873610609437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297930812863915740406291 19946896219295873610609437)
          ·
            refine ⟨7480086082235952603978539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19946896219295873610609437 7480086082235952603978539)
            ·
              refine ⟨11220129123353928905967809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480086082235952603978539 11220129123353928905967809)
              ·
                refine ⟨8415096842515446679475857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11220129123353928905967809 8415096842515446679475857)
                ·
                  refine ⟨6311322631886585009606893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8415096842515446679475857 6311322631886585009606893)
                  ·
                    refine ⟨2366745986957469378602585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6311322631886585009606893 2366745986957469378602585)
                    ·
                      refine ⟨1775059490218102033951939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366745986957469378602585 1775059490218102033951939)
                      ·
                        rfl

theorem cell23_3456916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_3456916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456916 prefixEnd_3456916 := by exact prefixLift 3456916
  have htrace : WordTrace (prefixWord ++ tailWord_3456916) baseStart_3456916 baseEnd_3456916 := by
    simpa [prefixWord, tailWord_3456916, baseEnd_3456916] using wordTrace_append hprefix tailTrace_3456916
  have hstable : (prefixWord ++ tailWord_3456916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456916).length < 2 ^ (prefixWord ++ tailWord_3456916).sum := by decide
  have hdescent : baseEnd_3456916 < baseStart_3456916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456932 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_3456932 : Nat := 118140960795 + 3456932 * 2 ^ 59
def prefixEnd_3456932 : Nat := 4983230072969 + 3 ^ 40 * 3456932 * 2
def baseEnd_3456932 : Nat := 1775067705908573971351865

theorem tailTrace_3456932 : CollatzResearch.WordTrace tailWord_3456932 prefixEnd_3456932 1775067705908573971351865 := by
  unfold tailWord_3456932
  simp only [CollatzResearch.WordTrace]
  refine ⟨63042334156066617913402525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84056445541422157217870033 63042334156066617913402525)
  ·
    refine ⟨23640875308524981717525947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63042334156066617913402525 23640875308524981717525947)
    ·
      refine ⟨35461312962787472576288921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23640875308524981717525947 35461312962787472576288921)
      ·
        refine ⟨26595984722090604432216691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35461312962787472576288921 26595984722090604432216691)
        ·
          refine ⟨39893977083135906648325037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26595984722090604432216691 39893977083135906648325037)
          ·
            refine ⟨14960241406175964993121889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39893977083135906648325037 14960241406175964993121889)
            ·
              refine ⟨11220181054631973744841417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14960241406175964993121889 11220181054631973744841417)
              ·
                refine ⟨8415135790973980308631063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11220181054631973744841417 8415135790973980308631063)
                ·
                  refine ⟨12622703686460970462946595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415135790973980308631063 12622703686460970462946595)
                  ·
                    refine ⟨18934055529691455694419893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12622703686460970462946595 18934055529691455694419893)
                    ·
                      refine ⟨1775067705908573971351865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18934055529691455694419893 1775067705908573971351865)
                      ·
                        rfl

theorem cell23_3456932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_3456932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456932 prefixEnd_3456932 := by exact prefixLift 3456932
  have htrace : WordTrace (prefixWord ++ tailWord_3456932) baseStart_3456932 baseEnd_3456932 := by
    simpa [prefixWord, tailWord_3456932, baseEnd_3456932] using wordTrace_append hprefix tailTrace_3456932
  have hstable : (prefixWord ++ tailWord_3456932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456932).length < 2 ^ (prefixWord ++ tailWord_3456932).sum := by decide
  have hdescent : baseEnd_3456932 < baseStart_3456932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456949 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3456949 : Nat := 118140960795 + 3456949 * 2 ^ 59
def prefixEnd_3456949 : Nat := 4983230072969 + 3 ^ 40 * 3456949 * 2
def baseEnd_3456949 : Nat := 1775076435079700404839287

theorem tailTrace_3456949 : CollatzResearch.WordTrace tailWord_3456949 prefixEnd_3456949 1775076435079700404839287 := by
  unfold tailWord_3456949
  simp only [CollatzResearch.WordTrace]
  refine ⟨126085288353071647730173901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84056858902047765153449267 126085288353071647730173901)
  ·
    refine ⟨47281983132401867898815213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126085288353071647730173901 47281983132401867898815213)
    ·
      refine ⟨17730743674650700462055705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47281983132401867898815213 17730743674650700462055705)
      ·
        refine ⟨13298057755988025346541779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17730743674650700462055705 13298057755988025346541779)
        ·
          refine ⟨19947086633982038019812669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298057755988025346541779 19947086633982038019812669)
          ·
            refine ⟨7480157487743264257429751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19947086633982038019812669 7480157487743264257429751)
            ·
              refine ⟨11220236231614896386144627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480157487743264257429751 11220236231614896386144627)
              ·
                refine ⟨16830354347422344579216941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11220236231614896386144627 16830354347422344579216941)
                ·
                  refine ⟨6311382880283379217206353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16830354347422344579216941 6311382880283379217206353)
                  ·
                    refine ⟨4733537160212534412904765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6311382880283379217206353 4733537160212534412904765)
                    ·
                      refine ⟨1775076435079700404839287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4733537160212534412904765 1775076435079700404839287)
                      ·
                        rfl

theorem cell23_3456949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3456949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3456949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3456949 prefixEnd_3456949 := by exact prefixLift 3456949
  have htrace : WordTrace (prefixWord ++ tailWord_3456949) baseStart_3456949 baseEnd_3456949 := by
    simpa [prefixWord, tailWord_3456949, baseEnd_3456949] using wordTrace_append hprefix tailTrace_3456949
  have hstable : (prefixWord ++ tailWord_3456949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456949).length < 2 ^ (prefixWord ++ tailWord_3456949).sum := by decide
  have hdescent : baseEnd_3456949 < baseStart_3456949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457002 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3457002 : Nat := 118140960795 + 3457002 * 2 ^ 59
def prefixEnd_3457002 : Nat := 4983230072969 + 3 ^ 40 * 3457002 * 2
def baseEnd_3457002 : Nat := 1775103649554388697476543

theorem tailTrace_3457002 : CollatzResearch.WordTrace tailWord_3457002 prefixEnd_3457002 1775103649554388697476543 := by
  unfold tailWord_3457002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31521805355469909445463315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84058147614586425187902173 31521805355469909445463315)
  ·
    refine ⟨47282708033204864168194973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31521805355469909445463315 47282708033204864168194973)
    ·
      refine ⟨17731015512451824063073115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47282708033204864168194973 17731015512451824063073115)
      ·
        refine ⟨26596523268677736094609673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17731015512451824063073115 26596523268677736094609673)
        ·
          refine ⟨19947392451508302070957255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26596523268677736094609673 19947392451508302070957255)
          ·
            refine ⟨29921088677262453106435883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19947392451508302070957255 29921088677262453106435883)
            ·
              refine ⟨44881633015893679659653825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29921088677262453106435883 44881633015893679659653825)
              ·
                refine ⟨33661224761920259744740369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44881633015893679659653825 33661224761920259744740369)
                ·
                  refine ⟨25245918571440194808555277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33661224761920259744740369 25245918571440194808555277)
                  ·
                    refine ⟨9467219464290073053208229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25245918571440194808555277 9467219464290073053208229)
                    ·
                      refine ⟨1775103649554388697476543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9467219464290073053208229 1775103649554388697476543)
                      ·
                        rfl

theorem cell23_3457002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3457002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457002 prefixEnd_3457002 := by exact prefixLift 3457002
  have htrace : WordTrace (prefixWord ++ tailWord_3457002) baseStart_3457002 baseEnd_3457002 := by
    simpa [prefixWord, tailWord_3457002, baseEnd_3457002] using wordTrace_append hprefix tailTrace_3457002
  have hstable : (prefixWord ++ tailWord_3457002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457002).length < 2 ^ (prefixWord ++ tailWord_3457002).sum := by decide
  have hdescent : baseEnd_3457002 < baseStart_3457002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457006 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_3457006 : Nat := 118140960795 + 3457006 * 2 ^ 59
def prefixEnd_3457006 : Nat := 4983230072969 + 3 ^ 40 * 3457006 * 2
def baseEnd_3457006 : Nat := 1775105703477006681826525

theorem tailTrace_3457006 : CollatzResearch.WordTrace tailWord_3457006 prefixEnd_3457006 1775105703477006681826525 := by
  unfold tailWord_3457006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760920914233143308124859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84058244875910097643332581 15760920914233143308124859)
  ·
    refine ⟨23641381371349714962187289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15760920914233143308124859 23641381371349714962187289)
    ·
      refine ⟨17731036028512286221640467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23641381371349714962187289 17731036028512286221640467)
      ·
        refine ⟨26596554042768429332460701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17731036028512286221640467 26596554042768429332460701)
        ·
          refine ⟨9973707766038160999672763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26596554042768429332460701 9973707766038160999672763)
          ·
            refine ⟨14960561649057241499509145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9973707766038160999672763 14960561649057241499509145)
            ·
              refine ⟨11220421236792931124631859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14960561649057241499509145 11220421236792931124631859)
              ·
                refine ⟨16830631855189396686947789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11220421236792931124631859 16830631855189396686947789)
                ·
                  refine ⟨6311486945696023757605421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16830631855189396686947789 6311486945696023757605421)
                  ·
                    refine ⟨2366807604636008909102033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6311486945696023757605421 2366807604636008909102033)
                    ·
                      refine ⟨1775105703477006681826525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366807604636008909102033 1775105703477006681826525)
                      ·
                        rfl

theorem cell23_3457006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_3457006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457006 prefixEnd_3457006 := by exact prefixLift 3457006
  have htrace : WordTrace (prefixWord ++ tailWord_3457006) baseStart_3457006 baseEnd_3457006 := by
    simpa [prefixWord, tailWord_3457006, baseEnd_3457006] using wordTrace_append hprefix tailTrace_3457006
  have hstable : (prefixWord ++ tailWord_3457006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457006).length < 2 ^ (prefixWord ++ tailWord_3457006).sum := by decide
  have hdescent : baseEnd_3457006 < baseStart_3457006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457019 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 1, 4, 2]
def baseStart_3457019 : Nat := 118140960795 + 3457019 * 2 ^ 59
def prefixEnd_3457019 : Nat := 4983230072969 + 3 ^ 40 * 3457019 * 2
def baseEnd_3457019 : Nat := 1775112378725515130963965

theorem tailTrace_3457019 : CollatzResearch.WordTrace tailWord_3457019 prefixEnd_3457019 1775112378725515130963965 := by
  unfold tailWord_3457019
  simp only [CollatzResearch.WordTrace]
  refine ⟨126087841462818049685222111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84058560975212033123481407 126087841462818049685222111)
  ·
    refine ⟨189131762194227074527833167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126087841462818049685222111 189131762194227074527833167)
    ·
      refine ⟨283697643291340611791749751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189131762194227074527833167 283697643291340611791749751)
      ·
        refine ⟨425546464937010917687624627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283697643291340611791749751 425546464937010917687624627)
        ·
          refine ⟨638319697405516376531436941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425546464937010917687624627 638319697405516376531436941)
          ·
            refine ⟨239369886527068641199288853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638319697405516376531436941 239369886527068641199288853)
            ·
              refine ⟨11220463430956342556216665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239369886527068641199288853 11220463430956342556216665)
              ·
                refine ⟨8415347573217256917162499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11220463430956342556216665 8415347573217256917162499)
                ·
                  refine ⟨12623021359825885375743749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415347573217256917162499 12623021359825885375743749)
                  ·
                    refine ⟨2366816504967353507951953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12623021359825885375743749 2366816504967353507951953)
                    ·
                      refine ⟨1775112378725515130963965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366816504967353507951953 1775112378725515130963965)
                      ·
                        rfl

theorem cell23_3457019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4, 2].length) (baseStart_3457019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457019 prefixEnd_3457019 := by exact prefixLift 3457019
  have htrace : WordTrace (prefixWord ++ tailWord_3457019) baseStart_3457019 baseEnd_3457019 := by
    simpa [prefixWord, tailWord_3457019, baseEnd_3457019] using wordTrace_append hprefix tailTrace_3457019
  have hstable : (prefixWord ++ tailWord_3457019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457019).length < 2 ^ (prefixWord ++ tailWord_3457019).sum := by decide
  have hdescent : baseEnd_3457019 < baseStart_3457019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457032 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3457032 : Nat := 118140960795 + 3457032 * 2 ^ 59
def prefixEnd_3457032 : Nat := 4983230072969 + 3 ^ 40 * 3457032 * 2
def baseEnd_3457032 : Nat := 1775119053974023580101405

theorem tailTrace_3457032 : CollatzResearch.WordTrace tailWord_3457032 prefixEnd_3457032 1775119053974023580101405 := by
  unfold tailWord_3457032
  simp only [CollatzResearch.WordTrace]
  refine ⟨63044157805885476452722675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84058877074513968603630233 63044157805885476452722675)
  ·
    refine ⟨94566236708828214679084013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63044157805885476452722675 94566236708828214679084013)
    ·
      refine ⟨35462338765810580504656505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94566236708828214679084013 35462338765810580504656505)
      ·
        refine ⟨26596754074357935378492379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35462338765810580504656505 26596754074357935378492379)
        ·
          refine ⟨39895131111536903067738569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26596754074357935378492379 39895131111536903067738569)
          ·
            refine ⟨29921348333652677300803927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39895131111536903067738569 29921348333652677300803927)
            ·
              refine ⟨44882022500479015951205891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29921348333652677300803927 44882022500479015951205891)
              ·
                refine ⟨67323033750718523926808837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44882022500479015951205891 67323033750718523926808837)
                ·
                  refine ⟨12623068828259723236276657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67323033750718523926808837 12623068828259723236276657)
                  ·
                    refine ⟨9467301621194792427207493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12623068828259723236276657 9467301621194792427207493)
                    ·
                      refine ⟨1775119053974023580101405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9467301621194792427207493 1775119053974023580101405)
                      ·
                        rfl

theorem cell23_3457032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3457032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457032 prefixEnd_3457032 := by exact prefixLift 3457032
  have htrace : WordTrace (prefixWord ++ tailWord_3457032) baseStart_3457032 baseEnd_3457032 := by
    simpa [prefixWord, tailWord_3457032, baseEnd_3457032] using wordTrace_append hprefix tailTrace_3457032
  have hstable : (prefixWord ++ tailWord_3457032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457032).length < 2 ^ (prefixWord ++ tailWord_3457032).sum := by decide
  have hdescent : baseEnd_3457032 < baseStart_3457032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457036 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 4, 2, 2]
def baseStart_3457036 : Nat := 118140960795 + 3457036 * 2 ^ 59
def prefixEnd_3457036 : Nat := 4983230072969 + 3 ^ 40 * 3457036 * 2
def baseEnd_3457036 : Nat := 1775121107896641564451387

theorem tailTrace_3457036 : CollatzResearch.WordTrace tailWord_3457036 prefixEnd_3457036 1775121107896641564451387 := by
  unfold tailWord_3457036
  simp only [CollatzResearch.WordTrace]
  refine ⟨63044230751878230794295481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84058974335837641059060641 63044230751878230794295481)
  ·
    refine ⟨47283173063908673095721611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63044230751878230794295481 47283173063908673095721611)
    ·
      refine ⟨70924759595863009643582417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47283173063908673095721611 70924759595863009643582417)
      ·
        refine ⟨53193569696897257232686813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70924759595863009643582417 53193569696897257232686813)
        ·
          refine ⟨19947588636336471462257555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53193569696897257232686813 19947588636336471462257555)
          ·
            refine ⟨29921382954504707193386333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19947588636336471462257555 29921382954504707193386333)
            ·
              refine ⟨11220518607939265197519875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29921382954504707193386333 11220518607939265197519875)
              ·
                refine ⟨16830777911908897796279813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11220518607939265197519875 16830777911908897796279813)
                ·
                  refine ⟨3155770858482918336802465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16830777911908897796279813 3155770858482918336802465)
                  ·
                    refine ⟨2366828143862188752601849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3155770858482918336802465 2366828143862188752601849)
                    ·
                      refine ⟨1775121107896641564451387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366828143862188752601849 1775121107896641564451387)
                      ·
                        rfl

theorem cell23_3457036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_3457036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457036 prefixEnd_3457036 := by exact prefixLift 3457036
  have htrace : WordTrace (prefixWord ++ tailWord_3457036) baseStart_3457036 baseEnd_3457036 := by
    simpa [prefixWord, tailWord_3457036, baseEnd_3457036] using wordTrace_append hprefix tailTrace_3457036
  have hstable : (prefixWord ++ tailWord_3457036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457036).length < 2 ^ (prefixWord ++ tailWord_3457036).sum := by decide
  have hdescent : baseEnd_3457036 < baseStart_3457036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457053 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_3457053 : Nat := 118140960795 + 3457053 * 2 ^ 59
def prefixEnd_3457053 : Nat := 4983230072969 + 3 ^ 40 * 3457053 * 2
def baseEnd_3457053 : Nat := 1775129837067767997938809

theorem tailTrace_3457053 : CollatzResearch.WordTrace tailWord_3457053 prefixEnd_3457053 1775129837067767997938809 := by
  unfold tailWord_3457053
  simp only [CollatzResearch.WordTrace]
  refine ⟨126089081544694873491959813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84059387696463248994639875 126089081544694873491959813)
  ·
    refine ⟨23641702789630288779742465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126089081544694873491959813 23641702789630288779742465)
    ·
      refine ⟨17731277092222716584806849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23641702789630288779742465 17731277092222716584806849)
      ·
        refine ⟨13298457819167037438605137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17731277092222716584806849 13298457819167037438605137)
        ·
          refine ⟨9973843364375278078953853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13298457819167037438605137 9973843364375278078953853)
          ·
            refine ⟨3740191261640729279607695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9973843364375278078953853 3740191261640729279607695)
            ·
              refine ⟨5610286892461093919411543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740191261640729279607695 5610286892461093919411543)
              ·
                refine ⟨8415430338691640879117315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610286892461093919411543 8415430338691640879117315)
                ·
                  refine ⟨12623145508037461318675973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415430338691640879117315 12623145508037461318675973)
                  ·
                    refine ⟨2366839782757023997251745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12623145508037461318675973 2366839782757023997251745)
                    ·
                      refine ⟨1775129837067767997938809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366839782757023997251745 1775129837067767997938809)
                      ·
                        rfl

theorem cell23_3457053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_3457053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457053 prefixEnd_3457053 := by exact prefixLift 3457053
  have htrace : WordTrace (prefixWord ++ tailWord_3457053) baseStart_3457053 baseEnd_3457053 := by
    simpa [prefixWord, tailWord_3457053, baseEnd_3457053] using wordTrace_append hprefix tailTrace_3457053
  have hstable : (prefixWord ++ tailWord_3457053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457053).length < 2 ^ (prefixWord ++ tailWord_3457053).sum := by decide
  have hdescent : baseEnd_3457053 < baseStart_3457053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457072 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_3457072 : Nat := 118140960795 + 3457072 * 2 ^ 59
def prefixEnd_3457072 : Nat := 4983230072969 + 3 ^ 40 * 3457072 * 2
def baseEnd_3457072 : Nat := 591713197733401141200407

theorem tailTrace_3457072 : CollatzResearch.WordTrace tailWord_3457072 prefixEnd_3457072 591713197733401141200407 := by
  unfold tailWord_3457072
  simp only [CollatzResearch.WordTrace]
  refine ⟨63044887265813019868450735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84059849687750693157934313 63044887265813019868450735)
  ·
    refine ⟨94567330898719529802676103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63044887265813019868450735 94567330898719529802676103)
    ·
      refine ⟨141850996348079294704014155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94567330898719529802676103 141850996348079294704014155)
      ·
        refine ⟨212776494522118942056021233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141850996348079294704014155 212776494522118942056021233)
        ·
          refine ⟨159582370891589206542015925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212776494522118942056021233 159582370891589206542015925)
          ·
            refine ⟨14960847271086488113313993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159582370891589206542015925 14960847271086488113313993)
            ·
              refine ⟨11220635453314866084985495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14960847271086488113313993 11220635453314866084985495)
              ·
                refine ⟨16830953179972299127478243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11220635453314866084985495 16830953179972299127478243)
                ·
                  refine ⟨25246429769958448691217365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16830953179972299127478243 25246429769958448691217365)
                  ·
                    refine ⟨591713197733401141200407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25246429769958448691217365 591713197733401141200407)
                    ·
                      rfl

theorem cell23_3457072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_3457072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457072 prefixEnd_3457072 := by exact prefixLift 3457072
  have htrace : WordTrace (prefixWord ++ tailWord_3457072) baseStart_3457072 baseEnd_3457072 := by
    simpa [prefixWord, tailWord_3457072, baseEnd_3457072] using wordTrace_append hprefix tailTrace_3457072
  have hstable : (prefixWord ++ tailWord_3457072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457072).length < 2 ^ (prefixWord ++ tailWord_3457072).sum := by decide
  have hdescent : baseEnd_3457072 < baseStart_3457072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457082 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_3457082 : Nat := 118140960795 + 3457082 * 2 ^ 59
def prefixEnd_3457082 : Nat := 4983230072969 + 3 ^ 40 * 3457082 * 2
def baseEnd_3457082 : Nat := 1775144728006748384476175

theorem tailTrace_3457082 : CollatzResearch.WordTrace tailWord_3457082 prefixEnd_3457082 1775144728006748384476175 := by
  unfold tailWord_3457082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31522534815397452861191375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84060092841059874296510333 31522534815397452861191375)
  ·
    refine ⟨47283802223096179291787063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31522534815397452861191375 47283802223096179291787063)
    ·
      refine ⟨70925703334644268937680595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47283802223096179291787063 70925703334644268937680595)
      ·
        refine ⟨106388555001966403406520893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70925703334644268937680595 106388555001966403406520893)
        ·
          refine ⟨39895708125737401277445335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106388555001966403406520893 39895708125737401277445335)
          ·
            refine ⟨59843562188606101916168003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39895708125737401277445335 59843562188606101916168003)
            ·
              refine ⟨89765343282909152874252005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59843562188606101916168003 89765343282909152874252005)
              ·
                refine ⟨16831001865545466163922251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89765343282909152874252005 16831001865545466163922251)
                ·
                  refine ⟨25246502798318199245883377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16831001865545466163922251 25246502798318199245883377)
                  ·
                    refine ⟨18934877098738649434412533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25246502798318199245883377 18934877098738649434412533)
                    ·
                      refine ⟨1775144728006748384476175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18934877098738649434412533 1775144728006748384476175)
                      ·
                        rfl

theorem cell23_3457082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_3457082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457082 prefixEnd_3457082 := by exact prefixLift 3457082
  have htrace : WordTrace (prefixWord ++ tailWord_3457082) baseStart_3457082 baseEnd_3457082 := by
    simpa [prefixWord, tailWord_3457082, baseEnd_3457082] using wordTrace_append hprefix tailTrace_3457082
  have hstable : (prefixWord ++ tailWord_3457082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457082).length < 2 ^ (prefixWord ++ tailWord_3457082).sum := by decide
  have hdescent : baseEnd_3457082 < baseStart_3457082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457089 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3457089 : Nat := 118140960795 + 3457089 * 2 ^ 59
def prefixEnd_3457089 : Nat := 4983230072969 + 3 ^ 40 * 3457089 * 2
def baseEnd_3457089 : Nat := 591716107457109952362881

theorem tailTrace_3457089 : CollatzResearch.WordTrace tailWord_3457089 prefixEnd_3457089 591716107457109952362881 := by
  unfold tailWord_3457089
  simp only [CollatzResearch.WordTrace]
  refine ⟨126090394572564451640270321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84060263048376301093513547 126090394572564451640270321)
  ·
    refine ⟨94567795929423338730202741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126090394572564451640270321 94567795929423338730202741)
    ·
      refine ⟨8865730868383438005956507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94567795929423338730202741 8865730868383438005956507)
      ·
        refine ⟨13298596302575157008934761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865730868383438005956507 13298596302575157008934761)
        ·
          refine ⟨9973947226931367756701071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13298596302575157008934761 9973947226931367756701071)
          ·
            refine ⟨14960920840397051635051607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9973947226931367756701071 14960920840397051635051607)
            ·
              refine ⟨22441381260595577452577411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14960920840397051635051607 22441381260595577452577411)
              ·
                refine ⟨33662071890893366178866117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22441381260595577452577411 33662071890893366178866117)
                ·
                  refine ⟨6311638479542506158537397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33662071890893366178866117 6311638479542506158537397)
                  ·
                    refine ⟨591716107457109952362881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6311638479542506158537397 591716107457109952362881)
                    ·
                      rfl

theorem cell23_3457089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3457089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457089 prefixEnd_3457089 := by exact prefixLift 3457089
  have htrace : WordTrace (prefixWord ++ tailWord_3457089) baseStart_3457089 baseEnd_3457089 := by
    simpa [prefixWord, tailWord_3457089, baseEnd_3457089] using wordTrace_append hprefix tailTrace_3457089
  have hstable : (prefixWord ++ tailWord_3457089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457089).length < 2 ^ (prefixWord ++ tailWord_3457089).sum := by decide
  have hdescent : baseEnd_3457089 < baseStart_3457089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457149 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 6]
def baseStart_3457149 : Nat := 118140960795 + 3457149 * 2 ^ 59
def prefixEnd_3457149 : Nat := 4983230072969 + 3 ^ 40 * 3457149 * 2
def baseEnd_3457149 : Nat := 197242125690066624704263

theorem tailTrace_3457149 : CollatzResearch.WordTrace tailWord_3457149 prefixEnd_3457149 197242125690066624704263 := by
  unfold tailWord_3457149
  simp only [CollatzResearch.WordTrace]
  refine ⟨126092582952347081887454501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84061721968231387924969667 126092582952347081887454501)
  ·
    refine ⟨23642359303565077853897719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126092582952347081887454501 23642359303565077853897719)
    ·
      refine ⟨35463538955347616780846579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23642359303565077853897719 35463538955347616780846579)
      ·
        refine ⟨53195308433021425171269869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35463538955347616780846579 53195308433021425171269869)
        ·
          refine ⟨19948240662383034439226201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53195308433021425171269869 19948240662383034439226201)
          ·
            refine ⟨14961180496787275829419651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19948240662383034439226201 14961180496787275829419651)
            ·
              refine ⟨22441770745180913744129477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14961180496787275829419651 22441770745180913744129477)
              ·
                refine ⟨4207832014721421327024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22441770745180913744129477 4207832014721421327024277)
                ·
                  refine ⟨197242125690066624704263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4207832014721421327024277 197242125690066624704263)
                  ·
                    rfl

theorem cell23_3457149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_3457149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457149 prefixEnd_3457149 := by exact prefixLift 3457149
  have htrace : WordTrace (prefixWord ++ tailWord_3457149) baseStart_3457149 baseEnd_3457149 := by
    simpa [prefixWord, tailWord_3457149, baseEnd_3457149] using wordTrace_append hprefix tailTrace_3457149
  have hstable : (prefixWord ++ tailWord_3457149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457149).length < 2 ^ (prefixWord ++ tailWord_3457149).sum := by decide
  have hdescent : baseEnd_3457149 < baseStart_3457149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457152 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_3457152 : Nat := 118140960795 + 3457152 * 2 ^ 59
def prefixEnd_3457152 : Nat := 4983230072969 + 3 ^ 40 * 3457152 * 2
def baseEnd_3457152 : Nat := 1775180671652563110600853

theorem tailTrace_3457152 : CollatzResearch.WordTrace tailWord_3457152 prefixEnd_3457152 1775180671652563110600853 := by
  unfold tailWord_3457152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63046346185668106699906855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84061794914224142266542473 63046346185668106699906855)
  ·
    refine ⟨94569519278502160049860283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63046346185668106699906855 94569519278502160049860283)
    ·
      refine ⟨141854278917753240074790425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94569519278502160049860283 141854278917753240074790425)
      ·
        refine ⟨106390709188314930056092819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141854278917753240074790425 106390709188314930056092819)
        ·
          refine ⟨159586063782472395084139229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106390709188314930056092819 159586063782472395084139229)
          ·
            refine ⟨59844773918427148156552211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159586063782472395084139229 59844773918427148156552211)
            ·
              refine ⟨89767160877640722234828317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59844773918427148156552211 89767160877640722234828317)
              ·
                refine ⟨33662685329115270838060619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89767160877640722234828317 33662685329115270838060619)
                ·
                  refine ⟨50494027993672906257090929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33662685329115270838060619 50494027993672906257090929)
                  ·
                    refine ⟨37870520995254679692818197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50494027993672906257090929 37870520995254679692818197)
                    ·
                      refine ⟨1775180671652563110600853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37870520995254679692818197 1775180671652563110600853)
                      ·
                        rfl

theorem cell23_3457152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_3457152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457152 prefixEnd_3457152 := by exact prefixLift 3457152
  have htrace : WordTrace (prefixWord ++ tailWord_3457152) baseStart_3457152 baseEnd_3457152 := by
    simpa [prefixWord, tailWord_3457152, baseEnd_3457152] using wordTrace_append hprefix tailTrace_3457152
  have hstable : (prefixWord ++ tailWord_3457152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457152).length < 2 ^ (prefixWord ++ tailWord_3457152).sum := by decide
  have hdescent : baseEnd_3457152 < baseStart_3457152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457174 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3457174 : Nat := 118140960795 + 3457174 * 2 ^ 59
def prefixEnd_3457174 : Nat := 4983230072969 + 3 ^ 40 * 3457174 * 2
def baseEnd_3457174 : Nat := 591730656075654008175251

theorem tailTrace_3457174 : CollatzResearch.WordTrace tailWord_3457174 prefixEnd_3457174 591730656075654008175251 := by
  unfold tailWord_3457174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880843423578531947319661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84062329851504340771409717 7880843423578531947319661)
  ·
    refine ⟨2955316283841949480244873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7880843423578531947319661 2955316283841949480244873)
    ·
      refine ⟨2216487212881462110183655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2955316283841949480244873 2216487212881462110183655)
      ·
        refine ⟨3324730819322193165275483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216487212881462110183655 3324730819322193165275483)
        ·
          refine ⟨4987096228983289747913225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324730819322193165275483 4987096228983289747913225)
          ·
            refine ⟨3740322171737467310934919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987096228983289747913225 3740322171737467310934919)
            ·
              refine ⟨5610483257606200966402379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740322171737467310934919 5610483257606200966402379)
              ·
                refine ⟨8415724886409301449603569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610483257606200966402379 8415724886409301449603569)
                ·
                  refine ⟨6311793664806976087202677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8415724886409301449603569 6311793664806976087202677)
                  ·
                    refine ⟨591730656075654008175251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6311793664806976087202677 591730656075654008175251)
                    ·
                      rfl

theorem cell23_3457174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3457174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457174 prefixEnd_3457174 := by exact prefixLift 3457174
  have htrace : WordTrace (prefixWord ++ tailWord_3457174) baseStart_3457174 baseEnd_3457174 := by
    simpa [prefixWord, tailWord_3457174, baseEnd_3457174] using wordTrace_append hprefix tailTrace_3457174
  have hstable : (prefixWord ++ tailWord_3457174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457174).length < 2 ^ (prefixWord ++ tailWord_3457174).sum := by decide
  have hdescent : baseEnd_3457174 < baseStart_3457174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457233 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 3, 2, 2]
def baseStart_3457233 : Nat := 118140960795 + 3457233 * 2 ^ 59
def prefixEnd_3457233 : Nat := 4983230072969 + 3 ^ 40 * 3457233 * 2
def baseEnd_3457233 : Nat := 1775222263585577293687981

theorem tailTrace_3457233 : CollatzResearch.WordTrace tailWord_3457233 prefixEnd_3457233 1775222263585577293687981 := by
  unfold tailWord_3457233
  simp only [CollatzResearch.WordTrace]
  refine ⟨126095646684042764233512353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84063764456028509489008235 126095646684042764233512353)
  ·
    refine ⟨94571735013032073175134265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126095646684042764233512353 94571735013032073175134265)
    ·
      refine ⟨70928801259774054881350699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94571735013032073175134265 70928801259774054881350699)
      ·
        refine ⟨106393201889661082322026049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70928801259774054881350699 106393201889661082322026049)
        ·
          refine ⟨79794901417245811741519537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106393201889661082322026049 79794901417245811741519537)
          ·
            refine ⟨59846176062934358806139653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79794901417245811741519537 59846176062934358806139653)
            ·
              refine ⟨11221158011800192276151185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59846176062934358806139653 11221158011800192276151185)
              ·
                refine ⟨8415868508850144207113389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11221158011800192276151185 8415868508850144207113389)
                ·
                  refine ⟨3155950690818804077667521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8415868508850144207113389 3155950690818804077667521)
                  ·
                    refine ⟨2366963018114103058250641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3155950690818804077667521 2366963018114103058250641)
                    ·
                      refine ⟨1775222263585577293687981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366963018114103058250641 1775222263585577293687981)
                      ·
                        rfl

theorem cell23_3457233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_3457233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457233 prefixEnd_3457233 := by exact prefixLift 3457233
  have htrace : WordTrace (prefixWord ++ tailWord_3457233) baseStart_3457233 baseEnd_3457233 := by
    simpa [prefixWord, tailWord_3457233, baseEnd_3457233] using wordTrace_append hprefix tailTrace_3457233
  have hstable : (prefixWord ++ tailWord_3457233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457233).length < 2 ^ (prefixWord ++ tailWord_3457233).sum := by decide
  have hdescent : baseEnd_3457233 < baseStart_3457233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457253 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3457253 : Nat := 118140960795 + 3457253 * 2 ^ 59
def prefixEnd_3457253 : Nat := 4983230072969 + 3 ^ 40 * 3457253 * 2
def baseEnd_3457253 : Nat := 1775232533198667215437889

theorem tailTrace_3457253 : CollatzResearch.WordTrace tailWord_3457253 prefixEnd_3457253 1775232533198667215437889 := by
  unfold tailWord_3457253
  simp only [CollatzResearch.WordTrace]
  refine ⟨126096376143970307649240413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84064250762646871766160275 126096376143970307649240413)
  ·
    refine ⟨47286141053988865368465155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126096376143970307649240413 47286141053988865368465155)
    ·
      refine ⟨70929211580983298052697733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47286141053988865368465155 70929211580983298052697733)
      ·
        refine ⟨13299227171434368384880825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70929211580983298052697733 13299227171434368384880825)
        ·
          refine ⟨9974420378575776288660619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13299227171434368384880825 9974420378575776288660619)
          ·
            refine ⟨14961630567863664432990929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9974420378575776288660619 14961630567863664432990929)
            ·
              refine ⟨11221222925897748324743197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14961630567863664432990929 11221222925897748324743197)
              ·
                refine ⟨4207958597211655621778699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11221222925897748324743197 4207958597211655621778699)
                ·
                  refine ⟨6311937895817483432668049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207958597211655621778699 6311937895817483432668049)
                  ·
                    refine ⟨4733953421863112574501037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6311937895817483432668049 4733953421863112574501037)
                    ·
                      refine ⟨1775232533198667215437889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4733953421863112574501037 1775232533198667215437889)
                      ·
                        rfl

theorem cell23_3457253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3457253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457253 prefixEnd_3457253 := by exact prefixLift 3457253
  have htrace : WordTrace (prefixWord ++ tailWord_3457253) baseStart_3457253 baseEnd_3457253 := by
    simpa [prefixWord, tailWord_3457253, baseEnd_3457253] using wordTrace_append hprefix tailTrace_3457253
  have hstable : (prefixWord ++ tailWord_3457253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457253).length < 2 ^ (prefixWord ++ tailWord_3457253).sum := by decide
  have hdescent : baseEnd_3457253 < baseStart_3457253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457267 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 1, 2, 2]
def baseStart_3457267 : Nat := 118140960795 + 3457267 * 2 ^ 59
def prefixEnd_3457267 : Nat := 4983230072969 + 3 ^ 40 * 3457267 * 2
def baseEnd_3457267 : Nat := 1775239721927830160662825

theorem tailTrace_3457267 : CollatzResearch.WordTrace tailWord_3457267 prefixEnd_3457267 1775239721927830160662825 := by
  unfold tailWord_3457267
  simp only [CollatzResearch.WordTrace]
  refine ⟨126096886765919588040250055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84064591177279725360166703 126096886765919588040250055)
  ·
    refine ⟨189145330148879382060375083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126096886765919588040250055 189145330148879382060375083)
    ·
      refine ⟨283717995223319073090562625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189145330148879382060375083 283717995223319073090562625)
      ·
        refine ⟨212788496417489304817921969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283717995223319073090562625 212788496417489304817921969)
        ·
          refine ⟨159591372313116978613441477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212788496417489304817921969 159591372313116978613441477)
          ·
            refine ⟨29923382308709433490020277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159591372313116978613441477 29923382308709433490020277)
            ·
              refine ⟨2805317091441509389689401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29923382308709433490020277 2805317091441509389689401)
              ·
                refine ⟨2103987818581132042267051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805317091441509389689401 2103987818581132042267051)
                ·
                  refine ⟨3155981727871698063400577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103987818581132042267051 3155981727871698063400577)
                  ·
                    refine ⟨2366986295903773547550433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3155981727871698063400577 2366986295903773547550433)
                    ·
                      refine ⟨1775239721927830160662825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2366986295903773547550433 1775239721927830160662825)
                      ·
                        rfl

theorem cell23_3457267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 2, 2].length) (baseStart_3457267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457267 prefixEnd_3457267 := by exact prefixLift 3457267
  have htrace : WordTrace (prefixWord ++ tailWord_3457267) baseStart_3457267 baseEnd_3457267 := by
    simpa [prefixWord, tailWord_3457267, baseEnd_3457267] using wordTrace_append hprefix tailTrace_3457267
  have hstable : (prefixWord ++ tailWord_3457267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457267).length < 2 ^ (prefixWord ++ tailWord_3457267).sum := by decide
  have hdescent : baseEnd_3457267 < baseStart_3457267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457283 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 3]
def baseStart_3457283 : Nat := 118140960795 + 3457283 * 2 ^ 59
def prefixEnd_3457283 : Nat := 4983230072969 + 3 ^ 40 * 3457283 * 2
def baseEnd_3457283 : Nat := 1775247937618302098062751

theorem tailTrace_3457283 : CollatzResearch.WordTrace tailWord_3457283 prefixEnd_3457283 1775247937618302098062751 := by
  unfold tailWord_3457283
  simp only [CollatzResearch.WordTrace]
  refine ⟨126097470333861622772832503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84064980222574415181888335 126097470333861622772832503)
  ·
    refine ⟨189146205500792434159248755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126097470333861622772832503 189146205500792434159248755)
    ·
      refine ⟨283719308251188651238873133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189146205500792434159248755 283719308251188651238873133)
      ·
        refine ⟨106394740594195744214577425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283719308251188651238873133 106394740594195744214577425)
        ·
          refine ⟨79796055445646808160933069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106394740594195744214577425 79796055445646808160933069)
          ·
            refine ⟨29923520792117553060349901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79796055445646808160933069 29923520792117553060349901)
            ·
              refine ⟨11221320297044082397631213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29923520792117553060349901 11221320297044082397631213)
              ·
                refine ⟨4207995111391530899111705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11221320297044082397631213 4207995111391530899111705)
                ·
                  refine ⟨3155996333543648174333779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207995111391530899111705 3155996333543648174333779)
                  ·
                    refine ⟨4733994500315472261500669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155996333543648174333779 4733994500315472261500669)
                    ·
                      refine ⟨1775247937618302098062751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4733994500315472261500669 1775247937618302098062751)
                      ·
                        rfl

theorem cell23_3457283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_3457283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457283 prefixEnd_3457283 := by exact prefixLift 3457283
  have htrace : WordTrace (prefixWord ++ tailWord_3457283) baseStart_3457283 baseEnd_3457283 := by
    simpa [prefixWord, tailWord_3457283, baseEnd_3457283] using wordTrace_append hprefix tailTrace_3457283
  have hstable : (prefixWord ++ tailWord_3457283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457283).length < 2 ^ (prefixWord ++ tailWord_3457283).sum := by decide
  have hdescent : baseEnd_3457283 < baseStart_3457283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457287 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3457287 : Nat := 118140960795 + 3457287 * 2 ^ 59
def prefixEnd_3457287 : Nat := 4983230072969 + 3 ^ 40 * 3457287 * 2
def baseEnd_3457287 : Nat := 1775249991540920082412733

theorem tailTrace_3457287 : CollatzResearch.WordTrace tailWord_3457287 prefixEnd_3457287 1775249991540920082412733 := by
  unfold tailWord_3457287
  simp only [CollatzResearch.WordTrace]
  refine ⟨126097616225847131455978115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84065077483898087637318743 126097616225847131455978115)
  ·
    refine ⟨189146424338770697183967173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126097616225847131455978115 189146424338770697183967173)
    ·
      refine ⟨35464954563519505721993845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189146424338770697183967173 35464954563519505721993845)
      ·
        refine ⟨3324839490329953661436923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35464954563519505721993845 3324839490329953661436923)
        ·
          refine ⟨4987259235494930492155385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324839490329953661436923 4987259235494930492155385)
          ·
            refine ⟨3740444426621197869116539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987259235494930492155385 3740444426621197869116539)
            ·
              refine ⟨5610666639931796803674809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740444426621197869116539 5610666639931796803674809)
              ·
                refine ⟨4207999979948847602756107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5610666639931796803674809 4207999979948847602756107)
                ·
                  refine ⟨6311999969923271404134161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207999979948847602756107 6311999969923271404134161)
                  ·
                    refine ⟨4733999977442453553100621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6311999969923271404134161 4733999977442453553100621)
                    ·
                      refine ⟨1775249991540920082412733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4733999977442453553100621 1775249991540920082412733)
                      ·
                        rfl

theorem cell23_3457287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3457287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457287 prefixEnd_3457287 := by exact prefixLift 3457287
  have htrace : WordTrace (prefixWord ++ tailWord_3457287) baseStart_3457287 baseEnd_3457287 := by
    simpa [prefixWord, tailWord_3457287, baseEnd_3457287] using wordTrace_append hprefix tailTrace_3457287
  have hstable : (prefixWord ++ tailWord_3457287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457287).length < 2 ^ (prefixWord ++ tailWord_3457287).sum := by decide
  have hdescent : baseEnd_3457287 < baseStart_3457287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457340 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_3457340 : Nat := 118140960795 + 3457340 * 2 ^ 59
def prefixEnd_3457340 : Nat := 4983230072969 + 3 ^ 40 * 3457340 * 2
def baseEnd_3457340 : Nat := 1775277206015608375049989

theorem tailTrace_3457340 : CollatzResearch.WordTrace tailWord_3457340 prefixEnd_3457340 1775277206015608375049989 := by
  unfold tailWord_3457340
  simp only [CollatzResearch.WordTrace]
  refine ⟨63049774647327560753828737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84066366196436747671771649 63049774647327560753828737)
  ·
    refine ⟨47287330985495670565371553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63049774647327560753828737 47287330985495670565371553)
    ·
      refine ⟨35465498239121752924028665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47287330985495670565371553 35465498239121752924028665)
      ·
        refine ⟨26599123679341314693021499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35465498239121752924028665 26599123679341314693021499)
        ·
          refine ⟨39898685519011972039532249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26599123679341314693021499 39898685519011972039532249)
          ·
            refine ⟨29924014139258979029649187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39898685519011972039532249 29924014139258979029649187)
            ·
              refine ⟨44886021208888468544473781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29924014139258979029649187 44886021208888468544473781)
              ·
                refine ⟨4208064488333293926044417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44886021208888468544473781 4208064488333293926044417)
                ·
                  refine ⟨3156048366249970444533313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208064488333293926044417 3156048366249970444533313)
                  ·
                    refine ⟨2367036274687477833399985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3156048366249970444533313 2367036274687477833399985)
                    ·
                      refine ⟨1775277206015608375049989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367036274687477833399985 1775277206015608375049989)
                      ·
                        rfl

theorem cell23_3457340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_3457340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457340 prefixEnd_3457340 := by exact prefixLift 3457340
  have htrace : WordTrace (prefixWord ++ tailWord_3457340) baseStart_3457340 baseEnd_3457340 := by
    simpa [prefixWord, tailWord_3457340, baseEnd_3457340] using wordTrace_append hprefix tailTrace_3457340
  have hstable : (prefixWord ++ tailWord_3457340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457340).length < 2 ^ (prefixWord ++ tailWord_3457340).sum := by decide
  have hdescent : baseEnd_3457340 < baseStart_3457340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457356 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3457356 : Nat := 118140960795 + 3457356 * 2 ^ 59
def prefixEnd_3457356 : Nat := 4983230072969 + 3 ^ 40 * 3457356 * 2
def baseEnd_3457356 : Nat := 1775285421706080312449915

theorem tailTrace_3457356 : CollatzResearch.WordTrace tailWord_3457356 prefixEnd_3457356 1775285421706080312449915 := by
  unfold tailWord_3457356
  simp only [CollatzResearch.WordTrace]
  refine ⟨63050066431298578120119961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84066755241731437493493281 63050066431298578120119961)
  ·
    refine ⟨47287549823473933590089971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63050066431298578120119961 47287549823473933590089971)
    ·
      refine ⟨70931324735210900385134957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47287549823473933590089971 70931324735210900385134957)
      ·
        refine ⟨26599246775704087644425609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70931324735210900385134957 26599246775704087644425609)
        ·
          refine ⟨19949435081778065733319207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26599246775704087644425609 19949435081778065733319207)
          ·
            refine ⟨29924152622667098599978811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19949435081778065733319207 29924152622667098599978811)
            ·
              refine ⟨44886228934000647899968217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29924152622667098599978811 44886228934000647899968217)
              ·
                refine ⟨33664671700500485924976163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44886228934000647899968217 33664671700500485924976163)
                ·
                  refine ⟨50497007550750728887464245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33664671700500485924976163 50497007550750728887464245)
                  ·
                    refine ⟨4734094457882880833199773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50497007550750728887464245 4734094457882880833199773)
                    ·
                      refine ⟨1775285421706080312449915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734094457882880833199773 1775285421706080312449915)
                      ·
                        rfl

theorem cell23_3457356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3457356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457356 prefixEnd_3457356 := by exact prefixLift 3457356
  have htrace : WordTrace (prefixWord ++ tailWord_3457356) baseStart_3457356 baseEnd_3457356 := by
    simpa [prefixWord, tailWord_3457356, baseEnd_3457356] using wordTrace_append hprefix tailTrace_3457356
  have hstable : (prefixWord ++ tailWord_3457356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457356).length < 2 ^ (prefixWord ++ tailWord_3457356).sum := by decide
  have hdescent : baseEnd_3457356 < baseStart_3457356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457433 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_3457433 : Nat := 118140960795 + 3457433 * 2 ^ 59
def prefixEnd_3457433 : Nat := 4983230072969 + 3 ^ 40 * 3457433 * 2
def baseEnd_3457433 : Nat := 1775324959716476511187061

theorem tailTrace_3457433 : CollatzResearch.WordTrace tailWord_3457433 prefixEnd_3457433 1775324959716476511187061 := by
  unfold tailWord_3457433
  simp only [CollatzResearch.WordTrace]
  refine ⟨126102941283318198390792953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84068627522212132260528635 126102941283318198390792953)
  ·
    refine ⟨94577205962488648793094715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126102941283318198390792953 94577205962488648793094715)
    ·
      refine ⟨141865808943732973189642073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94577205962488648793094715 141865808943732973189642073)
      ·
        refine ⟨106399356707799729892231555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141865808943732973189642073 106399356707799729892231555)
        ·
          refine ⟨159599035061699594838347333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106399356707799729892231555 159599035061699594838347333)
          ·
            refine ⟨29924819074068674032190125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159599035061699594838347333 29924819074068674032190125)
            ·
              refine ⟨11221807152775752762071297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29924819074068674032190125 11221807152775752762071297)
              ·
                refine ⟨8416355364581814571553473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11221807152775752762071297 8416355364581814571553473)
                ·
                  refine ⟨6312266523436360928665105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8416355364581814571553473 6312266523436360928665105)
                  ·
                    refine ⟨4734199892577270696498829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312266523436360928665105 4734199892577270696498829)
                    ·
                      refine ⟨1775324959716476511187061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734199892577270696498829 1775324959716476511187061)
                      ·
                        rfl

theorem cell23_3457433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_3457433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457433 prefixEnd_3457433 := by exact prefixLift 3457433
  have htrace : WordTrace (prefixWord ++ tailWord_3457433) baseStart_3457433 baseEnd_3457433 := by
    simpa [prefixWord, tailWord_3457433, baseEnd_3457433] using wordTrace_append hprefix tailTrace_3457433
  have hstable : (prefixWord ++ tailWord_3457433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457433).length < 2 ^ (prefixWord ++ tailWord_3457433).sum := by decide
  have hdescent : baseEnd_3457433 < baseStart_3457433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457440 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 3, 4]
def baseStart_3457440 : Nat := 118140960795 + 3457440 * 2 ^ 59
def prefixEnd_3457440 : Nat := 4983230072969 + 3 ^ 40 * 3457440 * 2
def baseEnd_3457440 : Nat := 591776184693685994599843

theorem tailTrace_3457440 : CollatzResearch.WordTrace tailWord_3457440 prefixEnd_3457440 591776184693685994599843 := by
  unfold tailWord_3457440
  simp only [CollatzResearch.WordTrace]
  refine ⟨63051598297146419293148887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84068797729528559057531849 63051598297146419293148887)
  ·
    refine ⟨94577397445719628939723331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63051598297146419293148887 94577397445719628939723331)
    ·
      refine ⟨141866096168579443409584997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94577397445719628939723331 141866096168579443409584997)
      ·
        refine ⟨26599893031608645639297187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141866096168579443409584997 26599893031608645639297187)
        ·
          refine ⟨39899839547412968458945781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26599893031608645639297187 39899839547412968458945781)
          ·
            refine ⟨3740609957569965793026167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39899839547412968458945781 3740609957569965793026167)
            ·
              refine ⟨5610914936354948689539251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740609957569965793026167 5610914936354948689539251)
              ·
                refine ⟨8416372404532423034308877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610914936354948689539251 8416372404532423034308877)
                ·
                  refine ⟨3156139651699658637865829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8416372404532423034308877 3156139651699658637865829)
                  ·
                    refine ⟨591776184693685994599843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3156139651699658637865829 591776184693685994599843)
                    ·
                      rfl

theorem cell23_3457440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_3457440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457440 prefixEnd_3457440 := by exact prefixLift 3457440
  have htrace : WordTrace (prefixWord ++ tailWord_3457440) baseStart_3457440 baseEnd_3457440 := by
    simpa [prefixWord, tailWord_3457440, baseEnd_3457440] using wordTrace_append hprefix tailTrace_3457440
  have hstable : (prefixWord ++ tailWord_3457440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457440).length < 2 ^ (prefixWord ++ tailWord_3457440).sum := by decide
  have hdescent : baseEnd_3457440 < baseStart_3457440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457496 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_3457496 : Nat := 118140960795 + 3457496 * 2 ^ 59
def prefixEnd_3457496 : Nat := 4983230072969 + 3 ^ 40 * 3457496 * 2
def baseEnd_3457496 : Nat := 591785769665903254899757

theorem tailTrace_3457496 : CollatzResearch.WordTrace tailWord_3457496 prefixEnd_3457496 591785769665903254899757 := by
  unfold tailWord_3457496
  simp only [CollatzResearch.WordTrace]
  refine ⟨63052619541044980075168171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84070159388059973433557561 63052619541044980075168171)
  ·
    refine ⟨94578929311567470112752257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63052619541044980075168171 94578929311567470112752257)
    ·
      refine ⟨70934196983675602584564193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94578929311567470112752257 70934196983675602584564193)
      ·
        refine ⟨53200647737756701938423145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70934196983675602584564193 53200647737756701938423145)
        ·
          refine ⟨39900485803317526453817359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53200647737756701938423145 39900485803317526453817359)
          ·
            refine ⟨59850728704976289680726039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39900485803317526453817359 59850728704976289680726039)
            ·
              refine ⟨89776093057464434521089059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59850728704976289680726039 89776093057464434521089059)
              ·
                refine ⟨134664139586196651781633589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89776093057464434521089059 134664139586196651781633589)
                ·
                  refine ⟨12624763086205936104528149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134664139586196651781633589 12624763086205936104528149)
                  ·
                    refine ⟨591785769665903254899757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12624763086205936104528149 591785769665903254899757)
                    ·
                      rfl

theorem cell23_3457496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_3457496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457496 prefixEnd_3457496 := by exact prefixLift 3457496
  have htrace : WordTrace (prefixWord ++ tailWord_3457496) baseStart_3457496 baseEnd_3457496 := by
    simpa [prefixWord, tailWord_3457496, baseEnd_3457496] using wordTrace_append hprefix tailTrace_3457496
  have hstable : (prefixWord ++ tailWord_3457496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457496).length < 2 ^ (prefixWord ++ tailWord_3457496).sum := by decide
  have hdescent : baseEnd_3457496 < baseStart_3457496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457497 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 1, 1, 3]
def baseStart_3457497 : Nat := 118140960795 + 3457497 * 2 ^ 59
def prefixEnd_3457497 : Nat := 4983230072969 + 3 ^ 40 * 3457497 * 2
def baseEnd_3457497 : Nat := 1775357822478364260786767

theorem tailTrace_3457497 : CollatzResearch.WordTrace tailWord_3457497 prefixEnd_3457497 1775357822478364260786767 := by
  unfold tailWord_3457497
  simp only [CollatzResearch.WordTrace]
  refine ⟨126105275555086337321122745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84070183703390891547415163 126105275555086337321122745)
  ·
    refine ⟨94578956666314752990842059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126105275555086337321122745 94578956666314752990842059)
    ·
      refine ⟨141868434999472129486263089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94578956666314752990842059 141868434999472129486263089)
      ·
        refine ⟨106401326249604097114697317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141868434999472129486263089 106401326249604097114697317)
        ·
          refine ⟨19950248671800768209005747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106401326249604097114697317 19950248671800768209005747)
          ·
            refine ⟨29925373007701152313508621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19950248671800768209005747 29925373007701152313508621)
            ·
              refine ⟨11222014877887932117565733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29925373007701152313508621 11222014877887932117565733)
              ·
                refine ⟨2104127789603987272043575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11222014877887932117565733 2104127789603987272043575)
                ·
                  refine ⟨3156191684405980908065363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104127789603987272043575 3156191684405980908065363)
                  ·
                    refine ⟨4734287526608971362098045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156191684405980908065363 4734287526608971362098045)
                    ·
                      refine ⟨1775357822478364260786767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734287526608971362098045 1775357822478364260786767)
                      ·
                        rfl

theorem cell23_3457497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_3457497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457497 prefixEnd_3457497 := by exact prefixLift 3457497
  have htrace : WordTrace (prefixWord ++ tailWord_3457497) baseStart_3457497 baseEnd_3457497 := by
    simpa [prefixWord, tailWord_3457497, baseEnd_3457497] using wordTrace_append hprefix tailTrace_3457497
  have hstable : (prefixWord ++ tailWord_3457497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457497).length < 2 ^ (prefixWord ++ tailWord_3457497).sum := by decide
  have hdescent : baseEnd_3457497 < baseStart_3457497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457503 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_3457503 : Nat := 118140960795 + 3457503 * 2 ^ 59
def prefixEnd_3457503 : Nat := 4983230072969 + 3 ^ 40 * 3457503 * 2
def baseEnd_3457503 : Nat := 1775360903362291237311739

theorem tailTrace_3457503 : CollatzResearch.WordTrace tailWord_3457503 prefixEnd_3457503 1775360903362291237311739 := by
  unfold tailWord_3457503
  simp only [CollatzResearch.WordTrace]
  refine ⟨126105494393064600345841163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84070329595376400230560775 126105494393064600345841163)
  ·
    refine ⟨189158241589596900518761745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126105494393064600345841163 189158241589596900518761745)
    ·
      refine ⟨141868681192197675389071309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189158241589596900518761745 141868681192197675389071309)
      ·
        refine ⟨53200755447074128270901741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141868681192197675389071309 53200755447074128270901741)
        ·
          refine ⟨19950283292652798101588153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53200755447074128270901741 19950283292652798101588153)
          ·
            refine ⟨14962712469489598576191115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19950283292652798101588153 14962712469489598576191115)
            ·
              refine ⟨22444068704234397864286673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14962712469489598576191115 22444068704234397864286673)
              ·
                refine ⟨16833051528175798398215005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22444068704234397864286673 16833051528175798398215005)
                ·
                  refine ⟨6312394323065924399330627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16833051528175798398215005 6312394323065924399330627)
                  ·
                    refine ⟨9468591484598886598995941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6312394323065924399330627 9468591484598886598995941)
                    ·
                      refine ⟨1775360903362291237311739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9468591484598886598995941 1775360903362291237311739)
                      ·
                        rfl

theorem cell23_3457503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_3457503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457503 prefixEnd_3457503 := by exact prefixLift 3457503
  have htrace : WordTrace (prefixWord ++ tailWord_3457503) baseStart_3457503 baseEnd_3457503 := by
    simpa [prefixWord, tailWord_3457503, baseEnd_3457503] using wordTrace_append hprefix tailTrace_3457503
  have hstable : (prefixWord ++ tailWord_3457503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457503).length < 2 ^ (prefixWord ++ tailWord_3457503).sum := by decide
  have hdescent : baseEnd_3457503 < baseStart_3457503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457523 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 3]
def baseStart_3457523 : Nat := 118140960795 + 3457523 * 2 ^ 59
def prefixEnd_3457523 : Nat := 4983230072969 + 3 ^ 40 * 3457523 * 2
def baseEnd_3457523 : Nat := 1775371172975381159061647

theorem tailTrace_3457523 : CollatzResearch.WordTrace tailWord_3457523 prefixEnd_3457523 1775371172975381159061647 := by
  unfold tailWord_3457523
  simp only [CollatzResearch.WordTrace]
  refine ⟨126106223852992143761569223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84070815901994762507712815 126106223852992143761569223)
  ·
    refine ⟨189159335779488215642353835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126106223852992143761569223 189159335779488215642353835)
    ·
      refine ⟨283739003669232323463530753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189159335779488215642353835 283739003669232323463530753)
      ·
        refine ⟨212804252751924242597648065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283739003669232323463530753 212804252751924242597648065)
        ·
          refine ⟨159603189563943181948236049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212804252751924242597648065 159603189563943181948236049)
          ·
            refine ⟨119702392172957386461177037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159603189563943181948236049 119702392172957386461177037)
            ·
              refine ⟨44888397064859019922941389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119702392172957386461177037 44888397064859019922941389)
              ·
                refine ⟨16833148899322132471103021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44888397064859019922941389 16833148899322132471103021)
                ·
                  refine ⟨6312430837245799676663633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16833148899322132471103021 6312430837245799676663633)
                  ·
                    refine ⟨4734323127934349757497725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312430837245799676663633 4734323127934349757497725)
                    ·
                      refine ⟨1775371172975381159061647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734323127934349757497725 1775371172975381159061647)
                      ·
                        rfl

theorem cell23_3457523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_3457523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457523 prefixEnd_3457523 := by exact prefixLift 3457523
  have htrace : WordTrace (prefixWord ++ tailWord_3457523) baseStart_3457523 baseEnd_3457523 := by
    simpa [prefixWord, tailWord_3457523, baseEnd_3457523] using wordTrace_append hprefix tailTrace_3457523
  have hstable : (prefixWord ++ tailWord_3457523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457523).length < 2 ^ (prefixWord ++ tailWord_3457523).sum := by decide
  have hdescent : baseEnd_3457523 < baseStart_3457523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457533 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_3457533 : Nat := 118140960795 + 3457533 * 2 ^ 59
def prefixEnd_3457533 : Nat := 4983230072969 + 3 ^ 40 * 3457533 * 2
def baseEnd_3457533 : Nat := 1775376307781926119936601

theorem tailTrace_3457533 : CollatzResearch.WordTrace tailWord_3457533 prefixEnd_3457533 1775376307781926119936601 := by
  unfold tailWord_3457533
  simp only [CollatzResearch.WordTrace]
  refine ⟨126106588582955915469433253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84071059055303943646288835 126106588582955915469433253)
  ·
    refine ⟨23644985359304234150518735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126106588582955915469433253 23644985359304234150518735)
    ·
      refine ⟨35467478038956351225778103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23644985359304234150518735 35467478038956351225778103)
      ·
        refine ⟨53201217058434526838667155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35467478038956351225778103 53201217058434526838667155)
        ·
          refine ⟨79801825587651790258000733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53201217058434526838667155 79801825587651790258000733)
          ·
            refine ⟨29925684595369421346750275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79801825587651790258000733 29925684595369421346750275)
            ·
              refine ⟨44888526893054132020125413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29925684595369421346750275 44888526893054132020125413)
              ·
                refine ⟨8416598792447649753773515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44888526893054132020125413 8416598792447649753773515)
                ·
                  refine ⟨12624898188671474630660273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8416598792447649753773515 12624898188671474630660273)
                  ·
                    refine ⟨9468673641503605972995205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12624898188671474630660273 9468673641503605972995205)
                    ·
                      refine ⟨1775376307781926119936601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9468673641503605972995205 1775376307781926119936601)
                      ·
                        rfl

theorem cell23_3457533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_3457533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457533 prefixEnd_3457533 := by exact prefixLift 3457533
  have htrace : WordTrace (prefixWord ++ tailWord_3457533) baseStart_3457533 baseEnd_3457533 := by
    simpa [prefixWord, tailWord_3457533, baseEnd_3457533] using wordTrace_append hprefix tailTrace_3457533
  have hstable : (prefixWord ++ tailWord_3457533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457533).length < 2 ^ (prefixWord ++ tailWord_3457533).sum := by decide
  have hdescent : baseEnd_3457533 < baseStart_3457533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457537 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_3457537 : Nat := 118140960795 + 3457537 * 2 ^ 59
def prefixEnd_3457537 : Nat := 4983230072969 + 3 ^ 40 * 3457537 * 2
def baseEnd_3457537 : Nat := 1775378361704544104286583

theorem tailTrace_3457537 : CollatzResearch.WordTrace tailWord_3457537 prefixEnd_3457537 1775378361704544104286583 := by
  unfold tailWord_3457537
  simp only [CollatzResearch.WordTrace]
  refine ⟨126106734474941424152578865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84071156316627616101719243 126106734474941424152578865)
  ·
    refine ⟨94580050856206068114434149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126106734474941424152578865 94580050856206068114434149)
    ·
      refine ⟨17733759535538637771456403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94580050856206068114434149 17733759535538637771456403)
      ·
        refine ⟨26600639303307956657184605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17733759535538637771456403 26600639303307956657184605)
        ·
          refine ⟨9975239738740483746444227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26600639303307956657184605 9975239738740483746444227)
          ·
            refine ⟨14962859608110725619666341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975239738740483746444227 14962859608110725619666341)
            ·
              refine ⟨2805536176520761053687439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14962859608110725619666341 2805536176520761053687439)
              ·
                refine ⟨4208304264781141580531159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805536176520761053687439 4208304264781141580531159)
                ·
                  refine ⟨6312456397171712370796739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208304264781141580531159 6312456397171712370796739)
                  ·
                    refine ⟨9468684595757568556195109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6312456397171712370796739 9468684595757568556195109)
                    ·
                      refine ⟨1775378361704544104286583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9468684595757568556195109 1775378361704544104286583)
                      ·
                        rfl

theorem cell23_3457537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_3457537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457537 prefixEnd_3457537 := by exact prefixLift 3457537
  have htrace : WordTrace (prefixWord ++ tailWord_3457537) baseStart_3457537 baseEnd_3457537 := by
    simpa [prefixWord, tailWord_3457537, baseEnd_3457537] using wordTrace_append hprefix tailTrace_3457537
  have hstable : (prefixWord ++ tailWord_3457537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457537).length < 2 ^ (prefixWord ++ tailWord_3457537).sum := by decide
  have hdescent : baseEnd_3457537 < baseStart_3457537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457543 : List Nat := [1, 1, 4, 3, 3, 1, 10]
def baseStart_3457543 : Nat := 118140960795 + 3457543 * 2 ^ 59
def prefixEnd_3457543 : Nat := 4983230072969 + 3 ^ 40 * 3457543 * 2
def baseEnd_3457543 : Nat := 21918289414672482479155

theorem tailTrace_3457543 : CollatzResearch.WordTrace tailWord_3457543 prefixEnd_3457543 21918289414672482479155 := by
  unfold tailWord_3457543
  simp only [CollatzResearch.WordTrace]
  refine ⟨126106953312919687177297283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84071302208613124784864855 126106953312919687177297283)
  ·
    refine ⟨189160429969379530765945925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126106953312919687177297283 189160429969379530765945925)
    ·
      refine ⟨35467580619258662018614861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189160429969379530765945925 35467580619258662018614861)
      ·
        refine ⟨13300342732221998256980573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35467580619258662018614861 13300342732221998256980573)
        ·
          refine ⟨4987628524583249346367715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13300342732221998256980573 4987628524583249346367715)
          ·
            refine ⟨7481442786874874019551573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987628524583249346367715 7481442786874874019551573)
            ·
              refine ⟨21918289414672482479155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7481442786874874019551573 21918289414672482479155)
              ·
                rfl

theorem cell23_3457543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 10].length) (baseStart_3457543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457543 prefixEnd_3457543 := by exact prefixLift 3457543
  have htrace : WordTrace (prefixWord ++ tailWord_3457543) baseStart_3457543 baseEnd_3457543 := by
    simpa [prefixWord, tailWord_3457543, baseEnd_3457543] using wordTrace_append hprefix tailTrace_3457543
  have hstable : (prefixWord ++ tailWord_3457543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457543).length < 2 ^ (prefixWord ++ tailWord_3457543).sum := by decide
  have hdescent : baseEnd_3457543 < baseStart_3457543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457547 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 2, 4]
def baseStart_3457547 : Nat := 118140960795 + 3457547 * 2 ^ 59
def prefixEnd_3457547 : Nat := 4983230072969 + 3 ^ 40 * 3457547 * 2
def baseEnd_3457547 : Nat := 591794498837029688387179

theorem tailTrace_3457547 : CollatzResearch.WordTrace tailWord_3457547 prefixEnd_3457547 591794498837029688387179 := by
  unfold tailWord_3457547
  simp only [CollatzResearch.WordTrace]
  refine ⟨126107099204905195860442895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84071399469936797240295263 126107099204905195860442895)
  ·
    refine ⟨189160648807357793790664343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126107099204905195860442895 189160648807357793790664343)
    ·
      refine ⟨283740973211036690685996515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189160648807357793790664343 283740973211036690685996515)
      ·
        refine ⟨425611459816555036028994773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283740973211036690685996515 425611459816555036028994773)
        ·
          refine ⟨9975268589450508656929565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 425611459816555036028994773 9975268589450508656929565)
          ·
            refine ⟨3740725721043940746348587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9975268589450508656929565 3740725721043940746348587)
            ·
              refine ⟨5611088581565911119522881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740725721043940746348587 5611088581565911119522881)
              ·
                refine ⟨4208316436174433339642161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611088581565911119522881 4208316436174433339642161)
                ·
                  refine ⟨3156237327130825004731621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208316436174433339642161 3156237327130825004731621)
                  ·
                    refine ⟨591794498837029688387179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3156237327130825004731621 591794498837029688387179)
                    ·
                      rfl

theorem cell23_3457547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 4].length) (baseStart_3457547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457547 prefixEnd_3457547 := by exact prefixLift 3457547
  have htrace : WordTrace (prefixWord ++ tailWord_3457547) baseStart_3457547 baseEnd_3457547 := by
    simpa [prefixWord, tailWord_3457547, baseEnd_3457547] using wordTrace_append hprefix tailTrace_3457547
  have hstable : (prefixWord ++ tailWord_3457547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457547).length < 2 ^ (prefixWord ++ tailWord_3457547).sum := by decide
  have hdescent : baseEnd_3457547 < baseStart_3457547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457580 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 3, 3, 2]
def baseStart_3457580 : Nat := 118140960795 + 3457580 * 2 ^ 59
def prefixEnd_3457580 : Nat := 4983230072969 + 3 ^ 40 * 3457580 * 2
def baseEnd_3457580 : Nat := 1775400441372687436048885

theorem tailTrace_3457580 : CollatzResearch.WordTrace tailWord_3457580 prefixEnd_3457580 1775400441372687436048885 := by
  unfold tailWord_3457580
  simp only [CollatzResearch.WordTrace]
  refine ⟨63054151406892821248197097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84072201875857094997596129 63054151406892821248197097)
  ·
    refine ⟨47290613555169615936147823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63054151406892821248197097 47290613555169615936147823)
    ·
      refine ⟨70935920332754423904221735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47290613555169615936147823 70935920332754423904221735)
      ·
        refine ⟨106403880499131635856332603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70935920332754423904221735 106403880499131635856332603)
        ·
          refine ⟨159605820748697453784498905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106403880499131635856332603 159605820748697453784498905)
          ·
            refine ⟨119704365561523090338374179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159605820748697453784498905 119704365561523090338374179)
            ·
              refine ⟨179556548342284635507561269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119704365561523090338374179 179556548342284635507561269)
              ·
                refine ⟨16833426407089184578833869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179556548342284635507561269 16833426407089184578833869)
                ·
                  refine ⟨6312534902658444217062701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16833426407089184578833869 6312534902658444217062701)
                  ·
                    refine ⟨2367200588496916581398513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6312534902658444217062701 2367200588496916581398513)
                    ·
                      refine ⟨1775400441372687436048885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367200588496916581398513 1775400441372687436048885)
                      ·
                        rfl

theorem cell23_3457580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_3457580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457580 prefixEnd_3457580 := by exact prefixLift 3457580
  have htrace : WordTrace (prefixWord ++ tailWord_3457580) baseStart_3457580 baseEnd_3457580 := by
    simpa [prefixWord, tailWord_3457580, baseEnd_3457580] using wordTrace_append hprefix tailTrace_3457580
  have hstable : (prefixWord ++ tailWord_3457580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457580).length < 2 ^ (prefixWord ++ tailWord_3457580).sum := by decide
  have hdescent : baseEnd_3457580 < baseStart_3457580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457623 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_3457623 : Nat := 118140960795 + 3457623 * 2 ^ 59
def prefixEnd_3457623 : Nat := 4983230072969 + 3 ^ 40 * 3457623 * 2
def baseEnd_3457623 : Nat := 1775422521040830767811187

theorem tailTrace_3457623 : CollatzResearch.WordTrace tailWord_3457623 prefixEnd_3457623 1775422521040830767811187 := by
  unfold tailWord_3457623
  simp only [CollatzResearch.WordTrace]
  refine ⟨126109871152629860840209523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84073247435086573893473015 126109871152629860840209523)
  ·
    refine ⟨189164806728944791260314285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126109871152629860840209523 189164806728944791260314285)
    ·
      refine ⟨70936802523354296722617857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189164806728944791260314285 70936802523354296722617857)
      ·
        refine ⟨53202601892515722541963393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70936802523354296722617857 53202601892515722541963393)
        ·
          refine ⟨39901951419386791906472545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53202601892515722541963393 39901951419386791906472545)
          ·
            refine ⟨29926463564540093929854409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39901951419386791906472545 29926463564540093929854409)
            ·
              refine ⟨22444847673405070447390807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29926463564540093929854409 22444847673405070447390807)
              ·
                refine ⟨33667271510107605671086211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22444847673405070447390807 33667271510107605671086211)
                ·
                  refine ⟨50500907265161408506629317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33667271510107605671086211 50500907265161408506629317)
                  ·
                    refine ⟨9468920112217764094992997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50500907265161408506629317 9468920112217764094992997)
                    ·
                      refine ⟨1775422521040830767811187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9468920112217764094992997 1775422521040830767811187)
                      ·
                        rfl

theorem cell23_3457623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_3457623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457623 prefixEnd_3457623 := by exact prefixLift 3457623
  have htrace : WordTrace (prefixWord ++ tailWord_3457623) baseStart_3457623 baseEnd_3457623 := by
    simpa [prefixWord, tailWord_3457623, baseEnd_3457623] using wordTrace_append hprefix tailTrace_3457623
  have hstable : (prefixWord ++ tailWord_3457623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457623).length < 2 ^ (prefixWord ++ tailWord_3457623).sum := by decide
  have hdescent : baseEnd_3457623 < baseStart_3457623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457643 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 3]
def baseStart_3457643 : Nat := 118140960795 + 3457643 * 2 ^ 59
def prefixEnd_3457643 : Nat := 4983230072969 + 3 ^ 40 * 3457643 * 2
def baseEnd_3457643 : Nat := 1775432790653920689561095

theorem tailTrace_3457643 : CollatzResearch.WordTrace tailWord_3457643 prefixEnd_3457643 1775432790653920689561095 := by
  unfold tailWord_3457643
  simp only [CollatzResearch.WordTrace]
  refine ⟨126110600612557404255937583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84073733741704936170625055 126110600612557404255937583)
  ·
    refine ⟨189165900918836106383906375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126110600612557404255937583 189165900918836106383906375)
    ·
      refine ⟨283748851378254159575859563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189165900918836106383906375 283748851378254159575859563)
      ·
        refine ⟨425623277067381239363789345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283748851378254159575859563 425623277067381239363789345)
        ·
          refine ⟨319217457800535929522842009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425623277067381239363789345 319217457800535929522842009)
          ·
            refine ⟨239413093350401947142131507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319217457800535929522842009 239413093350401947142131507)
            ·
              refine ⟨359119640025602920713197261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239413093350401947142131507 359119640025602920713197261)
              ·
                refine ⟨134669865009601095267448973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359119640025602920713197261 134669865009601095267448973)
                ·
                  refine ⟨50501199378600410725293365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134669865009601095267448973 50501199378600410725293365)
                  ·
                    refine ⟨4734487441743788505496253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50501199378600410725293365 4734487441743788505496253)
                    ·
                      refine ⟨1775432790653920689561095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734487441743788505496253 1775432790653920689561095)
                      ·
                        rfl

theorem cell23_3457643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 3].length) (baseStart_3457643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457643 prefixEnd_3457643 := by exact prefixLift 3457643
  have htrace : WordTrace (prefixWord ++ tailWord_3457643) baseStart_3457643 baseEnd_3457643 := by
    simpa [prefixWord, tailWord_3457643, baseEnd_3457643] using wordTrace_append hprefix tailTrace_3457643
  have hstable : (prefixWord ++ tailWord_3457643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457643).length < 2 ^ (prefixWord ++ tailWord_3457643).sum := by decide
  have hdescent : baseEnd_3457643 < baseStart_3457643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457661 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_3457661 : Nat := 118140960795 + 3457661 * 2 ^ 59
def prefixEnd_3457661 : Nat := 4983230072969 + 3 ^ 40 * 3457661 * 2
def baseEnd_3457661 : Nat := 1775442033305701619136013

theorem tailTrace_3457661 : CollatzResearch.WordTrace tailWord_3457661 prefixEnd_3457661 1775442033305701619136013 := by
  unfold tailWord_3457661
  simp only [CollatzResearch.WordTrace]
  refine ⟨126111257126492193330092837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84074171417661462220061891 126111257126492193330092837)
  ·
    refine ⟨23645860711217286249392407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126111257126492193330092837 23645860711217286249392407)
    ·
      refine ⟨35468791066825929374088611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23645860711217286249392407 35468791066825929374088611)
      ·
        refine ⟨53203186600238894061132917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35468791066825929374088611 53203186600238894061132917)
        ·
          refine ⟨4987798743772396318231211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53203186600238894061132917 4987798743772396318231211)
          ·
            refine ⟨7481698115658594477346817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987798743772396318231211 7481698115658594477346817)
            ·
              refine ⟨5611273586743945858010113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7481698115658594477346817 5611273586743945858010113)
              ·
                refine ⟨4208455190057959393507585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611273586743945858010113 4208455190057959393507585)
                ·
                  refine ⟨3156341392543469545130689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208455190057959393507585 3156341392543469545130689)
                  ·
                    refine ⟨2367256044407602158848017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3156341392543469545130689 2367256044407602158848017)
                    ·
                      refine ⟨1775442033305701619136013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367256044407602158848017 1775442033305701619136013)
                      ·
                        rfl

theorem cell23_3457661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_3457661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457661 prefixEnd_3457661 := by exact prefixLift 3457661
  have htrace : WordTrace (prefixWord ++ tailWord_3457661) baseStart_3457661 baseEnd_3457661 := by
    simpa [prefixWord, tailWord_3457661, baseEnd_3457661] using wordTrace_append hprefix tailTrace_3457661
  have hstable : (prefixWord ++ tailWord_3457661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457661).length < 2 ^ (prefixWord ++ tailWord_3457661).sum := by decide
  have hdescent : baseEnd_3457661 < baseStart_3457661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457663 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 4, 5]
def baseStart_3457663 : Nat := 118140960795 + 3457663 * 2 ^ 59
def prefixEnd_3457663 : Nat := 4983230072969 + 3 ^ 40 * 3457663 * 2
def baseEnd_3457663 : Nat := 591814353422336870437001

theorem tailTrace_3457663 : CollatzResearch.WordTrace tailWord_3457663 prefixEnd_3457663 591814353422336870437001 := by
  unfold tailWord_3457663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126111330072484947671665643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84074220048323298447777095 126111330072484947671665643)
  ·
    refine ⟨189166995108727421507498465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126111330072484947671665643 189166995108727421507498465)
    ·
      refine ⟨141875246331545566130623849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189166995108727421507498465 141875246331545566130623849)
      ·
        refine ⟨106406434748659174597967887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141875246331545566130623849 106406434748659174597967887)
        ·
          refine ⟨159609652122988761896951831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106406434748659174597967887 159609652122988761896951831)
          ·
            refine ⟨239414478184483142845427747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159609652122988761896951831 239414478184483142845427747)
            ·
              refine ⟨359121717276724714268141621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239414478184483142845427747 359121717276724714268141621)
              ·
                refine ⟨33667660994692941962638277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359121717276724714268141621 33667660994692941962638277)
                ·
                  refine ⟨6312686436504926617994677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33667660994692941962638277 6312686436504926617994677)
                  ·
                    refine ⟨591814353422336870437001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6312686436504926617994677 591814353422336870437001)
                    ·
                      rfl

theorem cell23_3457663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_3457663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457663 prefixEnd_3457663 := by exact prefixLift 3457663
  have htrace : WordTrace (prefixWord ++ tailWord_3457663) baseStart_3457663 baseEnd_3457663 := by
    simpa [prefixWord, tailWord_3457663, baseEnd_3457663] using wordTrace_append hprefix tailTrace_3457663
  have hstable : (prefixWord ++ tailWord_3457663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457663).length < 2 ^ (prefixWord ++ tailWord_3457663).sum := by decide
  have hdescent : baseEnd_3457663 < baseStart_3457663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457667 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 5]
def baseStart_3457667 : Nat := 118140960795 + 3457667 * 2 ^ 59
def prefixEnd_3457667 : Nat := 4983230072969 + 3 ^ 40 * 3457667 * 2
def baseEnd_3457667 : Nat := 197271679354403177295665

theorem tailTrace_3457667 : CollatzResearch.WordTrace tailWord_3457667 prefixEnd_3457667 197271679354403177295665 := by
  unfold tailWord_3457667
  simp only [CollatzResearch.WordTrace]
  refine ⟨126111475964470456354811255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84074317309646970903207503 126111475964470456354811255)
  ·
    refine ⟨189167213946705684532216883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126111475964470456354811255 189167213946705684532216883)
    ·
      refine ⟨283750820920058526798325325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189167213946705684532216883 283750820920058526798325325)
      ·
        refine ⟨106406557845021947549371997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283750820920058526798325325 106406557845021947549371997)
        ·
          refine ⟨39902459191883230331014499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106406557845021947549371997 39902459191883230331014499)
          ·
            refine ⟨59853688787824845496521749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39902459191883230331014499 59853688787824845496521749)
            ·
              refine ⟨2805641661929289632649457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59853688787824845496521749 2805641661929289632649457)
              ·
                refine ⟨2104231246446967224487093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805641661929289632649457 2104231246446967224487093)
                ·
                  refine ⟨197271679354403177295665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2104231246446967224487093 197271679354403177295665)
                  ·
                    rfl

theorem cell23_3457667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 5].length) (baseStart_3457667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457667 prefixEnd_3457667 := by exact prefixLift 3457667
  have htrace : WordTrace (prefixWord ++ tailWord_3457667) baseStart_3457667 baseEnd_3457667 := by
    simpa [prefixWord, tailWord_3457667, baseEnd_3457667] using wordTrace_append hprefix tailTrace_3457667
  have hstable : (prefixWord ++ tailWord_3457667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457667).length < 2 ^ (prefixWord ++ tailWord_3457667).sum := by decide
  have hdescent : baseEnd_3457667 < baseStart_3457667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457683 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4]
def baseStart_3457683 : Nat := 118140960795 + 3457683 * 2 ^ 59
def prefixEnd_3457683 : Nat := 4983230072969 + 3 ^ 40 * 3457683 * 2
def baseEnd_3457683 : Nat := 1775453329880100533060911

theorem tailTrace_3457683 : CollatzResearch.WordTrace tailWord_3457683 prefixEnd_3457683 1775453329880100533060911 := by
  unfold tailWord_3457683
  simp only [CollatzResearch.WordTrace]
  refine ⟨126112059532412491087393703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84074706354941660724929135 126112059532412491087393703)
  ·
    refine ⟨189168089298618736631090555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126112059532412491087393703 189168089298618736631090555)
    ·
      refine ⟨283752133947928104946635833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189168089298618736631090555 283752133947928104946635833)
      ·
        refine ⟨212814100460946078709976875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283752133947928104946635833 212814100460946078709976875)
        ·
          refine ⟨319221150691419118064965313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212814100460946078709976875 319221150691419118064965313)
          ·
            refine ⟨239415863018564338548723985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319221150691419118064965313 239415863018564338548723985)
            ·
              refine ⟨179561897263923253911542989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239415863018564338548723985 179561897263923253911542989)
              ·
                refine ⟨67335711473971220216828621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179561897263923253911542989 67335711473971220216828621)
                ·
                  refine ⟨25250891802739207581310733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67335711473971220216828621 25250891802739207581310733)
                  ·
                    refine ⟨9469084426027202842991525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25250891802739207581310733 9469084426027202842991525)
                    ·
                      refine ⟨1775453329880100533060911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9469084426027202842991525 1775453329880100533060911)
                      ·
                        rfl

theorem cell23_3457683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_3457683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457683 prefixEnd_3457683 := by exact prefixLift 3457683
  have htrace : WordTrace (prefixWord ++ tailWord_3457683) baseStart_3457683 baseEnd_3457683 := by
    simpa [prefixWord, tailWord_3457683, baseEnd_3457683] using wordTrace_append hprefix tailTrace_3457683
  have hstable : (prefixWord ++ tailWord_3457683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457683).length < 2 ^ (prefixWord ++ tailWord_3457683).sum := by decide
  have hdescent : baseEnd_3457683 < baseStart_3457683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457700 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_3457700 : Nat := 118140960795 + 3457700 * 2 ^ 59
def prefixEnd_3457700 : Nat := 4983230072969 + 3 ^ 40 * 3457700 * 2
def baseEnd_3457700 : Nat := 1775462059051226966548333

theorem tailTrace_3457700 : CollatzResearch.WordTrace tailWord_3457700 prefixEnd_3457700 1775462059051226966548333 := by
  unfold tailWord_3457700
  simp only [CollatzResearch.WordTrace]
  refine ⟨63056339786675451495381277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84075119715567268660508369 63056339786675451495381277)
  ·
    refine ⟨23646127420003294310767979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63056339786675451495381277 23646127420003294310767979)
    ·
      refine ⟨35469191130004941466151969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23646127420003294310767979 35469191130004941466151969)
      ·
        refine ⟨26601893347503706099613977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35469191130004941466151969 26601893347503706099613977)
        ·
          refine ⟨19951420010627779574710483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26601893347503706099613977 19951420010627779574710483)
          ·
            refine ⟨29927130015941669362065725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19951420010627779574710483 29927130015941669362065725)
            ·
              refine ⟨11222673755978126010774647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29927130015941669362065725 11222673755978126010774647)
              ·
                refine ⟨16834010633967189016161971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11222673755978126010774647 16834010633967189016161971)
                ·
                  refine ⟨25251015950950783524242957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16834010633967189016161971 25251015950950783524242957)
                  ·
                    refine ⟨9469130981606543821591109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25251015950950783524242957 9469130981606543821591109)
                    ·
                      refine ⟨1775462059051226966548333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9469130981606543821591109 1775462059051226966548333)
                      ·
                        rfl

theorem cell23_3457700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_3457700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457700 prefixEnd_3457700 := by exact prefixLift 3457700
  have htrace : WordTrace (prefixWord ++ tailWord_3457700) baseStart_3457700 baseEnd_3457700 := by
    simpa [prefixWord, tailWord_3457700, baseEnd_3457700] using wordTrace_append hprefix tailTrace_3457700
  have hstable : (prefixWord ++ tailWord_3457700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457700).length < 2 ^ (prefixWord ++ tailWord_3457700).sum := by decide
  have hdescent : baseEnd_3457700 < baseStart_3457700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457727 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 3, 4]
def baseStart_3457727 : Nat := 118140960795 + 3457727 * 2 ^ 59
def prefixEnd_3457727 : Nat := 4983230072969 + 3 ^ 40 * 3457727 * 2
def baseEnd_3457727 : Nat := 591825307676299453636903

theorem tailTrace_3457727 : CollatzResearch.WordTrace tailWord_3457727 prefixEnd_3457727 591825307676299453636903 := by
  unfold tailWord_3457727
  simp only [CollatzResearch.WordTrace]
  refine ⟨126113664344253086601995435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84075776229502057734663623 126113664344253086601995435)
  ·
    refine ⟨189170496516379629902993153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126113664344253086601995435 189170496516379629902993153)
    ·
      refine ⟨141877872387284722427244865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189170496516379629902993153 141877872387284722427244865)
      ·
        refine ⟨106408404290463541820433649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141877872387284722427244865 106408404290463541820433649)
        ·
          refine ⟨79806303217847656365325237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106408404290463541820433649 79806303217847656365325237)
          ·
            refine ⟨7481840926673217784249241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79806303217847656365325237 7481840926673217784249241)
            ·
              refine ⟨5611380695004913338186931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7481840926673217784249241 5611380695004913338186931)
              ·
                refine ⟨8417071042507370007280397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611380695004913338186931 8417071042507370007280397)
                ·
                  refine ⟨3156401640940263752730149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8417071042507370007280397 3156401640940263752730149)
                  ·
                    refine ⟨591825307676299453636903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3156401640940263752730149 591825307676299453636903)
                    ·
                      rfl

theorem cell23_3457727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_3457727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457727 prefixEnd_3457727 := by exact prefixLift 3457727
  have htrace : WordTrace (prefixWord ++ tailWord_3457727) baseStart_3457727 baseEnd_3457727 := by
    simpa [prefixWord, tailWord_3457727, baseEnd_3457727] using wordTrace_append hprefix tailTrace_3457727
  have hstable : (prefixWord ++ tailWord_3457727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457727).length < 2 ^ (prefixWord ++ tailWord_3457727).sum := by decide
  have hdescent : baseEnd_3457727 < baseStart_3457727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457761 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3457761 : Nat := 118140960795 + 3457761 * 2 ^ 59
def prefixEnd_3457761 : Nat := 4983230072969 + 3 ^ 40 * 3457761 * 2
def baseEnd_3457761 : Nat := 591831127123717075961851

theorem tailTrace_3457761 : CollatzResearch.WordTrace tailWord_3457761 prefixEnd_3457761 591831127123717075961851 := by
  unfold tailWord_3457761
  simp only [CollatzResearch.WordTrace]
  refine ⟨126114904426129910408733137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84076602950753273605822091 126114904426129910408733137)
  ·
    refine ⟨94586178319597432806549853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126114904426129910408733137 94586178319597432806549853)
    ·
      refine ⟨35469816869849037302456195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94586178319597432806549853 35469816869849037302456195)
      ·
        refine ⟨53204725304773555953684293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35469816869849037302456195 53204725304773555953684293)
        ·
          refine ⟨9975885994645041741315805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53204725304773555953684293 9975885994645041741315805)
          ·
            refine ⟨3740957247991890652993427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9975885994645041741315805 3740957247991890652993427)
            ·
              refine ⟨5611435871987835979490141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740957247991890652993427 5611435871987835979490141)
              ·
                refine ⟨2104288451995438492308803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5611435871987835979490141 2104288451995438492308803)
                ·
                  refine ⟨3156432677993157738463205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104288451995438492308803 3156432677993157738463205)
                  ·
                    refine ⟨591831127123717075961851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3156432677993157738463205 591831127123717075961851)
                    ·
                      rfl

theorem cell23_3457761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3457761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457761 prefixEnd_3457761 := by exact prefixLift 3457761
  have htrace : WordTrace (prefixWord ++ tailWord_3457761) baseStart_3457761 baseEnd_3457761 := by
    simpa [prefixWord, tailWord_3457761, baseEnd_3457761] using wordTrace_append hprefix tailTrace_3457761
  have hstable : (prefixWord ++ tailWord_3457761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457761).length < 2 ^ (prefixWord ++ tailWord_3457761).sum := by decide
  have hdescent : baseEnd_3457761 < baseStart_3457761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457770 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3457770 : Nat := 118140960795 + 3457770 * 2 ^ 59
def prefixEnd_3457770 : Nat := 4983230072969 + 3 ^ 40 * 3457770 * 2
def baseEnd_3457770 : Nat := 591832667565680564224337

theorem tailTrace_3457770 : CollatzResearch.WordTrace tailWord_3457770 prefixEnd_3457770 591832667565680564224337 := by
  unfold tailWord_3457770
  simp only [CollatzResearch.WordTrace]
  refine ⟨31528808170774326236452691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84076821788731536630540509 31528808170774326236452691)
  ·
    refine ⟨47293212256161489354679037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31528808170774326236452691 47293212256161489354679037)
    ·
      refine ⟨17734954596060558508004639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47293212256161489354679037 17734954596060558508004639)
      ·
        refine ⟨26602431894090837762006959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17734954596060558508004639 26602431894090837762006959)
        ·
          refine ⟨39903647841136256643010439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26602431894090837762006959 39903647841136256643010439)
          ·
            refine ⟨59855471761704384964515659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39903647841136256643010439 59855471761704384964515659)
            ·
              refine ⟨89783207642556577446773489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59855471761704384964515659 89783207642556577446773489)
              ·
                refine ⟨67337405731917433085080117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89783207642556577446773489 67337405731917433085080117)
                ·
                  refine ⟨6312881787367259351726261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67337405731917433085080117 6312881787367259351726261)
                  ·
                    refine ⟨591832667565680564224337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6312881787367259351726261 591832667565680564224337)
                    ·
                      rfl

theorem cell23_3457770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3457770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457770 prefixEnd_3457770 := by exact prefixLift 3457770
  have htrace : WordTrace (prefixWord ++ tailWord_3457770) baseStart_3457770 baseEnd_3457770 := by
    simpa [prefixWord, tailWord_3457770, baseEnd_3457770] using wordTrace_append hprefix tailTrace_3457770
  have hstable : (prefixWord ++ tailWord_3457770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457770).length < 2 ^ (prefixWord ++ tailWord_3457770).sum := by decide
  have hdescent : baseEnd_3457770 < baseStart_3457770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457862 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3457862 : Nat := 118140960795 + 3457862 * 2 ^ 59
def prefixEnd_3457862 : Nat := 4983230072969 + 3 ^ 40 * 3457862 * 2
def baseEnd_3457862 : Nat := 1775545242917255332722589

theorem tailTrace_3457862 : CollatzResearch.WordTrace tailWord_3457862 prefixEnd_3457862 1775545242917255332722589 := by
  unfold tailWord_3457862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941205881211375145567495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84079058799176003105439893 3941205881211375145567495)
  ·
    refine ⟨5911808821817062718351243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3941205881211375145567495 5911808821817062718351243)
    ·
      refine ⟨8867713232725594077526865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911808821817062718351243 8867713232725594077526865)
      ·
        refine ⟨6650784924544195558145149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8867713232725594077526865 6650784924544195558145149)
        ·
          refine ⟨2494044346704073334304431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6650784924544195558145149 2494044346704073334304431)
          ·
            refine ⟨3741066520056110001456647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494044346704073334304431 3741066520056110001456647)
            ·
              refine ⟨5611599780084165002184971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741066520056110001456647 5611599780084165002184971)
              ·
                refine ⟨8417399670126247503277457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611599780084165002184971 8417399670126247503277457)
                ·
                  refine ⟨6313049752594685627458093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8417399670126247503277457 6313049752594685627458093)
                  ·
                    refine ⟨2367393657223007110296785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6313049752594685627458093 2367393657223007110296785)
                    ·
                      refine ⟨1775545242917255332722589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367393657223007110296785 1775545242917255332722589)
                      ·
                        rfl

theorem cell23_3457862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3457862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457862 prefixEnd_3457862 := by exact prefixLift 3457862
  have htrace : WordTrace (prefixWord ++ tailWord_3457862) baseStart_3457862 baseEnd_3457862 := by
    simpa [prefixWord, tailWord_3457862, baseEnd_3457862] using wordTrace_append hprefix tailTrace_3457862
  have hstable : (prefixWord ++ tailWord_3457862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457862).length < 2 ^ (prefixWord ++ tailWord_3457862).sum := by decide
  have hdescent : baseEnd_3457862 < baseStart_3457862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457874 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3457874 : Nat := 118140960795 + 3457874 * 2 ^ 59
def prefixEnd_3457874 : Nat := 4983230072969 + 3 ^ 40 * 3457874 * 2
def baseEnd_3457874 : Nat := 1775551404685109285772533

theorem tailTrace_3457874 : CollatzResearch.WordTrace tailWord_3457874 prefixEnd_3457874 1775551404685109285772533 := by
  unfold tailWord_3457874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31529756468680132676899169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84079350583147020471731117 31529756468680132676899169)
  ·
    refine ⟨23647317351510099507674377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31529756468680132676899169 23647317351510099507674377)
    ·
      refine ⟨17735488013632574630755783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23647317351510099507674377 17735488013632574630755783)
      ·
        refine ⟨26603232020448861946133675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17735488013632574630755783 26603232020448861946133675)
        ·
          refine ⟨39904848030673292919200513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26603232020448861946133675 39904848030673292919200513)
          ·
            refine ⟨29928636023004969689400385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39904848030673292919200513 29928636023004969689400385)
            ·
              refine ⟨22446477017253727267050289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29928636023004969689400385 22446477017253727267050289)
              ·
                refine ⟨16834857762940295450287717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22446477017253727267050289 16834857762940295450287717)
                ·
                  refine ⟨3156535830551305396928947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16834857762940295450287717 3156535830551305396928947)
                  ·
                    refine ⟨4734803745826958095393421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156535830551305396928947 4734803745826958095393421)
                    ·
                      refine ⟨1775551404685109285772533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734803745826958095393421 1775551404685109285772533)
                      ·
                        rfl

theorem cell23_3457874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3457874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457874 prefixEnd_3457874 := by exact prefixLift 3457874
  have htrace : WordTrace (prefixWord ++ tailWord_3457874) baseStart_3457874 baseEnd_3457874 := by
    simpa [prefixWord, tailWord_3457874, baseEnd_3457874] using wordTrace_append hprefix tailTrace_3457874
  have hstable : (prefixWord ++ tailWord_3457874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457874).length < 2 ^ (prefixWord ++ tailWord_3457874).sum := by decide
  have hdescent : baseEnd_3457874 < baseStart_3457874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457891 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 3]
def baseStart_3457891 : Nat := 118140960795 + 3457891 * 2 ^ 59
def prefixEnd_3457891 : Nat := 4983230072969 + 3 ^ 40 * 3457891 * 2
def baseEnd_3457891 : Nat := 1775560133856235719259955

theorem tailTrace_3457891 : CollatzResearch.WordTrace tailWord_3457891 prefixEnd_3457891 1775560133856235719259955 := by
  unfold tailWord_3457891
  simp only [CollatzResearch.WordTrace]
  refine ⟨126119645915658942610965527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84079763943772628407310351 126119645915658942610965527)
  ·
    refine ⟨189179468873488413916448291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126119645915658942610965527 189179468873488413916448291)
    ·
      refine ⟨283769203310232620874672437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189179468873488413916448291 283769203310232620874672437)
      ·
        refine ⟨26603362810334308207000541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283769203310232620874672437 26603362810334308207000541)
        ·
          refine ⟨9976261053875365577625203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26603362810334308207000541 9976261053875365577625203)
          ·
            refine ⟨14964391580813048366437805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976261053875365577625203 14964391580813048366437805)
            ·
              refine ⟨5611646842804893137414177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14964391580813048366437805 5611646842804893137414177)
              ·
                refine ⟨4208735132103669853060633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611646842804893137414177 4208735132103669853060633)
                ·
                  refine ⟨3156551349077752389795475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208735132103669853060633 3156551349077752389795475)
                  ·
                    refine ⟨4734827023616628584693213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156551349077752389795475 4734827023616628584693213)
                    ·
                      refine ⟨1775560133856235719259955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734827023616628584693213 1775560133856235719259955)
                      ·
                        rfl

theorem cell23_3457891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_3457891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457891 prefixEnd_3457891 := by exact prefixLift 3457891
  have htrace : WordTrace (prefixWord ++ tailWord_3457891) baseStart_3457891 baseEnd_3457891 := by
    simpa [prefixWord, tailWord_3457891, baseEnd_3457891] using wordTrace_append hprefix tailTrace_3457891
  have hstable : (prefixWord ++ tailWord_3457891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457891).length < 2 ^ (prefixWord ++ tailWord_3457891).sum := by decide
  have hdescent : baseEnd_3457891 < baseStart_3457891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457897 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 8, 2]
def baseStart_3457897 : Nat := 118140960795 + 3457897 * 2 ^ 59
def prefixEnd_3457897 : Nat := 4983230072969 + 3 ^ 40 * 3457897 * 2
def baseEnd_3457897 : Nat := 1775563214740162695784927

theorem tailTrace_3457897 : CollatzResearch.WordTrace tailWord_3457897 prefixEnd_3457897 1775563214740162695784927 := by
  unfold tailWord_3457897
  simp only [CollatzResearch.WordTrace]
  refine ⟨126119864753637205635683945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84079909835758137090455963 126119864753637205635683945)
  ·
    refine ⟨94589898565227904226762959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126119864753637205635683945 94589898565227904226762959)
    ·
      refine ⟨141884847847841856340144439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94589898565227904226762959 141884847847841856340144439)
      ·
        refine ⟨212827271771762784510216659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141884847847841856340144439 212827271771762784510216659)
        ·
          refine ⟨319240907657644176765324989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212827271771762784510216659 319240907657644176765324989)
          ·
            refine ⟨119715340371616566286996871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319240907657644176765324989 119715340371616566286996871)
            ·
              refine ⟨179573010557424849430495307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119715340371616566286996871 179573010557424849430495307)
              ·
                refine ⟨269359515836137274145742961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179573010557424849430495307 269359515836137274145742961)
                ·
                  refine ⟨202019636877102955609307221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269359515836137274145742961 202019636877102955609307221)
                  ·
                    refine ⟨2367417619653550261046569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 202019636877102955609307221 2367417619653550261046569)
                    ·
                      refine ⟨1775563214740162695784927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367417619653550261046569 1775563214740162695784927)
                      ·
                        rfl

theorem cell23_3457897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 8, 2].length) (baseStart_3457897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457897 prefixEnd_3457897 := by exact prefixLift 3457897
  have htrace : WordTrace (prefixWord ++ tailWord_3457897) baseStart_3457897 baseEnd_3457897 := by
    simpa [prefixWord, tailWord_3457897, baseEnd_3457897] using wordTrace_append hprefix tailTrace_3457897
  have hstable : (prefixWord ++ tailWord_3457897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457897).length < 2 ^ (prefixWord ++ tailWord_3457897).sum := by decide
  have hdescent : baseEnd_3457897 < baseStart_3457897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457917 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_3457917 : Nat := 118140960795 + 3457917 * 2 ^ 59
def prefixEnd_3457917 : Nat := 4983230072969 + 3 ^ 40 * 3457917 * 2
def baseEnd_3457917 : Nat := 1775573484353252617534835

theorem tailTrace_3457917 : CollatzResearch.WordTrace tailWord_3457917 prefixEnd_3457917 1775573484353252617534835 := by
  unfold tailWord_3457917
  simp only [CollatzResearch.WordTrace]
  refine ⟨126120594213564749051412005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84080396142376499367608003 126120594213564749051412005)
  ·
    refine ⟨23647611415043390447139751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126120594213564749051412005 23647611415043390447139751)
    ·
      refine ⟨35471417122565085670709627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23647611415043390447139751 35471417122565085670709627)
      ·
        refine ⟨53207125683847628506064441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35471417122565085670709627 53207125683847628506064441)
        ·
          refine ⟨39905344262885721379548331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53207125683847628506064441 39905344262885721379548331)
          ·
            refine ⟨59858016394328582069322497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39905344262885721379548331 59858016394328582069322497)
            ·
              refine ⟨44893512295746436551991873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59858016394328582069322497 44893512295746436551991873)
              ·
                refine ⟨33670134221809827413993905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44893512295746436551991873 33670134221809827413993905)
                ·
                  refine ⟨25252600666357370560495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33670134221809827413993905 25252600666357370560495429)
                  ·
                    refine ⟨4734862624942006980092893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25252600666357370560495429 4734862624942006980092893)
                    ·
                      refine ⟨1775573484353252617534835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4734862624942006980092893 1775573484353252617534835)
                      ·
                        rfl

theorem cell23_3457917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_3457917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457917 prefixEnd_3457917 := by exact prefixLift 3457917
  have htrace : WordTrace (prefixWord ++ tailWord_3457917) baseStart_3457917 baseEnd_3457917 := by
    simpa [prefixWord, tailWord_3457917, baseEnd_3457917] using wordTrace_append hprefix tailTrace_3457917
  have hstable : (prefixWord ++ tailWord_3457917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457917).length < 2 ^ (prefixWord ++ tailWord_3457917).sum := by decide
  have hdescent : baseEnd_3457917 < baseStart_3457917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457920 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 9]
def baseStart_3457920 : Nat := 118140960795 + 3457920 * 2 ^ 59
def prefixEnd_3457920 : Nat := 4983230072969 + 3 ^ 40 * 3457920 * 2
def baseEnd_3457920 : Nat := 197286113866135122866369

theorem tailTrace_3457920 : CollatzResearch.WordTrace tailWord_3457920 prefixEnd_3457920 197286113866135122866369 := by
  unfold tailWord_3457920
  simp only [CollatzResearch.WordTrace]
  refine ⟨63060351816276940281885607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84080469088369253709180809 63060351816276940281885607)
  ·
    refine ⟨94590527724415410422828411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63060351816276940281885607 94590527724415410422828411)
    ·
      refine ⟨141885791586623115634242617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94590527724415410422828411 141885791586623115634242617)
      ·
        refine ⟨106414343689967336725681963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141885791586623115634242617 106414343689967336725681963)
        ·
          refine ⟨159621515534951005088522945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106414343689967336725681963 159621515534951005088522945)
          ·
            refine ⟨119716136651213253816392209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159621515534951005088522945 119716136651213253816392209)
            ·
              refine ⟨89787102488409940362294157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119716136651213253816392209 89787102488409940362294157)
              ·
                refine ⟨33670163433153727635860309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89787102488409940362294157 33670163433153727635860309)
                ·
                  refine ⟨197286113866135122866369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33670163433153727635860309 197286113866135122866369)
                  ·
                    rfl

theorem cell23_3457920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_3457920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457920 prefixEnd_3457920 := by exact prefixLift 3457920
  have htrace : WordTrace (prefixWord ++ tailWord_3457920) baseStart_3457920 baseEnd_3457920 := by
    simpa [prefixWord, tailWord_3457920, baseEnd_3457920] using wordTrace_append hprefix tailTrace_3457920
  have hstable : (prefixWord ++ tailWord_3457920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457920).length < 2 ^ (prefixWord ++ tailWord_3457920).sum := by decide
  have hdescent : baseEnd_3457920 < baseStart_3457920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457954 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3457954 : Nat := 118140960795 + 3457954 * 2 ^ 59
def prefixEnd_3457954 : Nat := 4983230072969 + 3 ^ 40 * 3457954 * 2
def baseEnd_3457954 : Nat := 197288053681940996974685

theorem tailTrace_3457954 : CollatzResearch.WordTrace tailWord_3457954 prefixEnd_3457954 197288053681940996974685 := by
  unfold tailWord_3457954
  simp only [CollatzResearch.WordTrace]
  refine ⟨31530485928607676092627229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84081295809620469580339277 31530485928607676092627229)
  ·
    refine ⟨11823932223227878534735211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31530485928607676092627229 11823932223227878534735211)
    ·
      refine ⟨17735898334841817802102817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823932223227878534735211 17735898334841817802102817)
      ·
        refine ⟨13301923751131363351577113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17735898334841817802102817 13301923751131363351577113)
        ·
          refine ⟨9976442813348522513682835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13301923751131363351577113 9976442813348522513682835)
          ·
            refine ⟨14964664220022783770524253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976442813348522513682835 14964664220022783770524253)
            ·
              refine ⟨5611749082508543913946595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14964664220022783770524253 5611749082508543913946595)
              ·
                refine ⟨8417623623762815870919893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611749082508543913946595 8417623623762815870919893)
                ·
                  refine ⟨197288053681940996974685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8417623623762815870919893 197288053681940996974685)
                  ·
                    rfl

theorem cell23_3457954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3457954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457954 prefixEnd_3457954 := by exact prefixLift 3457954
  have htrace : WordTrace (prefixWord ++ tailWord_3457954) baseStart_3457954 baseEnd_3457954 := by
    simpa [prefixWord, tailWord_3457954, baseEnd_3457954] using wordTrace_append hprefix tailTrace_3457954
  have hstable : (prefixWord ++ tailWord_3457954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457954).length < 2 ^ (prefixWord ++ tailWord_3457954).sum := by decide
  have hdescent : baseEnd_3457954 < baseStart_3457954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457984 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 2, 5]
def baseStart_3457984 : Nat := 118140960795 + 3457984 * 2 ^ 59
def prefixEnd_3457984 : Nat := 4983230072969 + 3 ^ 40 * 3457984 * 2
def baseEnd_3457984 : Nat := 591869295852367951799009

theorem tailTrace_3457984 : CollatzResearch.WordTrace tailWord_3457984 prefixEnd_3457984 591869295852367951799009 := by
  unfold tailWord_3457984
  simp only [CollatzResearch.WordTrace]
  refine ⟨63061518952161009747050503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84082025269548012996067337 63061518952161009747050503)
  ·
    refine ⟨94592278428241514620575755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63061518952161009747050503 94592278428241514620575755)
    ·
      refine ⟨141888417642362271930863633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94592278428241514620575755 141888417642362271930863633)
      ·
        refine ⟨106416313231771703948147725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141888417642362271930863633 106416313231771703948147725)
        ·
          refine ⟨39906117461914388980555397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106416313231771703948147725 39906117461914388980555397)
          ·
            refine ⟨7482397024108947933854137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39906117461914388980555397 7482397024108947933854137)
            ·
              refine ⟨5611797768081710950390603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7482397024108947933854137 5611797768081710950390603)
              ·
                refine ⟨8417696652122566425585905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611797768081710950390603 8417696652122566425585905)
                ·
                  refine ⟨6313272489091924819189429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8417696652122566425585905 6313272489091924819189429)
                  ·
                    refine ⟨591869295852367951799009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6313272489091924819189429 591869295852367951799009)
                    ·
                      rfl

theorem cell23_3457984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_3457984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457984 prefixEnd_3457984 := by exact prefixLift 3457984
  have htrace : WordTrace (prefixWord ++ tailWord_3457984) baseStart_3457984 baseEnd_3457984 := by
    simpa [prefixWord, tailWord_3457984, baseEnd_3457984] using wordTrace_append hprefix tailTrace_3457984
  have hstable : (prefixWord ++ tailWord_3457984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457984).length < 2 ^ (prefixWord ++ tailWord_3457984).sum := by decide
  have hdescent : baseEnd_3457984 < baseStart_3457984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457987 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 4]
def baseStart_3457987 : Nat := 118140960795 + 3457987 * 2 ^ 59
def prefixEnd_3457987 : Nat := 4983230072969 + 3 ^ 40 * 3457987 * 2
def baseEnd_3457987 : Nat := 1775609427999067343659513

theorem tailTrace_3457987 : CollatzResearch.WordTrace tailWord_3457987 prefixEnd_3457987 1775609427999067343659513 := by
  unfold tailWord_3457987
  simp only [CollatzResearch.WordTrace]
  refine ⟨126123147323311151006460215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84082098215540767337640143 126123147323311151006460215)
  ·
    refine ⟨189184720984966726509690323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126123147323311151006460215 189184720984966726509690323)
    ·
      refine ⟨283777081477450089764535485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189184720984966726509690323 283777081477450089764535485)
      ·
        refine ⟨106416405554043783661700807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283777081477450089764535485 106416405554043783661700807)
        ·
          refine ⟨159624608331065675492551211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106416405554043783661700807 159624608331065675492551211)
          ·
            refine ⟨239436912496598513238826817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159624608331065675492551211 239436912496598513238826817)
            ·
              refine ⟨179577684372448884929120113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239436912496598513238826817 179577684372448884929120113)
              ·
                refine ⟨134683263279336663696840085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179577684372448884929120113 134683263279336663696840085)
                ·
                  refine ⟨6313277966218906110789379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134683263279336663696840085 6313277966218906110789379)
                  ·
                    refine ⟨9469916949328359166184069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313277966218906110789379 9469916949328359166184069)
                    ·
                      refine ⟨1775609427999067343659513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9469916949328359166184069 1775609427999067343659513)
                      ·
                        rfl

theorem cell23_3457987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_3457987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3457987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3457987 prefixEnd_3457987 := by exact prefixLift 3457987
  have htrace : WordTrace (prefixWord ++ tailWord_3457987) baseStart_3457987 baseEnd_3457987 := by
    simpa [prefixWord, tailWord_3457987, baseEnd_3457987] using wordTrace_append hprefix tailTrace_3457987
  have hstable : (prefixWord ++ tailWord_3457987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457987).length < 2 ^ (prefixWord ++ tailWord_3457987).sum := by decide
  have hdescent : baseEnd_3457987 < baseStart_3457987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458005 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 5]
def baseStart_3458005 : Nat := 118140960795 + 3458005 * 2 ^ 59
def prefixEnd_3458005 : Nat := 4983230072969 + 3 ^ 40 * 3458005 * 2
def baseEnd_3458005 : Nat := 197290963405649808137159

theorem tailTrace_3458005 : CollatzResearch.WordTrace tailWord_3458005 prefixEnd_3458005 197290963405649808137159 := by
  unfold tailWord_3458005
  simp only [CollatzResearch.WordTrace]
  refine ⟨126123803837245940080615469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84082535891497293387076979 126123803837245940080615469)
  ·
    refine ⟨47296426438967227530230801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126123803837245940080615469 47296426438967227530230801)
    ·
      refine ⟨35472319829225420647673101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47296426438967227530230801 35472319829225420647673101)
      ·
        refine ⟨13302119935959532742877413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35472319829225420647673101 13302119935959532742877413)
        ·
          refine ⟨2494147487992412389289515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13302119935959532742877413 2494147487992412389289515)
          ·
            refine ⟨3741221231988618583934273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494147487992412389289515 3741221231988618583934273)
            ·
              refine ⟨2805915923991463937950705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3741221231988618583934273 2805915923991463937950705)
              ·
                refine ⟨2104436942993597953463029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805915923991463937950705 2104436942993597953463029)
                ·
                  refine ⟨197290963405649808137159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2104436942993597953463029 197290963405649808137159)
                  ·
                    rfl

theorem cell23_3458005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_3458005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458005 prefixEnd_3458005 := by exact prefixLift 3458005
  have htrace : WordTrace (prefixWord ++ tailWord_3458005) baseStart_3458005 baseEnd_3458005 := by
    simpa [prefixWord, tailWord_3458005, baseEnd_3458005] using wordTrace_append hprefix tailTrace_3458005
  have hstable : (prefixWord ++ tailWord_3458005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458005).length < 2 ^ (prefixWord ++ tailWord_3458005).sum := by decide
  have hdescent : baseEnd_3458005 < baseStart_3458005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458017 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3458017 : Nat := 118140960795 + 3458017 * 2 ^ 59
def prefixEnd_3458017 : Nat := 4983230072969 + 3 ^ 40 * 3458017 * 2
def baseEnd_3458017 : Nat := 1775624832418702226284375

theorem tailTrace_3458017 : CollatzResearch.WordTrace tailWord_3458017 prefixEnd_3458017 1775624832418702226284375 := by
  unfold tailWord_3458017
  simp only [CollatzResearch.WordTrace]
  refine ⟨126124241513202466130052305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84082827675468310753368203 126124241513202466130052305)
  ·
    refine ⟨94593181134901849597539229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126124241513202466130052305 94593181134901849597539229)
    ·
      refine ⟨35472442925588193599077211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94593181134901849597539229 35472442925588193599077211)
      ·
        refine ⟨53208664388382290398615817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35472442925588193599077211 53208664388382290398615817)
        ·
          refine ⟨39906498291286717798961863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53208664388382290398615817 39906498291286717798961863)
          ·
            refine ⟨59859747436930076698442795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39906498291286717798961863 59859747436930076698442795)
            ·
              refine ⟨89789621155395115047664193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59859747436930076698442795 89789621155395115047664193)
              ·
                refine ⟨67342215866546336285748145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89789621155395115047664193 67342215866546336285748145)
                ·
                  refine ⟨50506661899909752214311109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67342215866546336285748145 50506661899909752214311109)
                  ·
                    refine ⟨9469999106233078540183333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50506661899909752214311109 9469999106233078540183333)
                    ·
                      refine ⟨1775624832418702226284375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9469999106233078540183333 1775624832418702226284375)
                      ·
                        rfl

theorem cell23_3458017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3458017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458017 prefixEnd_3458017 := by exact prefixLift 3458017
  have htrace : WordTrace (prefixWord ++ tailWord_3458017) baseStart_3458017 baseEnd_3458017 := by
    simpa [prefixWord, tailWord_3458017, baseEnd_3458017] using wordTrace_append hprefix tailTrace_3458017
  have hstable : (prefixWord ++ tailWord_3458017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458017).length < 2 ^ (prefixWord ++ tailWord_3458017).sum := by decide
  have hdescent : baseEnd_3458017 < baseStart_3458017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458024 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3458024 : Nat := 118140960795 + 3458024 * 2 ^ 59
def prefixEnd_3458024 : Nat := 4983230072969 + 3 ^ 40 * 3458024 * 2
def baseEnd_3458024 : Nat := 1775628426783283698896843

theorem tailTrace_3458024 : CollatzResearch.WordTrace tailWord_3458024 prefixEnd_3458024 1775628426783283698896843 := by
  unfold tailWord_3458024
  simp only [CollatzResearch.WordTrace]
  refine ⟨63062248412088553162778563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84082997882784737550371417 63062248412088553162778563)
  ·
    refine ⟨94593372618132829744167845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63062248412088553162778563 94593372618132829744167845)
    ·
      refine ⟨17736257365899905577031471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94593372618132829744167845 17736257365899905577031471)
      ·
        refine ⟨26604386048849858365547207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17736257365899905577031471 26604386048849858365547207)
        ·
          refine ⟨39906579073274787548320811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26604386048849858365547207 39906579073274787548320811)
          ·
            refine ⟨59859868609912181322481217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39906579073274787548320811 59859868609912181322481217)
            ·
              refine ⟨44894901457434135991860913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59859868609912181322481217 44894901457434135991860913)
              ·
                refine ⟨33671176093075601993895685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44894901457434135991860913 33671176093075601993895685)
                ·
                  refine ⟨6313345517451675373855441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33671176093075601993895685 6313345517451675373855441)
                  ·
                    refine ⟨4735009138088756530391581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6313345517451675373855441 4735009138088756530391581)
                    ·
                      refine ⟨1775628426783283698896843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735009138088756530391581 1775628426783283698896843)
                      ·
                        rfl

theorem cell23_3458024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3458024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458024 prefixEnd_3458024 := by exact prefixLift 3458024
  have htrace : WordTrace (prefixWord ++ tailWord_3458024) baseStart_3458024 baseEnd_3458024 := by
    simpa [prefixWord, tailWord_3458024, baseEnd_3458024] using wordTrace_append hprefix tailTrace_3458024
  have hstable : (prefixWord ++ tailWord_3458024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458024).length < 2 ^ (prefixWord ++ tailWord_3458024).sum := by decide
  have hdescent : baseEnd_3458024 < baseStart_3458024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458038 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3458038 : Nat := 118140960795 + 3458038 * 2 ^ 59
def prefixEnd_3458038 : Nat := 4983230072969 + 3 ^ 40 * 3458038 * 2
def baseEnd_3458038 : Nat := 1775635615512446644121779

theorem tailTrace_3458038 : CollatzResearch.WordTrace tailWord_3458038 prefixEnd_3458038 1775635615512446644121779 := by
  unfold tailWord_3458038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882812965382899169785423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84083338297417591144377845 7882812965382899169785423)
  ·
    refine ⟨11824219448074348754678135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7882812965382899169785423 11824219448074348754678135)
    ·
      refine ⟨17736329172111523132017203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824219448074348754678135 17736329172111523132017203)
      ·
        refine ⟨26604493758167284698025805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17736329172111523132017203 26604493758167284698025805)
        ·
          refine ⟨9976685159312731761759677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26604493758167284698025805 9976685159312731761759677)
          ·
            refine ⟨3741256934742274410659879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9976685159312731761759677 3741256934742274410659879)
            ·
              refine ⟨5611885402113411615989819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741256934742274410659879 5611885402113411615989819)
              ·
                refine ⟨8417828103170117423984729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611885402113411615989819 8417828103170117423984729)
                ·
                  refine ⟨6313371077377588067988547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8417828103170117423984729 6313371077377588067988547)
                  ·
                    refine ⟨9470056616066382101982821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313371077377588067988547 9470056616066382101982821)
                    ·
                      refine ⟨1775635615512446644121779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9470056616066382101982821 1775635615512446644121779)
                      ·
                        rfl

theorem cell23_3458038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3458038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458038 prefixEnd_3458038 := by exact prefixLift 3458038
  have htrace : WordTrace (prefixWord ++ tailWord_3458038) baseStart_3458038 baseEnd_3458038 := by
    simpa [prefixWord, tailWord_3458038, baseEnd_3458038] using wordTrace_append hprefix tailTrace_3458038
  have hstable : (prefixWord ++ tailWord_3458038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458038).length < 2 ^ (prefixWord ++ tailWord_3458038).sum := by decide
  have hdescent : baseEnd_3458038 < baseStart_3458038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458064 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 5, 5, 2]
def baseStart_3458064 : Nat := 118140960795 + 3458064 * 2 ^ 59
def prefixEnd_3458064 : Nat := 4983230072969 + 3 ^ 40 * 3458064 * 2
def baseEnd_3458064 : Nat := 1775648966009463542396659

theorem tailTrace_3458064 : CollatzResearch.WordTrace tailWord_3458064 prefixEnd_3458064 1775648966009463542396659 := by
  unfold tailWord_3458064
  simp only [CollatzResearch.WordTrace]
  refine ⟨63062977872016096578506623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84083970496021462104675497 63062977872016096578506623)
  ·
    refine ⟨94594466808024144867759935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63062977872016096578506623 94594466808024144867759935)
    ·
      refine ⟨141891700212036217301639903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94594466808024144867759935 141891700212036217301639903)
      ·
        refine ⟨212837550318054325952459855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141891700212036217301639903 212837550318054325952459855)
        ·
          refine ⟨319256325477081488928689783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212837550318054325952459855 319256325477081488928689783)
          ·
            refine ⟨478884488215622233393034675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319256325477081488928689783 478884488215622233393034675)
            ·
              refine ⟨718326732323433350089552013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478884488215622233393034675 718326732323433350089552013)
              ·
                refine ⟨269372524621287506283582005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718326732323433350089552013 269372524621287506283582005)
                ·
                  refine ⟨25253674183245703714085813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269372524621287506283582005 25253674183245703714085813)
                  ·
                    refine ⟨2367531954679284723195545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25253674183245703714085813 2367531954679284723195545)
                    ·
                      refine ⟨1775648966009463542396659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367531954679284723195545 1775648966009463542396659)
                      ·
                        rfl

theorem cell23_3458064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 5, 2].length) (baseStart_3458064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458064 prefixEnd_3458064 := by exact prefixLift 3458064
  have htrace : WordTrace (prefixWord ++ tailWord_3458064) baseStart_3458064 baseEnd_3458064 := by
    simpa [prefixWord, tailWord_3458064, baseEnd_3458064] using wordTrace_append hprefix tailTrace_3458064
  have hstable : (prefixWord ++ tailWord_3458064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458064).length < 2 ^ (prefixWord ++ tailWord_3458064).sum := by decide
  have hdescent : baseEnd_3458064 < baseStart_3458064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458081 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_3458081 : Nat := 118140960795 + 3458081 * 2 ^ 59
def prefixEnd_3458081 : Nat := 4983230072969 + 3 ^ 40 * 3458081 * 2
def baseEnd_3458081 : Nat := 1775657695180589975884081

theorem tailTrace_3458081 : CollatzResearch.WordTrace tailWord_3458081 prefixEnd_3458081 1775657695180589975884081 := by
  unfold tailWord_3458081
  simp only [CollatzResearch.WordTrace]
  refine ⟨126126575784970605060382097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84084383856647070040254731 126126575784970605060382097)
  ·
    refine ⟨94594931838727953795286573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126126575784970605060382097 94594931838727953795286573)
    ·
      refine ⟨35473099439522982673232465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94594931838727953795286573 35473099439522982673232465)
      ·
        refine ⟨26604824579642237004924349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35473099439522982673232465 26604824579642237004924349)
        ·
          refine ⟨9976809217365838876846631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26604824579642237004924349 9976809217365838876846631)
          ·
            refine ⟨14965213826048758315269947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976809217365838876846631 14965213826048758315269947)
            ·
              refine ⟨22447820739073137472904921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14965213826048758315269947 22447820739073137472904921)
              ·
                refine ⟨16835865554304853104678691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22447820739073137472904921 16835865554304853104678691)
                ·
                  refine ⟨25253798331457279657018037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16835865554304853104678691 25253798331457279657018037)
                  ·
                    refine ⟨2367543593574119967845441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25253798331457279657018037 2367543593574119967845441)
                    ·
                      refine ⟨1775657695180589975884081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367543593574119967845441 1775657695180589975884081)
                      ·
                        rfl

theorem cell23_3458081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_3458081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458081 prefixEnd_3458081 := by exact prefixLift 3458081
  have htrace : WordTrace (prefixWord ++ tailWord_3458081) baseStart_3458081 baseEnd_3458081 := by
    simpa [prefixWord, tailWord_3458081, baseEnd_3458081] using wordTrace_append hprefix tailTrace_3458081
  have hstable : (prefixWord ++ tailWord_3458081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458081).length < 2 ^ (prefixWord ++ tailWord_3458081).sum := by decide
  have hdescent : baseEnd_3458081 < baseStart_3458081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458105 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3458105 : Nat := 118140960795 + 3458105 * 2 ^ 59
def prefixEnd_3458105 : Nat := 4983230072969 + 3 ^ 40 * 3458105 * 2
def baseEnd_3458105 : Nat := 1775670018716297881983971

theorem tailTrace_3458105 : CollatzResearch.WordTrace tailWord_3458105 prefixEnd_3458105 1775670018716297881983971 := by
  unfold tailWord_3458105
  simp only [CollatzResearch.WordTrace]
  refine ⟨126127451136883657159255769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84084967424589104772837179 126127451136883657159255769)
  ·
    refine ⟨94595588352662742869441827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126127451136883657159255769 94595588352662742869441827)
    ·
      refine ⟨141893382528994114304162741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94595588352662742869441827 141893382528994114304162741)
      ·
        refine ⟨13302504612093198216015257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141893382528994114304162741 13302504612093198216015257)
        ·
          refine ⟨9976878459069898662011443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13302504612093198216015257 9976878459069898662011443)
          ·
            refine ⟨14965317688604847993017165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976878459069898662011443 14965317688604847993017165)
            ·
              refine ⟨5611994133226817997381437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14965317688604847993017165 5611994133226817997381437)
              ·
                refine ⟨2104497799960056749018039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5611994133226817997381437 2104497799960056749018039)
                ·
                  refine ⟨3156746699940085123527059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104497799960056749018039 3156746699940085123527059)
                  ·
                    refine ⟨4735120049910127685290589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156746699940085123527059 4735120049910127685290589)
                    ·
                      refine ⟨1775670018716297881983971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735120049910127685290589 1775670018716297881983971)
                      ·
                        rfl

theorem cell23_3458105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3458105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458105 prefixEnd_3458105 := by exact prefixLift 3458105
  have htrace : WordTrace (prefixWord ++ tailWord_3458105) baseStart_3458105 baseEnd_3458105 := by
    simpa [prefixWord, tailWord_3458105, baseEnd_3458105] using wordTrace_append hprefix tailTrace_3458105
  have hstable : (prefixWord ++ tailWord_3458105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458105).length < 2 ^ (prefixWord ++ tailWord_3458105).sum := by decide
  have hdescent : baseEnd_3458105 < baseStart_3458105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_3458107 : Nat := 118140960795 + 3458107 * 2 ^ 59
def prefixEnd_3458107 : Nat := 4983230072969 + 3 ^ 40 * 3458107 * 2
def baseEnd_3458107 : Nat := 1775671045677606874158961

theorem tailTrace_3458107 : CollatzResearch.WordTrace tailWord_3458107 prefixEnd_3458107 1775671045677606874158961 := by
  unfold tailWord_3458107
  simp only [CollatzResearch.WordTrace]
  refine ⟨126127524082876411500828575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84085016055250941000552383 126127524082876411500828575)
  ·
    refine ⟨189191286124314617251242863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126127524082876411500828575 189191286124314617251242863)
    ·
      refine ⟨283786929186471925876864295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189191286124314617251242863 283786929186471925876864295)
      ·
        refine ⟨425680393779707888815296443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283786929186471925876864295 425680393779707888815296443)
        ·
          refine ⟨638520590669561833222944665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425680393779707888815296443 638520590669561833222944665)
          ·
            refine ⟨478890443002171374917208499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638520590669561833222944665 478890443002171374917208499)
            ·
              refine ⟨718335664503257062375812749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478890443002171374917208499 718335664503257062375812749)
              ·
                refine ⟨269375874188721398390929781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718335664503257062375812749 269375874188721398390929781)
                ·
                  refine ⟨25253988205192631099149667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269375874188721398390929781 25253988205192631099149667)
                  ·
                    refine ⟨37880982307788946648724501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25253988205192631099149667 37880982307788946648724501)
                    ·
                      refine ⟨1775671045677606874158961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37880982307788946648724501 1775671045677606874158961)
                      ·
                        rfl

theorem cell23_3458107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_3458107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458107 prefixEnd_3458107 := by exact prefixLift 3458107
  have htrace : WordTrace (prefixWord ++ tailWord_3458107) baseStart_3458107 baseEnd_3458107 := by
    simpa [prefixWord, tailWord_3458107, baseEnd_3458107] using wordTrace_append hprefix tailTrace_3458107
  have hstable : (prefixWord ++ tailWord_3458107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458107).length < 2 ^ (prefixWord ++ tailWord_3458107).sum := by decide
  have hdescent : baseEnd_3458107 < baseStart_3458107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458117 : List Nat := [1, 3, 1, 1, 1, 3, 13]
def baseStart_3458117 : Nat := 118140960795 + 3458117 * 2 ^ 59
def prefixEnd_3458117 : Nat := 4983230072969 + 3 ^ 40 * 3458117 * 2
def baseEnd_3458117 : Nat := 21921928154125331296715

theorem tailTrace_3458117 : CollatzResearch.WordTrace tailWord_3458117 prefixEnd_3458117 21921928154125331296715 := by
  unfold tailWord_3458117
  simp only [CollatzResearch.WordTrace]
  refine ⟨126127888812840183208692605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84085259208560122139128403 126127888812840183208692605)
  ·
    refine ⟨47297958304815068703259727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126127888812840183208692605 47297958304815068703259727)
    ·
      refine ⟨70946937457222603054889591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47297958304815068703259727 70946937457222603054889591)
      ·
        refine ⟨106420406185833904582334387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70946937457222603054889591 106420406185833904582334387)
        ·
          refine ⟨159630609278750856873501581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106420406185833904582334387 159630609278750856873501581)
          ·
            refine ⟨59861478479531571327563093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159630609278750856873501581 59861478479531571327563093)
            ·
              refine ⟨21921928154125331296715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 59861478479531571327563093 21921928154125331296715)
              ·
                rfl

theorem cell23_3458117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 13].length) (baseStart_3458117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458117 prefixEnd_3458117 := by exact prefixLift 3458117
  have htrace : WordTrace (prefixWord ++ tailWord_3458117) baseStart_3458117 baseEnd_3458117 := by
    simpa [prefixWord, tailWord_3458117, baseEnd_3458117] using wordTrace_append hprefix tailTrace_3458117
  have hstable : (prefixWord ++ tailWord_3458117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458117).length < 2 ^ (prefixWord ++ tailWord_3458117).sum := by decide
  have hdescent : baseEnd_3458117 < baseStart_3458117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458127 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_3458127 : Nat := 118140960795 + 3458127 * 2 ^ 59
def prefixEnd_3458127 : Nat := 4983230072969 + 3 ^ 40 * 3458127 * 2
def baseEnd_3458127 : Nat := 1775681315290696795908869

theorem tailTrace_3458127 : CollatzResearch.WordTrace tailWord_3458127 prefixEnd_3458127 1775681315290696795908869 := by
  unfold tailWord_3458127
  simp only [CollatzResearch.WordTrace]
  refine ⟨126128253542803954916556635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84085502361869303277704423 126128253542803954916556635)
  ·
    refine ⟨189192380314205932374834953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126128253542803954916556635 189192380314205932374834953)
    ·
      refine ⟨141894285235654449281126215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189192380314205932374834953 141894285235654449281126215)
      ·
        refine ⟨212841427853481673921689323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141894285235654449281126215 212841427853481673921689323)
        ·
          refine ⟨319262141780222510882533985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212841427853481673921689323 319262141780222510882533985)
          ·
            refine ⟨239446606335166883161900489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319262141780222510882533985 239446606335166883161900489)
            ·
              refine ⟨179584954751375162371425367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239446606335166883161900489 179584954751375162371425367)
              ·
                refine ⟨269377432127062743557138051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179584954751375162371425367 269377432127062743557138051)
                ·
                  refine ⟨404066148190594115335707077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269377432127062743557138051 404066148190594115335707077)
                  ·
                    refine ⟨75762402785736396625445077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404066148190594115335707077 75762402785736396625445077)
                    ·
                      refine ⟨1775681315290696795908869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75762402785736396625445077 1775681315290696795908869)
                      ·
                        rfl

theorem cell23_3458127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_3458127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458127 prefixEnd_3458127 := by exact prefixLift 3458127
  have htrace : WordTrace (prefixWord ++ tailWord_3458127) baseStart_3458127 baseEnd_3458127 := by
    simpa [prefixWord, tailWord_3458127, baseEnd_3458127] using wordTrace_append hprefix tailTrace_3458127
  have hstable : (prefixWord ++ tailWord_3458127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458127).length < 2 ^ (prefixWord ++ tailWord_3458127).sum := by decide
  have hdescent : baseEnd_3458127 < baseStart_3458127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458142 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3458142 : Nat := 118140960795 + 3458142 * 2 ^ 59
def prefixEnd_3458142 : Nat := 4983230072969 + 3 ^ 40 * 3458142 * 2
def baseEnd_3458142 : Nat := 591896339166838079073767

theorem tailTrace_3458142 : CollatzResearch.WordTrace tailWord_3458142 prefixEnd_3458142 591896339166838079073767 := by
  unfold tailWord_3458142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766100079718701559794085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84085867091833074985568453 15766100079718701559794085)
  ·
    refine ⟨2956143764947256542461391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15766100079718701559794085 2956143764947256542461391)
    ·
      refine ⟨4434215647420884813692087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956143764947256542461391 4434215647420884813692087)
      ·
        refine ⟨6651323471131327220538131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434215647420884813692087 6651323471131327220538131)
        ·
          refine ⟨9976985206696990830807197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6651323471131327220538131 9976985206696990830807197)
          ·
            refine ⟨3741369452511371561552699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9976985206696990830807197 3741369452511371561552699)
            ·
              refine ⟨5612054178767057342329049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741369452511371561552699 5612054178767057342329049)
              ·
                refine ⟨4209040634075293006746787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5612054178767057342329049 4209040634075293006746787)
                ·
                  refine ⟨6313560951112939510120181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209040634075293006746787 6313560951112939510120181)
                  ·
                    refine ⟨591896339166838079073767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6313560951112939510120181 591896339166838079073767)
                    ·
                      rfl

theorem cell23_3458142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3458142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458142 prefixEnd_3458142 := by exact prefixLift 3458142
  have htrace : WordTrace (prefixWord ++ tailWord_3458142) baseStart_3458142 baseEnd_3458142 := by
    simpa [prefixWord, tailWord_3458142, baseEnd_3458142] using wordTrace_append hprefix tailTrace_3458142
  have hstable : (prefixWord ++ tailWord_3458142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458142).length < 2 ^ (prefixWord ++ tailWord_3458142).sum := by decide
  have hdescent : baseEnd_3458142 < baseStart_3458142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458161 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_3458161 : Nat := 118140960795 + 3458161 * 2 ^ 59
def prefixEnd_3458161 : Nat := 4983230072969 + 3 ^ 40 * 3458161 * 2
def baseEnd_3458161 : Nat := 1775698773632949662883713

theorem tailTrace_3458161 : CollatzResearch.WordTrace tailWord_3458161 prefixEnd_3458161 1775698773632949662883713 := by
  unfold tailWord_3458161
  simp only [CollatzResearch.WordTrace]
  refine ⟨126129493624680778723294337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84086329083120519148862891 126129493624680778723294337)
  ·
    refine ⟨94597120218510584042470753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126129493624680778723294337 94597120218510584042470753)
    ·
      refine ⟨70947840163882938031853065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94597120218510584042470753 70947840163882938031853065)
      ·
        refine ⟨53210880122912203523889799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70947840163882938031853065 53210880122912203523889799)
        ·
          refine ⟨79816320184368305285834699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53210880122912203523889799 79816320184368305285834699)
          ·
            refine ⟨119724480276552457928752049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79816320184368305285834699 119724480276552457928752049)
            ·
              refine ⟨89793360207414343446564037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119724480276552457928752049 89793360207414343446564037)
              ·
                refine ⟨16836255038890189396230757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89793360207414343446564037 16836255038890189396230757)
                ·
                  refine ⟨3156797819791910511793267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16836255038890189396230757 3156797819791910511793267)
                  ·
                    refine ⟨4735196729687865767689901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156797819791910511793267 4735196729687865767689901)
                    ·
                      refine ⟨1775698773632949662883713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735196729687865767689901 1775698773632949662883713)
                      ·
                        rfl

theorem cell23_3458161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_3458161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458161 prefixEnd_3458161 := by exact prefixLift 3458161
  have htrace : WordTrace (prefixWord ++ tailWord_3458161) baseStart_3458161 baseEnd_3458161 := by
    simpa [prefixWord, tailWord_3458161, baseEnd_3458161] using wordTrace_append hprefix tailTrace_3458161
  have hstable : (prefixWord ++ tailWord_3458161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458161).length < 2 ^ (prefixWord ++ tailWord_3458161).sum := by decide
  have hdescent : baseEnd_3458161 < baseStart_3458161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458165 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3458165 : Nat := 118140960795 + 3458165 * 2 ^ 59
def prefixEnd_3458165 : Nat := 4983230072969 + 3 ^ 40 * 3458165 * 2
def baseEnd_3458165 : Nat := 1775700827555567647233695

theorem tailTrace_3458165 : CollatzResearch.WordTrace tailWord_3458165 prefixEnd_3458165 1775700827555567647233695 := by
  unfold tailWord_3458165
  simp only [CollatzResearch.WordTrace]
  refine ⟨126129639516666287406439949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84086426344444191604293299 126129639516666287406439949)
  ·
    refine ⟨47298614818749857777414981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126129639516666287406439949 47298614818749857777414981)
    ·
      refine ⟨8868490278515598333265309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47298614818749857777414981 8868490278515598333265309)
      ·
        refine ⟨3325683854443349374974491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8868490278515598333265309 3325683854443349374974491)
        ·
          refine ⟨4988525781665024062461737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325683854443349374974491 4988525781665024062461737)
          ·
            refine ⟨3741394336248768046846303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4988525781665024062461737 3741394336248768046846303)
            ·
              refine ⟨5612091504373152070269455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741394336248768046846303 5612091504373152070269455)
              ·
                refine ⟨8418137256559728105404183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612091504373152070269455 8418137256559728105404183)
                ·
                  refine ⟨12627205884839592158106275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418137256559728105404183 12627205884839592158106275)
                  ·
                    refine ⟨18940808827259388237159413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12627205884839592158106275 18940808827259388237159413)
                    ·
                      refine ⟨1775700827555567647233695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18940808827259388237159413 1775700827555567647233695)
                      ·
                        rfl

theorem cell23_3458165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3458165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458165 prefixEnd_3458165 := by exact prefixLift 3458165
  have htrace : WordTrace (prefixWord ++ tailWord_3458165) baseStart_3458165 baseEnd_3458165 := by
    simpa [prefixWord, tailWord_3458165, baseEnd_3458165] using wordTrace_append hprefix tailTrace_3458165
  have hstable : (prefixWord ++ tailWord_3458165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458165).length < 2 ^ (prefixWord ++ tailWord_3458165).sum := by decide
  have hdescent : baseEnd_3458165 < baseStart_3458165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458246 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3458246 : Nat := 118140960795 + 3458246 * 2 ^ 59
def prefixEnd_3458246 : Nat := 4983230072969 + 3 ^ 40 * 3458246 * 2
def baseEnd_3458246 : Nat := 1775742419488581830320823

theorem tailTrace_3458246 : CollatzResearch.WordTrace tailWord_3458246 prefixEnd_3458246 1775742419488581830320823 := by
  unfold tailWord_3458246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941643557167901195004331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84088395886248558826759061 3941643557167901195004331)
  ·
    refine ⟨5912465335751851792506497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3941643557167901195004331 5912465335751851792506497)
    ·
      refine ⟨4434349001813888844379873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5912465335751851792506497 4434349001813888844379873)
      ·
        refine ⟨3325761751360416633284905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434349001813888844379873 3325761751360416633284905)
        ·
          refine ⟨2494321313520312474963679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3325761751360416633284905 2494321313520312474963679)
          ·
            refine ⟨3741481970280468712445519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494321313520312474963679 3741481970280468712445519)
            ·
              refine ⟨5612222955420703068668279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741481970280468712445519 5612222955420703068668279)
              ·
                refine ⟨8418334433131054603002419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612222955420703068668279 8418334433131054603002419)
                ·
                  refine ⟨12627501649696581904503629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418334433131054603002419 12627501649696581904503629)
                  ·
                    refine ⟨4735313118636218214188861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12627501649696581904503629 4735313118636218214188861)
                    ·
                      refine ⟨1775742419488581830320823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735313118636218214188861 1775742419488581830320823)
                      ·
                        rfl

theorem cell23_3458246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3458246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458246 prefixEnd_3458246 := by exact prefixLift 3458246
  have htrace : WordTrace (prefixWord ++ tailWord_3458246) baseStart_3458246 baseEnd_3458246 := by
    simpa [prefixWord, tailWord_3458246, baseEnd_3458246] using wordTrace_append hprefix tailTrace_3458246
  have hstable : (prefixWord ++ tailWord_3458246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458246).length < 2 ^ (prefixWord ++ tailWord_3458246).sum := by decide
  have hdescent : baseEnd_3458246 < baseStart_3458246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458291 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 4]
def baseStart_3458291 : Nat := 118140960795 + 3458291 * 2 ^ 59
def prefixEnd_3458291 : Nat := 4983230072969 + 3 ^ 40 * 3458291 * 2
def baseEnd_3458291 : Nat := 1775765526118034154258115

theorem tailTrace_3458291 : CollatzResearch.WordTrace tailWord_3458291 prefixEnd_3458291 1775765526118034154258115 := by
  unfold tailWord_3458291
  simp only [CollatzResearch.WordTrace]
  refine ⟨126134235114209810925526727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84089490076139873950351151 126134235114209810925526727)
  ·
    refine ⟨189201352671314716388290091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126134235114209810925526727 189201352671314716388290091)
    ·
      refine ⟨283802029006972074582435137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189201352671314716388290091 283802029006972074582435137)
      ·
        refine ⟨212851521755229055936826353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283802029006972074582435137 212851521755229055936826353)
        ·
          refine ⟨159638641316421791952619765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212851521755229055936826353 159638641316421791952619765)
          ·
            refine ⟨14966122623414542995558103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159638641316421791952619765 14966122623414542995558103)
            ·
              refine ⟨22449183935121814493337155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14966122623414542995558103 22449183935121814493337155)
              ·
                refine ⟨33673775902682721740005733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22449183935121814493337155 33673775902682721740005733)
                ·
                  refine ⟨6313832981753010326251075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33673775902682721740005733 6313832981753010326251075)
                  ·
                    refine ⟨9470749472629515489376613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313832981753010326251075 9470749472629515489376613)
                    ·
                      refine ⟨1775765526118034154258115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9470749472629515489376613 1775765526118034154258115)
                      ·
                        rfl

theorem cell23_3458291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_3458291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458291 prefixEnd_3458291 := by exact prefixLift 3458291
  have htrace : WordTrace (prefixWord ++ tailWord_3458291) baseStart_3458291 baseEnd_3458291 := by
    simpa [prefixWord, tailWord_3458291, baseEnd_3458291] using wordTrace_append hprefix tailTrace_3458291
  have hstable : (prefixWord ++ tailWord_3458291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458291).length < 2 ^ (prefixWord ++ tailWord_3458291).sum := by decide
  have hdescent : baseEnd_3458291 < baseStart_3458291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458322 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3458322 : Nat := 118140960795 + 3458322 * 2 ^ 59
def prefixEnd_3458322 : Nat := 4983230072969 + 3 ^ 40 * 3458322 * 2
def baseEnd_3458322 : Nat := 591927148006107844323491

theorem tailTrace_3458322 : CollatzResearch.WordTrace tailWord_3458322 prefixEnd_3458322 591927148006107844323491 := by
  unfold tailWord_3458322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31533841444274375804976305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84090243851398335479936813 31533841444274375804976305)
  ·
    refine ⟨23650381083205781853732229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31533841444274375804976305 23650381083205781853732229)
    ·
      refine ⟨4434446453101084097574793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23650381083205781853732229 4434446453101084097574793)
      ·
        refine ⟨3325834839825813073181095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434446453101084097574793 3325834839825813073181095)
        ·
          refine ⟨4988752259738719609771643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325834839825813073181095 4988752259738719609771643)
          ·
            refine ⟨7483128389608079414657465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988752259738719609771643 7483128389608079414657465)
            ·
              refine ⟨5612346292206059560993099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7483128389608079414657465 5612346292206059560993099)
              ·
                refine ⟨8418519438309089341489649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612346292206059560993099 8418519438309089341489649)
                ·
                  refine ⟨6313889578731817006117237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8418519438309089341489649 6313889578731817006117237)
                  ·
                    refine ⟨591927148006107844323491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6313889578731817006117237 591927148006107844323491)
                    ·
                      rfl

theorem cell23_3458322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3458322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458322 prefixEnd_3458322 := by exact prefixLift 3458322
  have htrace : WordTrace (prefixWord ++ tailWord_3458322) baseStart_3458322 baseEnd_3458322 := by
    simpa [prefixWord, tailWord_3458322, baseEnd_3458322] using wordTrace_append hprefix tailTrace_3458322
  have hstable : (prefixWord ++ tailWord_3458322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458322).length < 2 ^ (prefixWord ++ tailWord_3458322).sum := by decide
  have hdescent : baseEnd_3458322 < baseStart_3458322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458328 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3458328 : Nat := 118140960795 + 3458328 * 2 ^ 59
def prefixEnd_3458328 : Nat := 4983230072969 + 3 ^ 40 * 3458328 * 2
def baseEnd_3458328 : Nat := 1775784524902250509495445

theorem tailTrace_3458328 : CollatzResearch.WordTrace tailWord_3458328 prefixEnd_3458328 1775784524902250509495445 := by
  unfold tailWord_3458328
  simp only [CollatzResearch.WordTrace]
  refine ⟨63067792307537883122311819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84090389743383844163082425 63067792307537883122311819)
  ·
    refine ⟨94601688461306824683467729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63067792307537883122311819 94601688461306824683467729)
    ·
      refine ⟨70951266345980118512600797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94601688461306824683467729 70951266345980118512600797)
      ·
        refine ⟨26606724879742544442225299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70951266345980118512600797 26606724879742544442225299)
        ·
          refine ⟨39910087319613816663337949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26606724879742544442225299 39910087319613816663337949)
          ·
            refine ⟨14966282744855181248751731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39910087319613816663337949 14966282744855181248751731)
            ·
              refine ⟨22449424117282771873127597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14966282744855181248751731 22449424117282771873127597)
              ·
                refine ⟨8418534043981039452422849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22449424117282771873127597 8418534043981039452422849)
                ·
                  refine ⟨6313900532985779589317137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8418534043981039452422849 6313900532985779589317137)
                  ·
                    refine ⟨4735425399739334691987853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6313900532985779589317137 4735425399739334691987853)
                    ·
                      refine ⟨1775784524902250509495445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735425399739334691987853 1775784524902250509495445)
                      ·
                        rfl

theorem cell23_3458328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3458328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458328 prefixEnd_3458328 := by exact prefixLift 3458328
  have htrace : WordTrace (prefixWord ++ tailWord_3458328) baseStart_3458328 baseEnd_3458328 := by
    simpa [prefixWord, tailWord_3458328, baseEnd_3458328] using wordTrace_append hprefix tailTrace_3458328
  have hstable : (prefixWord ++ tailWord_3458328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458328).length < 2 ^ (prefixWord ++ tailWord_3458328).sum := by decide
  have hdescent : baseEnd_3458328 < baseStart_3458328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458368 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 1, 5, 2]
def baseStart_3458368 : Nat := 118140960795 + 3458368 * 2 ^ 59
def prefixEnd_3458368 : Nat := 4983230072969 + 3 ^ 40 * 3458368 * 2
def baseEnd_3458368 : Nat := 1775805064128430352995261

theorem tailTrace_3458368 : CollatzResearch.WordTrace tailWord_3458368 prefixEnd_3458368 1775805064128430352995261 := by
  unfold tailWord_3458368
  simp only [CollatzResearch.WordTrace]
  refine ⟨63068521767465426538039879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84091362356620568717386505 63068521767465426538039879)
  ·
    refine ⟨94602782651198139807059819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63068521767465426538039879 94602782651198139807059819)
    ·
      refine ⟨141904173976797209710589729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94602782651198139807059819 141904173976797209710589729)
      ·
        refine ⟨106428130482597907282942297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141904173976797209710589729 106428130482597907282942297)
        ·
          refine ⟨79821097861948430462206723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106428130482597907282942297 79821097861948430462206723)
          ·
            refine ⟨119731646792922645693310085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79821097861948430462206723 119731646792922645693310085)
            ·
              refine ⟨22449683773672996067495641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119731646792922645693310085 22449683773672996067495641)
              ·
                refine ⟨16837262830254747050621731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22449683773672996067495641 16837262830254747050621731)
                ·
                  refine ⟨25255894245382120575932597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16837262830254747050621731 25255894245382120575932597)
                  ·
                    refine ⟨2367740085504573803993681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25255894245382120575932597 2367740085504573803993681)
                    ·
                      refine ⟨1775805064128430352995261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367740085504573803993681 1775805064128430352995261)
                      ·
                        rfl

theorem cell23_3458368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_3458368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458368 prefixEnd_3458368 := by exact prefixLift 3458368
  have htrace : WordTrace (prefixWord ++ tailWord_3458368) baseStart_3458368 baseEnd_3458368 := by
    simpa [prefixWord, tailWord_3458368, baseEnd_3458368] using wordTrace_append hprefix tailTrace_3458368
  have hstable : (prefixWord ++ tailWord_3458368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458368).length < 2 ^ (prefixWord ++ tailWord_3458368).sum := by decide
  have hdescent : baseEnd_3458368 < baseStart_3458368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458375 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_3458375 : Nat := 118140960795 + 3458375 * 2 ^ 59
def prefixEnd_3458375 : Nat := 4983230072969 + 3 ^ 40 * 3458375 * 2
def baseEnd_3458375 : Nat := 1775808658493011825607729

theorem tailTrace_3458375 : CollatzResearch.WordTrace tailWord_3458375 prefixEnd_3458375 1775808658493011825607729 := by
  unfold tailWord_3458375
  simp only [CollatzResearch.WordTrace]
  refine ⟨126137298845905493271584579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84091532563936995514389719 126137298845905493271584579)
  ·
    refine ⟨189205948268858239907376869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126137298845905493271584579 189205948268858239907376869)
    ·
      refine ⟨35476115300410919982633163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189205948268858239907376869 35476115300410919982633163)
      ·
        refine ⟨53214172950616379973949745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35476115300410919982633163 53214172950616379973949745)
        ·
          refine ⟨39910629712962284980462309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53214172950616379973949745 39910629712962284980462309)
          ·
            refine ⟨7483243071180428433836683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39910629712962284980462309 7483243071180428433836683)
            ·
              refine ⟨11224864606770642650755025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483243071180428433836683 11224864606770642650755025)
              ·
                refine ⟨8418648455077981988066269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11224864606770642650755025 8418648455077981988066269)
                ·
                  refine ⟨3156993170654243245524851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8418648455077981988066269 3156993170654243245524851)
                  ·
                    refine ⟨4735489755981364868287277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156993170654243245524851 4735489755981364868287277)
                    ·
                      refine ⟨1775808658493011825607729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735489755981364868287277 1775808658493011825607729)
                      ·
                        rfl

theorem cell23_3458375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_3458375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458375 prefixEnd_3458375 := by exact prefixLift 3458375
  have htrace : WordTrace (prefixWord ++ tailWord_3458375) baseStart_3458375 baseEnd_3458375 := by
    simpa [prefixWord, tailWord_3458375, baseEnd_3458375] using wordTrace_append hprefix tailTrace_3458375
  have hstable : (prefixWord ++ tailWord_3458375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458375).length < 2 ^ (prefixWord ++ tailWord_3458375).sum := by decide
  have hdescent : baseEnd_3458375 < baseStart_3458375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458392 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 1, 1, 3]
def baseStart_3458392 : Nat := 118140960795 + 3458392 * 2 ^ 59
def prefixEnd_3458392 : Nat := 4983230072969 + 3 ^ 40 * 3458392 * 2
def baseEnd_3458392 : Nat := 1775817387664138259095151

theorem tailTrace_3458392 : CollatzResearch.WordTrace tailWord_3458392 prefixEnd_3458392 1775817387664138259095151 := by
  unfold tailWord_3458392
  simp only [CollatzResearch.WordTrace]
  refine ⟨63068959443421952587476715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84091945924562603449968953 63068959443421952587476715)
  ·
    refine ⟨94603439165132928881215073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63068959443421952587476715 94603439165132928881215073)
    ·
      refine ⟨70952579373849696660911305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94603439165132928881215073 70952579373849696660911305)
      ·
        refine ⟨53214434530387272495683479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70952579373849696660911305 53214434530387272495683479)
        ·
          refine ⟨79821651795580908743525219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53214434530387272495683479 79821651795580908743525219)
          ·
            refine ⟨119732477693371363115287829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79821651795580908743525219 119732477693371363115287829)
            ·
              refine ⟨5612459891876782646029117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119732477693371363115287829 5612459891876782646029117)
              ·
                refine ⟨2104672459453793492260919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5612459891876782646029117 2104672459453793492260919)
                ·
                  refine ⟨3157008689180690238391379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104672459453793492260919 3157008689180690238391379)
                  ·
                    refine ⟨4735513033771035357587069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3157008689180690238391379 4735513033771035357587069)
                    ·
                      refine ⟨1775817387664138259095151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735513033771035357587069 1775817387664138259095151)
                      ·
                        rfl

theorem cell23_3458392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_3458392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458392 prefixEnd_3458392 := by exact prefixLift 3458392
  have htrace : WordTrace (prefixWord ++ tailWord_3458392) baseStart_3458392 baseEnd_3458392 := by
    simpa [prefixWord, tailWord_3458392, baseEnd_3458392] using wordTrace_append hprefix tailTrace_3458392
  have hstable : (prefixWord ++ tailWord_3458392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458392).length < 2 ^ (prefixWord ++ tailWord_3458392).sum := by decide
  have hdescent : baseEnd_3458392 < baseStart_3458392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458401 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3458401 : Nat := 118140960795 + 3458401 * 2 ^ 59
def prefixEnd_3458401 : Nat := 4983230072969 + 3 ^ 40 * 3458401 * 2
def baseEnd_3458401 : Nat := 1775822008990028723882609

theorem tailTrace_3458401 : CollatzResearch.WordTrace tailWord_3458401 prefixEnd_3458401 1775822008990028723882609 := by
  unfold tailWord_3458401
  simp only [CollatzResearch.WordTrace]
  refine ⟨126138247143811299712031057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84092164762540866474687371 126138247143811299712031057)
  ·
    refine ⟨94603685357858474784023293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126138247143811299712031057 94603685357858474784023293)
    ·
      refine ⟨35476382009196928044008735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94603685357858474784023293 35476382009196928044008735)
      ·
        refine ⟨53214573013795392066013103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35476382009196928044008735 53214573013795392066013103)
        ·
          refine ⟨79821859520693088099019655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53214573013795392066013103 79821859520693088099019655)
          ·
            refine ⟨119732789281039632148529483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79821859520693088099019655 119732789281039632148529483)
            ·
              refine ⟨179599183921559448222794225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119732789281039632148529483 179599183921559448222794225)
              ·
                refine ⟨134699387941169586167095669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179599183921559448222794225 134699387941169586167095669)
                ·
                  refine ⟨12628067619484648703165219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134699387941169586167095669 12628067619484648703165219)
                  ·
                    refine ⟨18942101429226973054747829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12628067619484648703165219 18942101429226973054747829)
                    ·
                      refine ⟨1775822008990028723882609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18942101429226973054747829 1775822008990028723882609)
                      ·
                        rfl

theorem cell23_3458401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3458401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458401 prefixEnd_3458401 := by exact prefixLift 3458401
  have htrace : WordTrace (prefixWord ++ tailWord_3458401) baseStart_3458401 baseEnd_3458401 := by
    simpa [prefixWord, tailWord_3458401, baseEnd_3458401] using wordTrace_append hprefix tailTrace_3458401
  have hstable : (prefixWord ++ tailWord_3458401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458401).length < 2 ^ (prefixWord ++ tailWord_3458401).sum := by decide
  have hdescent : baseEnd_3458401 < baseStart_3458401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458418 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3458418 : Nat := 118140960795 + 3458418 * 2 ^ 59
def prefixEnd_3458418 : Nat := 4983230072969 + 3 ^ 40 * 3458418 * 2
def baseEnd_3458418 : Nat := 1775830738161155157370031

theorem tailTrace_3458418 : CollatzResearch.WordTrace tailWord_3458418 prefixEnd_3458418 1775830738161155157370031 := by
  unfold tailWord_3458418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31534716796187427903849977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84092578123166474410266605 31534716796187427903849977)
  ·
    refine ⟨23651037597140570927887483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31534716796187427903849977 23651037597140570927887483)
    ·
      refine ⟨35476556395710856391831225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651037597140570927887483 35476556395710856391831225)
      ·
        refine ⟨26607417296783142293873419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35476556395710856391831225 26607417296783142293873419)
        ·
          refine ⟨39911125945174713440810129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26607417296783142293873419 39911125945174713440810129)
          ·
            refine ⟨29933344458881035080607597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39911125945174713440810129 29933344458881035080607597)
            ·
              refine ⟨11225004172080388155227849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29933344458881035080607597 11225004172080388155227849)
              ·
                refine ⟨8418753129060291116420887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11225004172080388155227849 8418753129060291116420887)
                ·
                  refine ⟨12628129693590436674631331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418753129060291116420887 12628129693590436674631331)
                  ·
                    refine ⟨18942194540385655011946997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12628129693590436674631331 18942194540385655011946997)
                    ·
                      refine ⟨1775830738161155157370031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18942194540385655011946997 1775830738161155157370031)
                      ·
                        rfl

theorem cell23_3458418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3458418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458418 prefixEnd_3458418 := by exact prefixLift 3458418
  have htrace : WordTrace (prefixWord ++ tailWord_3458418) baseStart_3458418 baseEnd_3458418 := by
    simpa [prefixWord, tailWord_3458418, baseEnd_3458418] using wordTrace_append hprefix tailTrace_3458418
  have hstable : (prefixWord ++ tailWord_3458418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458418).length < 2 ^ (prefixWord ++ tailWord_3458418).sum := by decide
  have hdescent : baseEnd_3458418 < baseStart_3458418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458435 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 3]
def baseStart_3458435 : Nat := 118140960795 + 3458435 * 2 ^ 59
def prefixEnd_3458435 : Nat := 4983230072969 + 3 ^ 40 * 3458435 * 2
def baseEnd_3458435 : Nat := 1775839467332281590857453

theorem tailTrace_3458435 : CollatzResearch.WordTrace tailWord_3458435 prefixEnd_3458435 1775839467332281590857453 := by
  unfold tailWord_3458435
  simp only [CollatzResearch.WordTrace]
  refine ⟨126139487225688123518768759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84092991483792082345845839 126139487225688123518768759)
  ·
    refine ⟨189209230838532185278153139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126139487225688123518768759 189209230838532185278153139)
    ·
      refine ⟨283813846257798277917229709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189209230838532185278153139 283813846257798277917229709)
      ·
        refine ⟨106430192346674354218961141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283813846257798277917229709 106430192346674354218961141)
        ·
          refine ⟨9977830532500720708027607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106430192346674354218961141 9977830532500720708027607)
          ·
            refine ⟨14966745798751081062041411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9977830532500720708027607 14966745798751081062041411)
            ·
              refine ⟨22450118698126621593062117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14966745798751081062041411 22450118698126621593062117)
              ·
                refine ⟨4209397255898741548699147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22450118698126621593062117 4209397255898741548699147)
                ·
                  refine ⟨6314095883848112323048721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209397255898741548699147 6314095883848112323048721)
                  ·
                    refine ⟨4735571912886084242286541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314095883848112323048721 4735571912886084242286541)
                    ·
                      refine ⟨1775839467332281590857453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735571912886084242286541 1775839467332281590857453)
                      ·
                        rfl

theorem cell23_3458435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_3458435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458435 prefixEnd_3458435 := by exact prefixLift 3458435
  have htrace : WordTrace (prefixWord ++ tailWord_3458435) baseStart_3458435 baseEnd_3458435 := by
    simpa [prefixWord, tailWord_3458435, baseEnd_3458435] using wordTrace_append hprefix tailTrace_3458435
  have hstable : (prefixWord ++ tailWord_3458435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458435).length < 2 ^ (prefixWord ++ tailWord_3458435).sum := by decide
  have hdescent : baseEnd_3458435 < baseStart_3458435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458452 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3458452 : Nat := 118140960795 + 3458452 * 2 ^ 59
def prefixEnd_3458452 : Nat := 4983230072969 + 3 ^ 40 * 3458452 * 2
def baseEnd_3458452 : Nat := 1775848196503408024344875

theorem tailTrace_3458452 : CollatzResearch.WordTrace tailWord_3458452 prefixEnd_3458452 1775848196503408024344875 := by
  unfold tailWord_3458452
  simp only [CollatzResearch.WordTrace]
  refine ⟨63070053633313267711068805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84093404844417690281425073 63070053633313267711068805)
  ·
    refine ⟨11825635056246237695825401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63070053633313267711068805 11825635056246237695825401)
    ·
      refine ⟨8869226292184678271869051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11825635056246237695825401 8869226292184678271869051)
      ·
        refine ⟨13303839438277017407803577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869226292184678271869051 13303839438277017407803577)
        ·
          refine ⟨9977879578707763055852683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13303839438277017407803577 9977879578707763055852683)
          ·
            refine ⟨14966819368061644583779025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9977879578707763055852683 14966819368061644583779025)
            ·
              refine ⟨11225114526046233437834269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14966819368061644583779025 11225114526046233437834269)
              ·
                refine ⟨4209417947267337539187851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11225114526046233437834269 4209417947267337539187851)
                ·
                  refine ⟨6314126920901006308781777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209417947267337539187851 6314126920901006308781777)
                  ·
                    refine ⟨4735595190675754731586333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314126920901006308781777 4735595190675754731586333)
                    ·
                      refine ⟨1775848196503408024344875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735595190675754731586333 1775848196503408024344875)
                      ·
                        rfl

theorem cell23_3458452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3458452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458452 prefixEnd_3458452 := by exact prefixLift 3458452
  have htrace : WordTrace (prefixWord ++ tailWord_3458452) baseStart_3458452 baseEnd_3458452 := by
    simpa [prefixWord, tailWord_3458452, baseEnd_3458452] using wordTrace_append hprefix tailTrace_3458452
  have hstable : (prefixWord ++ tailWord_3458452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458452).length < 2 ^ (prefixWord ++ tailWord_3458452).sum := by decide
  have hdescent : baseEnd_3458452 < baseStart_3458452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458525 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3458525 : Nat := 118140960795 + 3458525 * 2 ^ 59
def prefixEnd_3458525 : Nat := 4983230072969 + 3 ^ 40 * 3458525 * 2
def baseEnd_3458525 : Nat := 1775885680591186238732039

theorem tailTrace_3458525 : CollatzResearch.WordTrace tailWord_3458525 prefixEnd_3458525 1775885680591186238732039 := by
  unfold tailWord_3458525
  simp only [CollatzResearch.WordTrace]
  refine ⟨126142769795362068889545029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84095179863574712593030019 126142769795362068889545029)
  ·
    refine ⟨23651769336630387916789693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126142769795362068889545029 23651769336630387916789693)
    ·
      refine ⟨8869413501236395468796135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23651769336630387916789693 8869413501236395468796135)
      ·
        refine ⟨13304120251854593203194203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869413501236395468796135 13304120251854593203194203)
        ·
          refine ⟨19956180377781889804791305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304120251854593203194203 19956180377781889804791305)
          ·
            refine ⟨14967135283336417353593479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19956180377781889804791305 14967135283336417353593479)
            ·
              refine ⟨22450702925004626030390219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14967135283336417353593479 22450702925004626030390219)
              ·
                refine ⟨33676054387506939045585329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22450702925004626030390219 33676054387506939045585329)
                ·
                  refine ⟨25257040790630204284188997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33676054387506939045585329 25257040790630204284188997)
                  ·
                    refine ⟨4735695148243163303285437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25257040790630204284188997 4735695148243163303285437)
                    ·
                      refine ⟨1775885680591186238732039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735695148243163303285437 1775885680591186238732039)
                      ·
                        rfl

theorem cell23_3458525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3458525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458525 prefixEnd_3458525 := by exact prefixLift 3458525
  have htrace : WordTrace (prefixWord ++ tailWord_3458525) baseStart_3458525 baseEnd_3458525 := by
    simpa [prefixWord, tailWord_3458525, baseEnd_3458525] using wordTrace_append hprefix tailTrace_3458525
  have hstable : (prefixWord ++ tailWord_3458525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458525).length < 2 ^ (prefixWord ++ tailWord_3458525).sum := by decide
  have hdescent : baseEnd_3458525 < baseStart_3458525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458535 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3458535 : Nat := 118140960795 + 3458535 * 2 ^ 59
def prefixEnd_3458535 : Nat := 4983230072969 + 3 ^ 40 * 3458535 * 2
def baseEnd_3458535 : Nat := 1775890815397731199606993

theorem tailTrace_3458535 : CollatzResearch.WordTrace tailWord_3458535 prefixEnd_3458535 1775890815397731199606993 := by
  unfold tailWord_3458535
  simp only [CollatzResearch.WordTrace]
  refine ⟨126143134525325840597409059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84095423016883893731606039 126143134525325840597409059)
  ·
    refine ⟨189214701787988760896113589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126143134525325840597409059 189214701787988760896113589)
    ·
      refine ⟨17738878292623946334010649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189214701787988760896113589 17738878292623946334010649)
      ·
        refine ⟨13304158719467959750507987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17738878292623946334010649 13304158719467959750507987)
        ·
          refine ⟨19956238079201939625761981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304158719467959750507987 19956238079201939625761981)
          ·
            refine ⟨7483589279700727359660743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19956238079201939625761981 7483589279700727359660743)
            ·
              refine ⟨11225383919551091039491115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483589279700727359660743 11225383919551091039491115)
              ·
                refine ⟨16838075879326636559236673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225383919551091039491115 16838075879326636559236673)
                ·
                  refine ⟨12628556909494977419427505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16838075879326636559236673 12628556909494977419427505)
                  ·
                    refine ⟨9471417682121233064570629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12628556909494977419427505 9471417682121233064570629)
                    ·
                      refine ⟨1775890815397731199606993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9471417682121233064570629 1775890815397731199606993)
                      ·
                        rfl

theorem cell23_3458535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3458535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458535 prefixEnd_3458535 := by exact prefixLift 3458535
  have htrace : WordTrace (prefixWord ++ tailWord_3458535) baseStart_3458535 baseEnd_3458535 := by
    simpa [prefixWord, tailWord_3458535, baseEnd_3458535] using wordTrace_append hprefix tailTrace_3458535
  have hstable : (prefixWord ++ tailWord_3458535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458535).length < 2 ^ (prefixWord ++ tailWord_3458535).sum := by decide
  have hdescent : baseEnd_3458535 < baseStart_3458535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458568 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3458568 : Nat := 118140960795 + 3458568 * 2 ^ 59
def prefixEnd_3458568 : Nat := 4983230072969 + 3 ^ 40 * 3458568 * 2
def baseEnd_3458568 : Nat := 1775907760259329570494341

theorem tailTrace_3458568 : CollatzResearch.WordTrace tailWord_3458568 prefixEnd_3458568 1775907760259329570494341 := by
  unfold tailWord_3458568
  simp only [CollatzResearch.WordTrace]
  refine ⟨63072169067103143616680179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84096225422804191488906905 63072169067103143616680179)
  ·
    refine ⟨94608253600654715425020269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63072169067103143616680179 94608253600654715425020269)
    ·
      refine ⟨35478095100245518284382601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94608253600654715425020269 35478095100245518284382601)
      ·
        refine ⟨26608571325184138713286951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35478095100245518284382601 26608571325184138713286951)
        ·
          refine ⟨39912856987776208069930427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26608571325184138713286951 39912856987776208069930427)
          ·
            refine ⟨59869285481664312104895641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39912856987776208069930427 59869285481664312104895641)
            ·
              refine ⟨44901964111248234078671731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59869285481664312104895641 44901964111248234078671731)
              ·
                refine ⟨67352946166872351118007597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44901964111248234078671731 67352946166872351118007597)
                ·
                  refine ⟨25257354812577131669252849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67352946166872351118007597 25257354812577131669252849)
                  ·
                    refine ⟨18943016109432848751939637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25257354812577131669252849 18943016109432848751939637)
                    ·
                      refine ⟨1775907760259329570494341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18943016109432848751939637 1775907760259329570494341)
                      ·
                        rfl

theorem cell23_3458568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3458568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458568 prefixEnd_3458568 := by exact prefixLift 3458568
  have htrace : WordTrace (prefixWord ++ tailWord_3458568) baseStart_3458568 baseEnd_3458568 := by
    simpa [prefixWord, tailWord_3458568, baseEnd_3458568] using wordTrace_append hprefix tailTrace_3458568
  have hstable : (prefixWord ++ tailWord_3458568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458568).length < 2 ^ (prefixWord ++ tailWord_3458568).sum := by decide
  have hdescent : baseEnd_3458568 < baseStart_3458568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458573 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3458573 : Nat := 118140960795 + 3458573 * 2 ^ 59
def prefixEnd_3458573 : Nat := 4983230072969 + 3 ^ 40 * 3458573 * 2
def baseEnd_3458573 : Nat := 1775910327662602050931819

theorem tailTrace_3458573 : CollatzResearch.WordTrace tailWord_3458573 prefixEnd_3458573 1775910327662602050931819 := by
  unfold tailWord_3458573
  simp only [CollatzResearch.WordTrace]
  refine ⟨126144520499188173087292373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84096346999458782058194915 126144520499188173087292373)
  ·
    refine ⟨2956512199199722806733415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 126144520499188173087292373 2956512199199722806733415)
    ·
      refine ⟨4434768298799584210100123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956512199199722806733415 4434768298799584210100123)
      ·
        refine ⟨6652152448199376315150185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434768298799584210100123 6652152448199376315150185)
        ·
          refine ⟨4989114336149532236362639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6652152448199376315150185 4989114336149532236362639)
          ·
            refine ⟨7483671504224298354543959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989114336149532236362639 7483671504224298354543959)
            ·
              refine ⟨11225507256336447531815939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483671504224298354543959 11225507256336447531815939)
              ·
                refine ⟨16838260884504671297723909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225507256336447531815939 16838260884504671297723909)
                ·
                  refine ⟨3157173915844625868323233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16838260884504671297723909 3157173915844625868323233)
                  ·
                    refine ⟨2367880436883469401242425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3157173915844625868323233 2367880436883469401242425)
                    ·
                      refine ⟨1775910327662602050931819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367880436883469401242425 1775910327662602050931819)
                      ·
                        rfl

theorem cell23_3458573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3458573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458573 prefixEnd_3458573 := by exact prefixLift 3458573
  have htrace : WordTrace (prefixWord ++ tailWord_3458573) baseStart_3458573 baseEnd_3458573 := by
    simpa [prefixWord, tailWord_3458573, baseEnd_3458573] using wordTrace_append hprefix tailTrace_3458573
  have hstable : (prefixWord ++ tailWord_3458573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458573).length < 2 ^ (prefixWord ++ tailWord_3458573).sum := by decide
  have hdescent : baseEnd_3458573 < baseStart_3458573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458590 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3458590 : Nat := 118140960795 + 3458590 * 2 ^ 59
def prefixEnd_3458590 : Nat := 4983230072969 + 3 ^ 40 * 3458590 * 2
def baseEnd_3458590 : Nat := 1775919056833728484419241

theorem tailTrace_3458590 : CollatzResearch.WordTrace tailWord_3458590 prefixEnd_3458590 1775919056833728484419241 := by
  unfold tailWord_3458590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15768142567515823123832653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84096760360084389993774149 15768142567515823123832653)
  ·
    refine ⟨5913053462818433671437245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15768142567515823123832653 5913053462818433671437245)
    ·
      refine ⟨2217395048556912626788967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5913053462818433671437245 2217395048556912626788967)
      ·
        refine ⟨3326092572835368940183451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217395048556912626788967 3326092572835368940183451)
        ·
          refine ⟨4989138859253053410275177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326092572835368940183451 4989138859253053410275177)
          ·
            refine ⟨3741854144439790057706383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4989138859253053410275177 3741854144439790057706383)
            ·
              refine ⟨5612781216659685086559575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741854144439790057706383 5612781216659685086559575)
              ·
                refine ⟨8419171824989527629839363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612781216659685086559575 8419171824989527629839363)
                ·
                  refine ⟨12628757737484291444759045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8419171824989527629839363 12628757737484291444759045)
                  ·
                    refine ⟨2367892075778304645892321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12628757737484291444759045 2367892075778304645892321)
                    ·
                      refine ⟨1775919056833728484419241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367892075778304645892321 1775919056833728484419241)
                      ·
                        rfl

theorem cell23_3458590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3458590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458590 prefixEnd_3458590 := by exact prefixLift 3458590
  have htrace : WordTrace (prefixWord ++ tailWord_3458590) baseStart_3458590 baseEnd_3458590 := by
    simpa [prefixWord, tailWord_3458590, baseEnd_3458590] using wordTrace_append hprefix tailTrace_3458590
  have hstable : (prefixWord ++ tailWord_3458590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458590).length < 2 ^ (prefixWord ++ tailWord_3458590).sum := by decide
  have hdescent : baseEnd_3458590 < baseStart_3458590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458608 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_3458608 : Nat := 118140960795 + 3458608 * 2 ^ 59
def prefixEnd_3458608 : Nat := 4983230072969 + 3 ^ 40 * 3458608 * 2
def baseEnd_3458608 : Nat := 1775928299485509413994157

theorem tailTrace_3458608 : CollatzResearch.WordTrace tailWord_3458608 prefixEnd_3458608 1775928299485509413994157 := by
  unfold tailWord_3458608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63072898527030687032408239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84097198036040916043210985 63072898527030687032408239)
  ·
    refine ⟨94609347790546030548612359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63072898527030687032408239 94609347790546030548612359)
    ·
      refine ⟨141914021685819045822918539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94609347790546030548612359 141914021685819045822918539)
      ·
        refine ⟨212871032528728568734377809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141914021685819045822918539 212871032528728568734377809)
        ·
          refine ⟨159653274396546426550783357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212871032528728568734377809 159653274396546426550783357)
          ·
            refine ⟨59869977898704909956543759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159653274396546426550783357 59869977898704909956543759)
            ·
              refine ⟨89804966848057364934815639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59869977898704909956543759 89804966848057364934815639)
              ·
                refine ⟨134707450272086047402223459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89804966848057364934815639 134707450272086047402223459)
                ·
                  refine ⟨202061175408129071103335189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134707450272086047402223459 202061175408129071103335189)
                  ·
                    refine ⟨9471617597256050207968837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 202061175408129071103335189 9471617597256050207968837)
                    ·
                      refine ⟨1775928299485509413994157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9471617597256050207968837 1775928299485509413994157)
                      ·
                        rfl

theorem cell23_3458608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_3458608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458608 prefixEnd_3458608 := by exact prefixLift 3458608
  have htrace : WordTrace (prefixWord ++ tailWord_3458608) baseStart_3458608 baseEnd_3458608 := by
    simpa [prefixWord, tailWord_3458608, baseEnd_3458608] using wordTrace_append hprefix tailTrace_3458608
  have hstable : (prefixWord ++ tailWord_3458608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458608).length < 2 ^ (prefixWord ++ tailWord_3458608).sum := by decide
  have hdescent : baseEnd_3458608 < baseStart_3458608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458615 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_3458615 : Nat := 118140960795 + 3458615 * 2 ^ 59
def prefixEnd_3458615 : Nat := 4983230072969 + 3 ^ 40 * 3458615 * 2
def baseEnd_3458615 : Nat := 1775931893850090886606625

theorem tailTrace_3458615 : CollatzResearch.WordTrace tailWord_3458615 prefixEnd_3458615 1775931893850090886606625 := by
  unfold tailWord_3458615
  simp only [CollatzResearch.WordTrace]
  refine ⟨126146052365036014260321299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84097368243357342840214199 126146052365036014260321299)
  ·
    refine ⟨189219078547554021390481949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126146052365036014260321299 189219078547554021390481949)
    ·
      refine ⟨70957154455332758021430731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189219078547554021390481949 70957154455332758021430731)
      ·
        refine ⟨106435731682999137032146097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70957154455332758021430731 106435731682999137032146097)
        ·
          refine ⟨79826798762249352774109573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106435731682999137032146097 79826798762249352774109573)
          ·
            refine ⟨14967524767921753645145545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79826798762249352774109573 14967524767921753645145545)
            ·
              refine ⟨11225643575941315233859159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14967524767921753645145545 11225643575941315233859159)
              ·
                refine ⟨16838465363911972850788739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225643575941315233859159 16838465363911972850788739)
                ·
                  refine ⟨25257698045867959276183109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16838465363911972850788739 25257698045867959276183109)
                  ·
                    refine ⟨4735818383600242364284333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25257698045867959276183109 4735818383600242364284333)
                    ·
                      refine ⟨1775931893850090886606625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735818383600242364284333 1775931893850090886606625)
                      ·
                        rfl

theorem cell23_3458615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_3458615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458615 prefixEnd_3458615 := by exact prefixLift 3458615
  have htrace : WordTrace (prefixWord ++ tailWord_3458615) baseStart_3458615 baseEnd_3458615 := by
    simpa [prefixWord, tailWord_3458615, baseEnd_3458615] using wordTrace_append hprefix tailTrace_3458615
  have hstable : (prefixWord ++ tailWord_3458615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458615).length < 2 ^ (prefixWord ++ tailWord_3458615).sum := by decide
  have hdescent : baseEnd_3458615 < baseStart_3458615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458618 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_3458618 : Nat := 118140960795 + 3458618 * 2 ^ 59
def prefixEnd_3458618 : Nat := 4983230072969 + 3 ^ 40 * 3458618 * 2
def baseEnd_3458618 : Nat := 197325937143561597207679

theorem tailTrace_3458618 : CollatzResearch.WordTrace tailWord_3458618 prefixEnd_3458618 197325937143561597207679 := by
  unfold tailWord_3458618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31536540446006286443170127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84097441189350097181787005 31536540446006286443170127)
  ·
    refine ⟨47304810669009429664755191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31536540446006286443170127 47304810669009429664755191)
    ·
      refine ⟨70957216003514144497132787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47304810669009429664755191 70957216003514144497132787)
      ·
        refine ⟨106435824005271216745699181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70957216003514144497132787 106435824005271216745699181)
        ·
          refine ⟨39913434001976706279637193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106435824005271216745699181 39913434001976706279637193)
          ·
            refine ⟨29935075501482529709727895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39913434001976706279637193 29935075501482529709727895)
            ·
              refine ⟨44902613252223794564591843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29935075501482529709727895 44902613252223794564591843)
              ·
                refine ⟨67353919878335691846887765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44902613252223794564591843 67353919878335691846887765)
                ·
                  refine ⟨197325937143561597207679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67353919878335691846887765 197325937143561597207679)
                  ·
                    rfl

theorem cell23_3458618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_3458618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458618 prefixEnd_3458618 := by exact prefixLift 3458618
  have htrace : WordTrace (prefixWord ++ tailWord_3458618) baseStart_3458618 baseEnd_3458618 := by
    simpa [prefixWord, tailWord_3458618, baseEnd_3458618] using wordTrace_append hprefix tailTrace_3458618
  have hstable : (prefixWord ++ tailWord_3458618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458618).length < 2 ^ (prefixWord ++ tailWord_3458618).sum := by decide
  have hdescent : baseEnd_3458618 < baseStart_3458618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458648 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_3458648 : Nat := 118140960795 + 3458648 * 2 ^ 59
def prefixEnd_3458648 : Nat := 4983230072969 + 3 ^ 40 * 3458648 * 2
def baseEnd_3458648 : Nat := 591982946237229752497991

theorem tailTrace_3458648 : CollatzResearch.WordTrace tailWord_3458648 prefixEnd_3458648 591982946237229752497991 := by
  unfold tailWord_3458648
  simp only [CollatzResearch.WordTrace]
  refine ⟨63073627986958230448136299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84098170649277640597515065 63073627986958230448136299)
  ·
    refine ⟨94610441980437345672204449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63073627986958230448136299 94610441980437345672204449)
    ·
      refine ⟨70957831485328009254153337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94610441980437345672204449 70957831485328009254153337)
      ·
        refine ⟨53218373613996006940615003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70957831485328009254153337 53218373613996006940615003)
        ·
          refine ⟨79827560420994010410922505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53218373613996006940615003 79827560420994010410922505)
          ·
            refine ⟨59870670315745507808191879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79827560420994010410922505 59870670315745507808191879)
            ·
              refine ⟨89806005473618261712287819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59870670315745507808191879 89806005473618261712287819)
              ·
                refine ⟨134709008210427392568431729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89806005473618261712287819 134709008210427392568431729)
                ·
                  refine ⟨101031756157820544426323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134709008210427392568431729 101031756157820544426323797)
                  ·
                    refine ⟨591982946237229752497991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 101031756157820544426323797 591982946237229752497991)
                    ·
                      rfl

theorem cell23_3458648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_3458648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458648 prefixEnd_3458648 := by exact prefixLift 3458648
  have htrace : WordTrace (prefixWord ++ tailWord_3458648) baseStart_3458648 baseEnd_3458648 := by
    simpa [prefixWord, tailWord_3458648, baseEnd_3458648] using wordTrace_append hprefix tailTrace_3458648
  have hstable : (prefixWord ++ tailWord_3458648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458648).length < 2 ^ (prefixWord ++ tailWord_3458648).sum := by decide
  have hdescent : baseEnd_3458648 < baseStart_3458648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458652 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 6]
def baseStart_3458652 : Nat := 118140960795 + 3458652 * 2 ^ 59
def prefixEnd_3458652 : Nat := 4983230072969 + 3 ^ 40 * 3458652 * 2
def baseEnd_3458652 : Nat := 197327876959367471315995

theorem tailTrace_3458652 : CollatzResearch.WordTrace tailWord_3458652 prefixEnd_3458652 197327876959367471315995 := by
  unfold tailWord_3458652
  simp only [CollatzResearch.WordTrace]
  refine ⟨63073700932950984789709105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84098267910601313052945473 63073700932950984789709105)
  ·
    refine ⟨47305275699713238592281829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63073700932950984789709105 47305275699713238592281829)
    ·
      refine ⟨8869739193696232236052843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47305275699713238592281829 8869739193696232236052843)
      ·
        refine ⟨13304608790544348354079265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869739193696232236052843 13304608790544348354079265)
        ·
          refine ⟨9978456592908261265559449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13304608790544348354079265 9978456592908261265559449)
          ·
            refine ⟨7483842444681195949169587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9978456592908261265559449 7483842444681195949169587)
            ·
              refine ⟨11225763667021793923754381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483842444681195949169587 11225763667021793923754381)
              ·
                refine ⟨4209661375133172721407893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11225763667021793923754381 4209661375133172721407893)
                ·
                  refine ⟨197327876959367471315995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4209661375133172721407893 197327876959367471315995)
                  ·
                    rfl

theorem cell23_3458652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_3458652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458652 prefixEnd_3458652 := by exact prefixLift 3458652
  have htrace : WordTrace (prefixWord ++ tailWord_3458652) baseStart_3458652 baseEnd_3458652 := by
    simpa [prefixWord, tailWord_3458652, baseEnd_3458652] using wordTrace_append hprefix tailTrace_3458652
  have hstable : (prefixWord ++ tailWord_3458652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458652).length < 2 ^ (prefixWord ++ tailWord_3458652).sum := by decide
  have hdescent : baseEnd_3458652 < baseStart_3458652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458679 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 1, 1, 3]
def baseStart_3458679 : Nat := 118140960795 + 3458679 * 2 ^ 59
def prefixEnd_3458679 : Nat := 4983230072969 + 3 ^ 40 * 3458679 * 2
def baseEnd_3458679 : Nat := 1775964756611978636206331

theorem tailTrace_3458679 : CollatzResearch.WordTrace tailWord_3458679 prefixEnd_3458679 1775964756611978636206331 := by
  unfold tailWord_3458679
  simp only [CollatzResearch.WordTrace]
  refine ⟨126148386636804153190651091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84098924424536102127100727 126148386636804153190651091)
  ·
    refine ⟨189222579955206229785976637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126148386636804153190651091 189222579955206229785976637)
    ·
      refine ⟨70958467483202336169741239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189222579955206229785976637 70958467483202336169741239)
      ·
        refine ⟨106437701224803504254611859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70958467483202336169741239 106437701224803504254611859)
        ·
          refine ⟨159656551837205256381917789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106437701224803504254611859 159656551837205256381917789)
          ·
            refine ⟨59871206938951971143219171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159656551837205256381917789 59871206938951971143219171)
            ·
              refine ⟨89806810408427956714828757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59871206938951971143219171 89806810408427956714828757)
              ·
                refine ⟨2104847118947530235503799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89806810408427956714828757 2104847118947530235503799)
                ·
                  refine ⟨3157270678421295353255699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104847118947530235503799 3157270678421295353255699)
                  ·
                    refine ⟨4735906017631943029883549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3157270678421295353255699 4735906017631943029883549)
                    ·
                      refine ⟨1775964756611978636206331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4735906017631943029883549 1775964756611978636206331)
                      ·
                        rfl

theorem cell23_3458679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_3458679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458679 prefixEnd_3458679 := by exact prefixLift 3458679
  have htrace : WordTrace (prefixWord ++ tailWord_3458679) baseStart_3458679 baseEnd_3458679 := by
    simpa [prefixWord, tailWord_3458679, baseEnd_3458679] using wordTrace_append hprefix tailTrace_3458679
  have hstable : (prefixWord ++ tailWord_3458679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458679).length < 2 ^ (prefixWord ++ tailWord_3458679).sum := by decide
  have hdescent : baseEnd_3458679 < baseStart_3458679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458689 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_3458689 : Nat := 118140960795 + 3458689 * 2 ^ 59
def prefixEnd_3458689 : Nat := 4983230072969 + 3 ^ 40 * 3458689 * 2
def baseEnd_3458689 : Nat := 1775969891418523597081285

theorem tailTrace_3458689 : CollatzResearch.WordTrace tailWord_3458689 prefixEnd_3458689 1775969891418523597081285 := by
  unfold tailWord_3458689
  simp only [CollatzResearch.WordTrace]
  refine ⟨126148751366767924898515121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84099167577845283265676747 126148751366767924898515121)
  ·
    refine ⟨94611563525075943673886341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126148751366767924898515121 94611563525075943673886341)
    ·
      refine ⟨17739668160951739438853689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94611563525075943673886341 17739668160951739438853689)
      ·
        refine ⟨13304751120713804579140267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17739668160951739438853689 13304751120713804579140267)
        ·
          refine ⟨19957126681070706868710401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304751120713804579140267 19957126681070706868710401)
          ·
            refine ⟨14967845010803030151532801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19957126681070706868710401 14967845010803030151532801)
            ·
              refine ⟨11225883758102272613649601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14967845010803030151532801 11225883758102272613649601)
              ·
                refine ⟨8419412818576704460237201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11225883758102272613649601 8419412818576704460237201)
                ·
                  refine ⟨6314559613932528345177901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8419412818576704460237201 6314559613932528345177901)
                  ·
                    refine ⟨2367959855224698129441713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6314559613932528345177901 2367959855224698129441713)
                    ·
                      refine ⟨1775969891418523597081285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367959855224698129441713 1775969891418523597081285)
                      ·
                        rfl

theorem cell23_3458689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_3458689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458689 prefixEnd_3458689 := by exact prefixLift 3458689
  have htrace : WordTrace (prefixWord ++ tailWord_3458689) baseStart_3458689 baseEnd_3458689 := by
    simpa [prefixWord, tailWord_3458689, baseEnd_3458689] using wordTrace_append hprefix tailTrace_3458689
  have hstable : (prefixWord ++ tailWord_3458689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458689).length < 2 ^ (prefixWord ++ tailWord_3458689).sum := by decide
  have hdescent : baseEnd_3458689 < baseStart_3458689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458702 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3458702 : Nat := 118140960795 + 3458702 * 2 ^ 59
def prefixEnd_3458702 : Nat := 4983230072969 + 3 ^ 40 * 3458702 * 2
def baseEnd_3458702 : Nat := 1775976566667032046218725

theorem tailTrace_3458702 : CollatzResearch.WordTrace tailWord_3458702 prefixEnd_3458702 1775976566667032046218725 := by
  unfold tailWord_3458702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15768653189465103514842295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84099483677147218745825573 15768653189465103514842295)
  ·
    refine ⟨23652979784197655272263443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15768653189465103514842295 23652979784197655272263443)
    ·
      refine ⟨35479469676296482908395165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23652979784197655272263443 35479469676296482908395165)
      ·
        refine ⟨13304801128611181090648187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35479469676296482908395165 13304801128611181090648187)
        ·
          refine ⟨19957201692916771635972281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304801128611181090648187 19957201692916771635972281)
          ·
            refine ⟨14967901269687578726979211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19957201692916771635972281 14967901269687578726979211)
            ·
              refine ⟨22451851904531368090468817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14967901269687578726979211 22451851904531368090468817)
              ·
                refine ⟨16838888928398526067851613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22451851904531368090468817 16838888928398526067851613)
                ·
                  refine ⟨6314583348149447275444355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16838888928398526067851613 6314583348149447275444355)
                  ·
                    refine ⟨9471875022224170913166533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314583348149447275444355 9471875022224170913166533)
                    ·
                      refine ⟨1775976566667032046218725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9471875022224170913166533 1775976566667032046218725)
                      ·
                        rfl

theorem cell23_3458702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3458702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458702 prefixEnd_3458702 := by exact prefixLift 3458702
  have htrace : WordTrace (prefixWord ++ tailWord_3458702) baseStart_3458702 baseEnd_3458702 := by
    simpa [prefixWord, tailWord_3458702, baseEnd_3458702] using wordTrace_append hprefix tailTrace_3458702
  have hstable : (prefixWord ++ tailWord_3458702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458702).length < 2 ^ (prefixWord ++ tailWord_3458702).sum := by decide
  have hdescent : baseEnd_3458702 < baseStart_3458702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458712 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 1, 6]
def baseStart_3458712 : Nat := 118140960795 + 3458712 * 2 ^ 59
def prefixEnd_3458712 : Nat := 4983230072969 + 3 ^ 40 * 3458712 * 2
def baseEnd_3458712 : Nat := 591993900491192335697893

theorem tailTrace_3458712 : CollatzResearch.WordTrace tailWord_3458712 prefixEnd_3458712 591993900491192335697893 := by
  unfold tailWord_3458712
  simp only [CollatzResearch.WordTrace]
  refine ⟨63074795122842299913301195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84099726830456399884401593 63074795122842299913301195)
  ·
    refine ⟨94612192684263449869951793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63074795122842299913301195 94612192684263449869951793)
    ·
      refine ⟨70959144513197587402463845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94612192684263449869951793 70959144513197587402463845)
      ·
        refine ⟨13304839596224547637961971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70959144513197587402463845 13304839596224547637961971)
        ·
          refine ⟨19957259394336821456942957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304839596224547637961971 19957259394336821456942957)
          ·
            refine ⟨7483972272876308046353609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19957259394336821456942957 7483972272876308046353609)
            ·
              refine ⟨5612979204657231034765207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7483972272876308046353609 5612979204657231034765207)
              ·
                refine ⟨8419468806985846552147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612979204657231034765207 8419468806985846552147811)
                ·
                  refine ⟨12629203210478769828221717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8419468806985846552147811 12629203210478769828221717)
                  ·
                    refine ⟨591993900491192335697893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12629203210478769828221717 591993900491192335697893)
                    ·
                      rfl

theorem cell23_3458712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_3458712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458712 prefixEnd_3458712 := by exact prefixLift 3458712
  have htrace : WordTrace (prefixWord ++ tailWord_3458712) baseStart_3458712 baseEnd_3458712 := by
    simpa [prefixWord, tailWord_3458712, baseEnd_3458712] using wordTrace_append hprefix tailTrace_3458712
  have hstable : (prefixWord ++ tailWord_3458712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458712).length < 2 ^ (prefixWord ++ tailWord_3458712).sum := by decide
  have hdescent : baseEnd_3458712 < baseStart_3458712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458736 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 1, 2, 2]
def baseStart_3458736 : Nat := 118140960795 + 3458736 * 2 ^ 59
def prefixEnd_3458736 : Nat := 4983230072969 + 3 ^ 40 * 3458736 * 2
def baseEnd_3458736 : Nat := 1775994025009284913193569

theorem tailTrace_3458736 : CollatzResearch.WordTrace tailWord_3458736 prefixEnd_3458736 1775994025009284913193569 := by
  unfold tailWord_3458736
  simp only [CollatzResearch.WordTrace]
  refine ⟨63075232798798825962738031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84100310398398434616984041 63075232798798825962738031)
  ·
    refine ⟨94612849198198238944107047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63075232798798825962738031 94612849198198238944107047)
    ·
      refine ⟨141919273797297358416160571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94612849198198238944107047 141919273797297358416160571)
      ·
        refine ⟨212878910695946037624240857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141919273797297358416160571 212878910695946037624240857)
        ·
          refine ⟨159659183021959528218180643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212878910695946037624240857 159659183021959528218180643)
          ·
            refine ⟨239488774532939292327270965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159659183021959528218180643 239488774532939292327270965)
            ·
              refine ⟨22452072612463058655681653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239488774532939292327270965 22452072612463058655681653)
              ·
                refine ⟨2104881807418411748970155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22452072612463058655681653 2104881807418411748970155)
                ·
                  refine ⟨3157322711127617623455233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104881807418411748970155 3157322711127617623455233)
                  ·
                    refine ⟨2367992033345713217591425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3157322711127617623455233 2367992033345713217591425)
                    ·
                      refine ⟨1775994025009284913193569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2367992033345713217591425 1775994025009284913193569)
                      ·
                        rfl

theorem cell23_3458736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 2, 2].length) (baseStart_3458736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458736 prefixEnd_3458736 := by exact prefixLift 3458736
  have htrace : WordTrace (prefixWord ++ tailWord_3458736) baseStart_3458736 baseEnd_3458736 := by
    simpa [prefixWord, tailWord_3458736, baseEnd_3458736] using wordTrace_append hprefix tailTrace_3458736
  have hstable : (prefixWord ++ tailWord_3458736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458736).length < 2 ^ (prefixWord ++ tailWord_3458736).sum := by decide
  have hdescent : baseEnd_3458736 < baseStart_3458736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458769 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_3458769 : Nat := 118140960795 + 3458769 * 2 ^ 59
def prefixEnd_3458769 : Nat := 4983230072969 + 3 ^ 40 * 3458769 * 2
def baseEnd_3458769 : Nat := 1776010969870883284080917

theorem tailTrace_3458769 : CollatzResearch.WordTrace tailWord_3458769 prefixEnd_3458769 1776010969870883284080917 := by
  unfold tailWord_3458769
  simp only [CollatzResearch.WordTrace]
  refine ⟨126151669206478098561427361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84101112804318732374284907 126151669206478098561427361)
  ·
    refine ⟨94613751904858573921070521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126151669206478098561427361 94613751904858573921070521)
    ·
      refine ⟨70960313928643930440802891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94613751904858573921070521 70960313928643930440802891)
      ·
        refine ⟨106440470892965895661204337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70960313928643930440802891 106440470892965895661204337)
        ·
          refine ⟨79830353169724421745903253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106440470892965895661204337 79830353169724421745903253)
          ·
            refine ⟨3742047804830832269339215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79830353169724421745903253 3742047804830832269339215)
            ·
              refine ⟨5613071707246248404008823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742047804830832269339215 5613071707246248404008823)
              ·
                refine ⟨8419607560869372606013235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613071707246248404008823 8419607560869372606013235)
                ·
                  refine ⟨12629411341304058909019853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8419607560869372606013235 12629411341304058909019853)
                  ·
                    refine ⟨4736029252989022090882445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12629411341304058909019853 4736029252989022090882445)
                    ·
                      refine ⟨1776010969870883284080917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736029252989022090882445 1776010969870883284080917)
                      ·
                        rfl

theorem cell23_3458769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_3458769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458769 prefixEnd_3458769 := by exact prefixLift 3458769
  have htrace : WordTrace (prefixWord ++ tailWord_3458769) baseStart_3458769 baseEnd_3458769 := by
    simpa [prefixWord, tailWord_3458769, baseEnd_3458769] using wordTrace_append hprefix tailTrace_3458769
  have hstable : (prefixWord ++ tailWord_3458769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458769).length < 2 ^ (prefixWord ++ tailWord_3458769).sum := by decide
  have hdescent : baseEnd_3458769 < baseStart_3458769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458787 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3458787 : Nat := 118140960795 + 3458787 * 2 ^ 59
def prefixEnd_3458787 : Nat := 4983230072969 + 3 ^ 40 * 3458787 * 2
def baseEnd_3458787 : Nat := 1776020212522664213655835

theorem tailTrace_3458787 : CollatzResearch.WordTrace tailWord_3458787 prefixEnd_3458787 1776020212522664213655835 := by
  unfold tailWord_3458787
  simp only [CollatzResearch.WordTrace]
  refine ⟨126152325720412887635582615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84101550480275258423721743 126152325720412887635582615)
  ·
    refine ⟨189228488580619331453373923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126152325720412887635582615 189228488580619331453373923)
    ·
      refine ⟨283842732870928997180060885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189228488580619331453373923 283842732870928997180060885)
      ·
        refine ⟨6652564051662398371407677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 283842732870928997180060885 6652564051662398371407677)
        ·
          refine ⟨2494711519373399389277879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6652564051662398371407677 2494711519373399389277879)
          ·
            refine ⟨3742067279060099083916819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494711519373399389277879 3742067279060099083916819)
            ·
              refine ⟨5613100918590148625875229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742067279060099083916819 5613100918590148625875229)
              ·
                refine ⟨2104912844471305734703211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613100918590148625875229 2104912844471305734703211)
                ·
                  refine ⟨3157369266706958602054817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104912844471305734703211 3157369266706958602054817)
                  ·
                    refine ⟨2368026950030218951541113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3157369266706958602054817 2368026950030218951541113)
                    ·
                      refine ⟨1776020212522664213655835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368026950030218951541113 1776020212522664213655835)
                      ·
                        rfl

theorem cell23_3458787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3458787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458787 prefixEnd_3458787 := by exact prefixLift 3458787
  have htrace : WordTrace (prefixWord ++ tailWord_3458787) baseStart_3458787 baseEnd_3458787 := by
    simpa [prefixWord, tailWord_3458787, baseEnd_3458787] using wordTrace_append hprefix tailTrace_3458787
  have hstable : (prefixWord ++ tailWord_3458787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458787).length < 2 ^ (prefixWord ++ tailWord_3458787).sum := by decide
  have hdescent : baseEnd_3458787 < baseStart_3458787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458795 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_3458795 : Nat := 118140960795 + 3458795 * 2 ^ 59
def prefixEnd_3458795 : Nat := 4983230072969 + 3 ^ 40 * 3458795 * 2
def baseEnd_3458795 : Nat := 1776024320367900182355797

theorem tailTrace_3458795 : CollatzResearch.WordTrace tailWord_3458795 prefixEnd_3458795 1776024320367900182355797 := by
  unfold tailWord_3458795
  simp only [CollatzResearch.WordTrace]
  refine ⟨126152617504383905001873839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84101745002922603334582559 126152617504383905001873839)
  ·
    refine ⟨189228926256575857502810759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126152617504383905001873839 189228926256575857502810759)
    ·
      refine ⟨283843389384863786254216139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189228926256575857502810759 283843389384863786254216139)
      ·
        refine ⟨425765084077295679381324209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283843389384863786254216139 425765084077295679381324209)
        ·
          refine ⟨319323813057971759535993157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425765084077295679381324209 319323813057971759535993157)
          ·
            refine ⟨59873214948369704912998717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319323813057971759535993157 59873214948369704912998717)
            ·
              refine ⟨22452455605638639342374519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59873214948369704912998717 22452455605638639342374519)
              ·
                refine ⟨33678683408457959013561779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22452455605638639342374519 33678683408457959013561779)
                ·
                  refine ⟨50518025112686938520342669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33678683408457959013561779 50518025112686938520342669)
                  ·
                    refine ⟨18944259417257601945128501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50518025112686938520342669 18944259417257601945128501)
                    ·
                      refine ⟨1776024320367900182355797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18944259417257601945128501 1776024320367900182355797)
                      ·
                        rfl

theorem cell23_3458795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_3458795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458795 prefixEnd_3458795 := by exact prefixLift 3458795
  have htrace : WordTrace (prefixWord ++ tailWord_3458795) baseStart_3458795 baseEnd_3458795 := by
    simpa [prefixWord, tailWord_3458795, baseEnd_3458795] using wordTrace_append hprefix tailTrace_3458795
  have hstable : (prefixWord ++ tailWord_3458795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458795).length < 2 ^ (prefixWord ++ tailWord_3458795).sum := by decide
  have hdescent : baseEnd_3458795 < baseStart_3458795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458804 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3458804 : Nat := 118140960795 + 3458804 * 2 ^ 59
def prefixEnd_3458804 : Nat := 4983230072969 + 3 ^ 40 * 3458804 * 2
def baseEnd_3458804 : Nat := 1776028941693790647143257

theorem tailTrace_3458804 : CollatzResearch.WordTrace tailWord_3458804 prefixEnd_3458804 1776028941693790647143257 := by
  unfold tailWord_3458804
  simp only [CollatzResearch.WordTrace]
  refine ⟨63076472880675649769475733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84101963840900866359300977 63076472880675649769475733)
  ·
    refine ⟨2956709666281671082944175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63076472880675649769475733 2956709666281671082944175)
    ·
      refine ⟨4435064499422506624416263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956709666281671082944175 4435064499422506624416263)
      ·
        refine ⟨6652596749133759936624395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4435064499422506624416263 6652596749133759936624395)
        ·
          refine ⟨9978895123700639904936593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6652596749133759936624395 9978895123700639904936593)
          ·
            refine ⟨7484171342775479928702445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9978895123700639904936593 7484171342775479928702445)
            ·
              refine ⟨2806564253540804973263417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7484171342775479928702445 2806564253540804973263417)
              ·
                refine ⟨2104923190155603729947563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806564253540804973263417 2104923190155603729947563)
                ·
                  refine ⟨3157384785233405594921345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104923190155603729947563 3157384785233405594921345)
                  ·
                    refine ⟨2368038588925054196191009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3157384785233405594921345 2368038588925054196191009)
                    ·
                      refine ⟨1776028941693790647143257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368038588925054196191009 1776028941693790647143257)
                      ·
                        rfl

theorem cell23_3458804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3458804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458804 prefixEnd_3458804 := by exact prefixLift 3458804
  have htrace : WordTrace (prefixWord ++ tailWord_3458804) baseStart_3458804 baseEnd_3458804 := by
    simpa [prefixWord, tailWord_3458804, baseEnd_3458804] using wordTrace_append hprefix tailTrace_3458804
  have hstable : (prefixWord ++ tailWord_3458804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458804).length < 2 ^ (prefixWord ++ tailWord_3458804).sum := by decide
  have hdescent : baseEnd_3458804 < baseStart_3458804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458812 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_3458812 : Nat := 118140960795 + 3458812 * 2 ^ 59
def prefixEnd_3458812 : Nat := 4983230072969 + 3 ^ 40 * 3458812 * 2
def baseEnd_3458812 : Nat := 1776033049539026615843219

theorem tailTrace_3458812 : CollatzResearch.WordTrace tailWord_3458812 prefixEnd_3458812 1776033049539026615843219 := by
  unfold tailWord_3458812
  simp only [CollatzResearch.WordTrace]
  refine ⟨63076618772661158452621345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84102158363548211270161793 63076618772661158452621345)
  ·
    refine ⟨47307464079495868839466009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63076618772661158452621345 47307464079495868839466009)
    ·
      refine ⟨35480598059621901629599507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47307464079495868839466009 35480598059621901629599507)
      ·
        refine ⟨53220897089432852444399261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35480598059621901629599507 53220897089432852444399261)
        ·
          refine ⟨19957836408537319666649723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53220897089432852444399261 19957836408537319666649723)
          ·
            refine ⟨29936754612805979499974585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19957836408537319666649723 29936754612805979499974585)
            ·
              refine ⟨22452565959604484624980939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29936754612805979499974585 22452565959604484624980939)
              ·
                refine ⟨33678848939406726937471409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22452565959604484624980939 33678848939406726937471409)
                ·
                  refine ⟨25259136704555045203103557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33678848939406726937471409 25259136704555045203103557)
                  ·
                    refine ⟨4736088132104070975581917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25259136704555045203103557 4736088132104070975581917)
                    ·
                      refine ⟨1776033049539026615843219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736088132104070975581917 1776033049539026615843219)
                      ·
                        rfl

theorem cell23_3458812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_3458812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458812 prefixEnd_3458812 := by exact prefixLift 3458812
  have htrace : WordTrace (prefixWord ++ tailWord_3458812) baseStart_3458812 baseEnd_3458812 := by
    simpa [prefixWord, tailWord_3458812, baseEnd_3458812] using wordTrace_append hprefix tailTrace_3458812
  have hstable : (prefixWord ++ tailWord_3458812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458812).length < 2 ^ (prefixWord ++ tailWord_3458812).sum := by decide
  have hdescent : baseEnd_3458812 < baseStart_3458812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458866 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_3458866 : Nat := 118140960795 + 3458866 * 2 ^ 59
def prefixEnd_3458866 : Nat := 4983230072969 + 3 ^ 40 * 3458866 * 2
def baseEnd_3458866 : Nat := 197340086388263267174219

theorem tailTrace_3458866 : CollatzResearch.WordTrace tailWord_3458866 prefixEnd_3458866 197340086388263267174219 := by
  unfold tailWord_3458866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31538801771781671031927113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84103471391417789418472301 31538801771781671031927113)
  ·
    refine ⟨23654101328836253273945335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31538801771781671031927113 23654101328836253273945335)
    ·
      refine ⟨35481151993254379910918003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23654101328836253273945335 35481151993254379910918003)
      ·
        refine ⟨53221727989881569866377005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35481151993254379910918003 53221727989881569866377005)
        ·
          refine ⟨19958147996205588699891377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53221727989881569866377005 19958147996205588699891377)
          ·
            refine ⟨14968610997154191524918533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19958147996205588699891377 14968610997154191524918533)
            ·
              refine ⟨2806614561966410910922225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14968610997154191524918533 2806614561966410910922225)
              ·
                refine ⟨2104960921474808183191669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806614561966410910922225 2104960921474808183191669)
                ·
                  refine ⟨197340086388263267174219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2104960921474808183191669 197340086388263267174219)
                  ·
                    rfl

theorem cell23_3458866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_3458866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458866 prefixEnd_3458866 := by exact prefixLift 3458866
  have htrace : WordTrace (prefixWord ++ tailWord_3458866) baseStart_3458866 baseEnd_3458866 := by
    simpa [prefixWord, tailWord_3458866, baseEnd_3458866] using wordTrace_append hprefix tailTrace_3458866
  have hstable : (prefixWord ++ tailWord_3458866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458866).length < 2 ^ (prefixWord ++ tailWord_3458866).sum := by decide
  have hdescent : baseEnd_3458866 < baseStart_3458866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458872 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_3458872 : Nat := 118140960795 + 3458872 * 2 ^ 59
def prefixEnd_3458872 : Nat := 4983230072969 + 3 ^ 40 * 3458872 * 2
def baseEnd_3458872 : Nat := 1776063858378296381092943

theorem tailTrace_3458872 : CollatzResearch.WordTrace tailWord_3458872 prefixEnd_3458872 1776063858378296381092943 := by
  unfold tailWord_3458872
  simp only [CollatzResearch.WordTrace]
  refine ⟨63077712962552473576213435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84103617283403298101617913 63077712962552473576213435)
  ·
    refine ⟨94616569443828710364320153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63077712962552473576213435 94616569443828710364320153)
    ·
      refine ⟨70962427082871532773240115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94616569443828710364320153 70962427082871532773240115)
      ·
        refine ⟨106443640624307299159860173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70962427082871532773240115 106443640624307299159860173)
        ·
          refine ⟨39916365234115237184947565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106443640624307299159860173 39916365234115237184947565)
          ·
            refine ⟨14968636962793213944355337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39916365234115237184947565 14968636962793213944355337)
            ·
              refine ⟨11226477722094910458266503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14968636962793213944355337 11226477722094910458266503)
              ·
                refine ⟨16839716583142365687399755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11226477722094910458266503 16839716583142365687399755)
                ·
                  refine ⟨25259574874713548531099633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16839716583142365687399755 25259574874713548531099633)
                  ·
                    refine ⟨18944681156035161398324725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25259574874713548531099633 18944681156035161398324725)
                    ·
                      refine ⟨1776063858378296381092943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18944681156035161398324725 1776063858378296381092943)
                      ·
                        rfl

theorem cell23_3458872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_3458872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458872 prefixEnd_3458872 := by exact prefixLift 3458872
  have htrace : WordTrace (prefixWord ++ tailWord_3458872) baseStart_3458872 baseEnd_3458872 := by
    simpa [prefixWord, tailWord_3458872, baseEnd_3458872] using wordTrace_append hprefix tailTrace_3458872
  have hstable : (prefixWord ++ tailWord_3458872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458872).length < 2 ^ (prefixWord ++ tailWord_3458872).sum := by decide
  have hdescent : baseEnd_3458872 < baseStart_3458872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458912 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_3458912 : Nat := 118140960795 + 3458912 * 2 ^ 59
def prefixEnd_3458912 : Nat := 4983230072969 + 3 ^ 40 * 3458912 * 2
def baseEnd_3458912 : Nat := 1776084397604476224592759

theorem tailTrace_3458912 : CollatzResearch.WordTrace tailWord_3458912 prefixEnd_3458912 1776084397604476224592759 := by
  unfold tailWord_3458912
  simp only [CollatzResearch.WordTrace]
  refine ⟨63078442422480016991941495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84104589896640022655921993 63078442422480016991941495)
  ·
    refine ⟨94617663633720025487912243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63078442422480016991941495 94617663633720025487912243)
    ·
      refine ⟨141926495450580038231868365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94617663633720025487912243 141926495450580038231868365)
      ·
        refine ⟨53222435793967514336950637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141926495450580038231868365 53222435793967514336950637)
        ·
          refine ⟨19958413422737817876356489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53222435793967514336950637 19958413422737817876356489)
          ·
            refine ⟨14968810067053363407267367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19958413422737817876356489 14968810067053363407267367)
            ·
              refine ⟨22453215100580045110901051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14968810067053363407267367 22453215100580045110901051)
              ·
                refine ⟨33679822650870067666351577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22453215100580045110901051 33679822650870067666351577)
                ·
                  refine ⟨25259866988152550749763683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33679822650870067666351577 25259866988152550749763683)
                  ·
                    refine ⟨37889800482228826124645525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25259866988152550749763683 37889800482228826124645525)
                    ·
                      refine ⟨1776084397604476224592759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37889800482228826124645525 1776084397604476224592759)
                      ·
                        rfl

theorem cell23_3458912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_3458912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458912 prefixEnd_3458912 := by exact prefixLift 3458912
  have htrace : WordTrace (prefixWord ++ tailWord_3458912) baseStart_3458912 baseEnd_3458912 := by
    simpa [prefixWord, tailWord_3458912, baseEnd_3458912] using wordTrace_append hprefix tailTrace_3458912
  have hstable : (prefixWord ++ tailWord_3458912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458912).length < 2 ^ (prefixWord ++ tailWord_3458912).sum := by decide
  have hdescent : baseEnd_3458912 < baseStart_3458912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458919 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3458919 : Nat := 118140960795 + 3458919 * 2 ^ 59
def prefixEnd_3458919 : Nat := 4983230072969 + 3 ^ 40 * 3458919 * 2
def baseEnd_3458919 : Nat := 1776087991969057697205227

theorem tailTrace_3458919 : CollatzResearch.WordTrace tailWord_3458919 prefixEnd_3458919 1776087991969057697205227 := by
  unfold tailWord_3458919
  simp only [CollatzResearch.WordTrace]
  refine ⟨126157140155934674179387811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84104760103956449452925207 126157140155934674179387811)
  ·
    refine ⟨189235710233902011269081717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126157140155934674179387811 189235710233902011269081717)
    ·
      refine ⟨17740847834428313556476411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189235710233902011269081717 17740847834428313556476411)
      ·
        refine ⟨26611271751642470334714617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17740847834428313556476411 26611271751642470334714617)
        ·
          refine ⟨19958453813731852751035963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26611271751642470334714617 19958453813731852751035963)
          ·
            refine ⟨29937680720597779126553945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19958453813731852751035963 29937680720597779126553945)
            ·
              refine ⟨22453260540448334344915459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29937680720597779126553945 22453260540448334344915459)
              ·
                refine ⟨33679890810672501517373189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22453260540448334344915459 33679890810672501517373189)
                ·
                  refine ⟨6314979527001094034507473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33679890810672501517373189 6314979527001094034507473)
                  ·
                    refine ⟨4736234645250820525880605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314979527001094034507473 4736234645250820525880605)
                    ·
                      refine ⟨1776087991969057697205227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736234645250820525880605 1776087991969057697205227)
                      ·
                        rfl

theorem cell23_3458919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3458919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458919 prefixEnd_3458919 := by exact prefixLift 3458919
  have htrace : WordTrace (prefixWord ++ tailWord_3458919) baseStart_3458919 baseEnd_3458919 := by
    simpa [prefixWord, tailWord_3458919, baseEnd_3458919] using wordTrace_append hprefix tailTrace_3458919
  have hstable : (prefixWord ++ tailWord_3458919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458919).length < 2 ^ (prefixWord ++ tailWord_3458919).sum := by decide
  have hdescent : baseEnd_3458919 < baseStart_3458919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458926 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3458926 : Nat := 118140960795 + 3458926 * 2 ^ 59
def prefixEnd_3458926 : Nat := 4983230072969 + 3 ^ 40 * 3458926 * 2
def baseEnd_3458926 : Nat := 592030528777879723272565

theorem tailTrace_3458926 : CollatzResearch.WordTrace tailWord_3458926 prefixEnd_3458926 592030528777879723272565 := by
  unfold tailWord_3458926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15769674433363664296861579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84104930311272876249928421 15769674433363664296861579)
  ·
    refine ⟨23654511650045496445292369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15769674433363664296861579 23654511650045496445292369)
    ·
      refine ⟨17740883737534122333969277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23654511650045496445292369 17740883737534122333969277)
      ·
        refine ⟨6652831401575295875238479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17740883737534122333969277 6652831401575295875238479)
        ·
          refine ⟨9979247102362943812857719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6652831401575295875238479 9979247102362943812857719)
          ·
            refine ⟨14968870653544415719286579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9979247102362943812857719 14968870653544415719286579)
            ·
              refine ⟨22453305980316623578929869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14968870653544415719286579 22453305980316623578929869)
              ·
                refine ⟨8419989742618733842098701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22453305980316623578929869 8419989742618733842098701)
                ·
                  refine ⟨3157496153482025190787013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8419989742618733842098701 3157496153482025190787013)
                  ·
                    refine ⟨592030528777879723272565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157496153482025190787013 592030528777879723272565)
                    ·
                      rfl

theorem cell23_3458926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3458926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458926 prefixEnd_3458926 := by exact prefixLift 3458926
  have htrace : WordTrace (prefixWord ++ tailWord_3458926) baseStart_3458926 baseEnd_3458926 := by
    simpa [prefixWord, tailWord_3458926, baseEnd_3458926] using wordTrace_append hprefix tailTrace_3458926
  have hstable : (prefixWord ++ tailWord_3458926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458926).length < 2 ^ (prefixWord ++ tailWord_3458926).sum := by decide
  have hdescent : baseEnd_3458926 < baseStart_3458926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458969 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 1, 5]
def baseStart_3458969 : Nat := 118140960795 + 3458969 * 2 ^ 59
def prefixEnd_3458969 : Nat := 4983230072969 + 3 ^ 40 * 3458969 * 2
def baseEnd_3458969 : Nat := 592037888667260833859999

theorem tailTrace_3458969 : CollatzResearch.WordTrace tailWord_3458969 prefixEnd_3458969 592037888667260833859999 := by
  unfold tailWord_3458969
  simp only [CollatzResearch.WordTrace]
  refine ⟨126158963805753532718707961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84105975870502355145805307 126158963805753532718707961)
  ·
    refine ⟨94619222854315149539030971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126158963805753532718707961 94619222854315149539030971)
    ·
      refine ⟨141928834281472724308546457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94619222854315149539030971 141928834281472724308546457)
      ·
        refine ⟨106446625711104543231409843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141928834281472724308546457 106446625711104543231409843)
        ·
          refine ⟨159669938566656814847114765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106446625711104543231409843 159669938566656814847114765)
          ·
            refine ⟨59876226962496305567668037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159669938566656814847114765 59876226962496305567668037)
            ·
              refine ⟨11226792555468057293937757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59876226962496305567668037 11226792555468057293937757)
              ·
                refine ⟨4210047208300521485226659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11226792555468057293937757 4210047208300521485226659)
                ·
                  refine ⟨6315070812450782227839989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210047208300521485226659 6315070812450782227839989)
                  ·
                    refine ⟨592037888667260833859999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6315070812450782227839989 592037888667260833859999)
                    ·
                      rfl

theorem cell23_3458969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_3458969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458969 prefixEnd_3458969 := by exact prefixLift 3458969
  have htrace : WordTrace (prefixWord ++ tailWord_3458969) baseStart_3458969 baseEnd_3458969 := by
    simpa [prefixWord, tailWord_3458969, baseEnd_3458969] using wordTrace_append hprefix tailTrace_3458969
  have hstable : (prefixWord ++ tailWord_3458969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458969).length < 2 ^ (prefixWord ++ tailWord_3458969).sum := by decide
  have hdescent : baseEnd_3458969 < baseStart_3458969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458983 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3458983 : Nat := 118140960795 + 3458983 * 2 ^ 59
def prefixEnd_3458983 : Nat := 4983230072969 + 3 ^ 40 * 3458983 * 2
def baseEnd_3458983 : Nat := 1776120854730945446804933

theorem tailTrace_3458983 : CollatzResearch.WordTrace tailWord_3458983 prefixEnd_3458983 1776120854730945446804933 := by
  unfold tailWord_3458983
  simp only [CollatzResearch.WordTrace]
  refine ⟨126159474427702813109717603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84106316285135208739811735 126159474427702813109717603)
  ·
    refine ⟨189239211641554219664576405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126159474427702813109717603 189239211641554219664576405)
    ·
      refine ⟨8870588045697854046777019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189239211641554219664576405 8870588045697854046777019)
      ·
        refine ⟨13305882068546781070165529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870588045697854046777019 13305882068546781070165529)
        ·
          refine ⟨9979411551410085802624147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13305882068546781070165529 9979411551410085802624147)
          ·
            refine ⟨14969117327115128703936221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9979411551410085802624147 14969117327115128703936221)
            ·
              refine ⟨5613418997668173263976083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14969117327115128703936221 5613418997668173263976083)
              ·
                refine ⟨8420128496502259895964125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613418997668173263976083 8420128496502259895964125)
                ·
                  refine ⟨3157548186188347460986547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8420128496502259895964125 3157548186188347460986547)
                  ·
                    refine ⟨4736322279282521191479821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3157548186188347460986547 4736322279282521191479821)
                    ·
                      refine ⟨1776120854730945446804933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736322279282521191479821 1776120854730945446804933)
                      ·
                        rfl

theorem cell23_3458983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3458983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458983 prefixEnd_3458983 := by exact prefixLift 3458983
  have htrace : WordTrace (prefixWord ++ tailWord_3458983) baseStart_3458983 baseEnd_3458983 := by
    simpa [prefixWord, tailWord_3458983, baseEnd_3458983] using wordTrace_append hprefix tailTrace_3458983
  have hstable : (prefixWord ++ tailWord_3458983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458983).length < 2 ^ (prefixWord ++ tailWord_3458983).sum := by decide
  have hdescent : baseEnd_3458983 < baseStart_3458983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458990 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_3458990 : Nat := 118140960795 + 3458990 * 2 ^ 59
def prefixEnd_3458990 : Nat := 4983230072969 + 3 ^ 40 * 3458990 * 2
def baseEnd_3458990 : Nat := 197347161010614102157489

theorem tailTrace_3458990 : CollatzResearch.WordTrace tailWord_3458990 prefixEnd_3458990 197347161010614102157489 := by
  unfold tailWord_3458990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15769966217334681663152803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84106486492451635536814949 15769966217334681663152803)
  ·
    refine ⟨23654949326002022494729205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15769966217334681663152803 23654949326002022494729205)
    ·
      refine ⟨2217651499312689608880863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23654949326002022494729205 2217651499312689608880863)
      ·
        refine ⟨3326477248969034413321295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217651499312689608880863 3326477248969034413321295)
        ·
          refine ⟨4989715873453551619981943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326477248969034413321295 4989715873453551619981943)
          ·
            refine ⟨7484573810180327429972915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989715873453551619981943 7484573810180327429972915)
            ·
              refine ⟨11226860715270491144959373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484573810180327429972915 11226860715270491144959373)
              ·
                refine ⟨4210072768226434179359765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11226860715270491144959373 4210072768226434179359765)
                ·
                  refine ⟨197347161010614102157489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4210072768226434179359765 197347161010614102157489)
                  ·
                    rfl

theorem cell23_3458990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_3458990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3458990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3458990 prefixEnd_3458990 := by exact prefixLift 3458990
  have htrace : WordTrace (prefixWord ++ tailWord_3458990) baseStart_3458990 baseEnd_3458990 := by
    simpa [prefixWord, tailWord_3458990, baseEnd_3458990] using wordTrace_append hprefix tailTrace_3458990
  have hstable : (prefixWord ++ tailWord_3458990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458990).length < 2 ^ (prefixWord ++ tailWord_3458990).sum := by decide
  have hdescent : baseEnd_3458990 < baseStart_3458990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459006 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3459006 : Nat := 118140960795 + 3459006 * 2 ^ 59
def prefixEnd_3459006 : Nat := 4983230072969 + 3 ^ 40 * 3459006 * 2
def baseEnd_3459006 : Nat := 1776132664785998856817327

theorem tailTrace_3459006 : CollatzResearch.WordTrace tailWord_3459006 prefixEnd_3459006 1776132664785998856817327 := by
  unfold tailWord_3459006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15770039163327436004725609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84106875537746325358536581 15770039163327436004725609)
  ·
    refine ⟨11827529372495577003544207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15770039163327436004725609 11827529372495577003544207)
    ·
      refine ⟨17741294058743365505316311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827529372495577003544207 17741294058743365505316311)
      ·
        refine ⟨26611941088115048257974467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17741294058743365505316311 26611941088115048257974467)
        ·
          refine ⟨39917911632172572386961701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26611941088115048257974467 39917911632172572386961701)
          ·
            refine ⟨7484608431032357322555319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39917911632172572386961701 7484608431032357322555319)
            ·
              refine ⟨11226912646548535983832979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484608431032357322555319 11226912646548535983832979)
              ·
                refine ⟨16840368969822803975749469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11226912646548535983832979 16840368969822803975749469)
                ·
                  refine ⟨6315138363683551490906051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16840368969822803975749469 6315138363683551490906051)
                  ·
                    refine ⟨9472707545525327236359077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6315138363683551490906051 9472707545525327236359077)
                    ·
                      refine ⟨1776132664785998856817327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9472707545525327236359077 1776132664785998856817327)
                      ·
                        rfl

theorem cell23_3459006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3459006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459006 prefixEnd_3459006 := by exact prefixLift 3459006
  have htrace : WordTrace (prefixWord ++ tailWord_3459006) baseStart_3459006 baseEnd_3459006 := by
    simpa [prefixWord, tailWord_3459006, baseEnd_3459006] using wordTrace_append hprefix tailTrace_3459006
  have hstable : (prefixWord ++ tailWord_3459006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459006).length < 2 ^ (prefixWord ++ tailWord_3459006).sum := by decide
  have hdescent : baseEnd_3459006 < baseStart_3459006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459019 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4]
def baseStart_3459019 : Nat := 118140960795 + 3459019 * 2 ^ 59
def prefixEnd_3459019 : Nat := 4983230072969 + 3 ^ 40 * 3459019 * 2
def baseEnd_3459019 : Nat := 1776139340034507305954767

theorem tailTrace_3459019 : CollatzResearch.WordTrace tailWord_3459019 prefixEnd_3459019 1776139340034507305954767 := by
  unfold tailWord_3459019
  simp only [CollatzResearch.WordTrace]
  refine ⟨126160787455572391258028111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84107191637048260838685407 126160787455572391258028111)
  ·
    refine ⟨189241181183358586887042167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126160787455572391258028111 189241181183358586887042167)
    ·
      refine ⟨283861771775037880330563251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189241181183358586887042167 283861771775037880330563251)
      ·
        refine ⟨425792657662556820495844877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283861771775037880330563251 425792657662556820495844877)
        ·
          refine ⟨159672246623458807685941829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425792657662556820495844877 159672246623458807685941829)
          ·
            refine ⟨29938546241898526441114093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159672246623458807685941829 29938546241898526441114093)
            ·
              refine ⟨11226954840711947415417785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29938546241898526441114093 11226954840711947415417785)
              ·
                refine ⟨8420216130533960561563339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11226954840711947415417785 8420216130533960561563339)
                ·
                  refine ⟨12630324195800940842345009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8420216130533960561563339 12630324195800940842345009)
                  ·
                    refine ⟨9472743146850705631758757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12630324195800940842345009 9472743146850705631758757)
                    ·
                      refine ⟨1776139340034507305954767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9472743146850705631758757 1776139340034507305954767)
                      ·
                        rfl

theorem cell23_3459019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].length) (baseStart_3459019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459019 prefixEnd_3459019 := by exact prefixLift 3459019
  have htrace : WordTrace (prefixWord ++ tailWord_3459019) baseStart_3459019 baseEnd_3459019 := by
    simpa [prefixWord, tailWord_3459019, baseEnd_3459019] using wordTrace_append hprefix tailTrace_3459019
  have hstable : (prefixWord ++ tailWord_3459019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459019).length < 2 ^ (prefixWord ++ tailWord_3459019).sum := by decide
  have hdescent : baseEnd_3459019 < baseStart_3459019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459033 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 2, 4]
def baseStart_3459033 : Nat := 118140960795 + 3459033 * 2 ^ 59
def prefixEnd_3459033 : Nat := 4983230072969 + 3 ^ 40 * 3459033 * 2
def baseEnd_3459033 : Nat := 592048842921223417059901

theorem tailTrace_3459033 : CollatzResearch.WordTrace tailWord_3459033 prefixEnd_3459033 592048842921223417059901 := by
  unfold tailWord_3459033
  simp only [CollatzResearch.WordTrace]
  refine ⟨126161298077521671649037753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84107532051681114432691835 126161298077521671649037753)
  ·
    refine ⟨94620973558141253736778315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126161298077521671649037753 94620973558141253736778315)
    ·
      refine ⟨141931460337211880605167473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94620973558141253736778315 141931460337211880605167473)
      ·
        refine ⟨106448595252908910453875605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141931460337211880605167473 106448595252908910453875605)
        ·
          refine ⟨4989777902480105177525419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106448595252908910453875605 4989777902480105177525419)
          ·
            refine ⟨7484666853720157766288129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989777902480105177525419 7484666853720157766288129)
            ·
              refine ⟨5613500140290118324716097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7484666853720157766288129 5613500140290118324716097)
              ·
                refine ⟨4210125105217588743537073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613500140290118324716097 4210125105217588743537073)
                ·
                  refine ⟨3157593828913191557652805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210125105217588743537073 3157593828913191557652805)
                  ·
                    refine ⟨592048842921223417059901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157593828913191557652805 592048842921223417059901)
                    ·
                      rfl

theorem cell23_3459033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_3459033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459033 prefixEnd_3459033 := by exact prefixLift 3459033
  have htrace : WordTrace (prefixWord ++ tailWord_3459033) baseStart_3459033 baseEnd_3459033 := by
    simpa [prefixWord, tailWord_3459033, baseEnd_3459033] using wordTrace_append hprefix tailTrace_3459033
  have hstable : (prefixWord ++ tailWord_3459033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459033).length < 2 ^ (prefixWord ++ tailWord_3459033).sum := by decide
  have hdescent : baseEnd_3459033 < baseStart_3459033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459034 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3]
def baseStart_3459034 : Nat := 118140960795 + 3459034 * 2 ^ 59
def prefixEnd_3459034 : Nat := 4983230072969 + 3 ^ 40 * 3459034 * 2
def baseEnd_3459034 : Nat := 1776147042244324747267199

theorem tailTrace_3459034 : CollatzResearch.WordTrace tailWord_3459034 prefixEnd_3459034 1776147042244324747267199 := by
  unfold tailWord_3459034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31540333637629512204956039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84107556367012032546549437 31540333637629512204956039)
  ·
    refine ⟨47310500456444268307434059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31540333637629512204956039 47310500456444268307434059)
    ·
      refine ⟨70965750684666402461151089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47310500456444268307434059 70965750684666402461151089)
      ·
        refine ⟨53224313013499801845863317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70965750684666402461151089 53224313013499801845863317)
        ·
          refine ⟨2494889672507803211524843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53224313013499801845863317 2494889672507803211524843)
          ·
            refine ⟨3742334508761704817287265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494889672507803211524843 3742334508761704817287265)
            ·
              refine ⟨2806750881571278612965449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742334508761704817287265 2806750881571278612965449)
              ·
                refine ⟨2105063161178458959724087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806750881571278612965449 2105063161178458959724087)
                ·
                  refine ⟨3157594741767688439586131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105063161178458959724087 3157594741767688439586131)
                  ·
                    refine ⟨4736392112651532659379197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3157594741767688439586131 4736392112651532659379197)
                    ·
                      refine ⟨1776147042244324747267199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736392112651532659379197 1776147042244324747267199)
                      ·
                        rfl

theorem cell23_3459034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_3459034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459034 prefixEnd_3459034 := by exact prefixLift 3459034
  have htrace : WordTrace (prefixWord ++ tailWord_3459034) baseStart_3459034 baseEnd_3459034 := by
    simpa [prefixWord, tailWord_3459034, baseEnd_3459034] using wordTrace_append hprefix tailTrace_3459034
  have hstable : (prefixWord ++ tailWord_3459034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459034).length < 2 ^ (prefixWord ++ tailWord_3459034).sum := by decide
  have hdescent : baseEnd_3459034 < baseStart_3459034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459083 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 1, 3, 2]
def baseStart_3459083 : Nat := 118140960795 + 3459083 * 2 ^ 59
def prefixEnd_3459083 : Nat := 4983230072969 + 3 ^ 40 * 3459083 * 2
def baseEnd_3459083 : Nat := 1776172202796395055554473

theorem tailTrace_3459083 : CollatzResearch.WordTrace tailWord_3459083 prefixEnd_3459083 1776172202796395055554473 := by
  unfold tailWord_3459083
  simp only [CollatzResearch.WordTrace]
  refine ⟨126163121727340530188357903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84108747818227020125571935 126163121727340530188357903)
  ·
    refine ⟨189244682591010795282536855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126163121727340530188357903 189244682591010795282536855)
    ·
      refine ⟨283867023886516192923805283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189244682591010795282536855 283867023886516192923805283)
      ·
        refine ⟨425800535829774289385707925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283867023886516192923805283 425800535829774289385707925)
        ·
          refine ⟨19959400117020669814955059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 425800535829774289385707925 19959400117020669814955059)
          ·
            refine ⟨29939100175531004722432589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19959400117020669814955059 29939100175531004722432589)
            ·
              refine ⟨11227162565824126770912221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29939100175531004722432589 11227162565824126770912221)
              ·
                refine ⟨4210185962184047539092083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11227162565824126770912221 4210185962184047539092083)
                ·
                  refine ⟨6315278943276071308638125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210185962184047539092083 6315278943276071308638125)
                  ·
                    refine ⟨2368229603728526740739297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6315278943276071308638125 2368229603728526740739297)
                    ·
                      refine ⟨1776172202796395055554473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368229603728526740739297 1776172202796395055554473)
                      ·
                        rfl

theorem cell23_3459083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 3, 2].length) (baseStart_3459083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459083 prefixEnd_3459083 := by exact prefixLift 3459083
  have htrace : WordTrace (prefixWord ++ tailWord_3459083) baseStart_3459083 baseEnd_3459083 := by
    simpa [prefixWord, tailWord_3459083, baseEnd_3459083] using wordTrace_append hprefix tailTrace_3459083
  have hstable : (prefixWord ++ tailWord_3459083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459083).length < 2 ^ (prefixWord ++ tailWord_3459083).sum := by decide
  have hdescent : baseEnd_3459083 < baseStart_3459083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459099 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 3]
def baseStart_3459099 : Nat := 118140960795 + 3459099 * 2 ^ 59
def prefixEnd_3459099 : Nat := 4983230072969 + 3 ^ 40 * 3459099 * 2
def baseEnd_3459099 : Nat := 1776180418486866992954399

theorem tailTrace_3459099 : CollatzResearch.WordTrace tailWord_3459099 prefixEnd_3459099 1776180418486866992954399 := by
  unfold tailWord_3459099
  simp only [CollatzResearch.WordTrace]
  refine ⟨126163705295282564920940351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84109136863521709947293567 126163705295282564920940351)
  ·
    refine ⟨189245557942923847381410527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126163705295282564920940351 189245557942923847381410527)
    ·
      refine ⟨283868336914385771072115791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189245557942923847381410527 283868336914385771072115791)
      ·
        refine ⟨425802505371578656608173687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283868336914385771072115791 425802505371578656608173687)
        ·
          refine ⟨638703758057367984912260531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425802505371578656608173687 638703758057367984912260531)
          ·
            refine ⟨958055637086051977368390797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638703758057367984912260531 958055637086051977368390797)
            ·
              refine ⟨359270863907269491513146549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 958055637086051977368390797 359270863907269491513146549)
              ·
                refine ⟨33681643491306514829357489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359270863907269491513146549 33681643491306514829357489)
                ·
                  refine ⟨25261232618479886122018117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33681643491306514829357489 25261232618479886122018117)
                  ·
                    refine ⟨4736481115964978647878397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25261232618479886122018117 4736481115964978647878397)
                    ·
                      refine ⟨1776180418486866992954399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736481115964978647878397 1776180418486866992954399)
                      ·
                        rfl

theorem cell23_3459099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 3].length) (baseStart_3459099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459099 prefixEnd_3459099 := by exact prefixLift 3459099
  have htrace : WordTrace (prefixWord ++ tailWord_3459099) baseStart_3459099 baseEnd_3459099 := by
    simpa [prefixWord, tailWord_3459099, baseEnd_3459099] using wordTrace_append hprefix tailTrace_3459099
  have hstable : (prefixWord ++ tailWord_3459099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459099).length < 2 ^ (prefixWord ++ tailWord_3459099).sum := by decide
  have hdescent : baseEnd_3459099 < baseStart_3459099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459159 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_3459159 : Nat := 118140960795 + 3459159 * 2 ^ 59
def prefixEnd_3459159 : Nat := 4983230072969 + 3 ^ 40 * 3459159 * 2
def baseEnd_3459159 : Nat := 1776211227326136758204123

theorem tailTrace_3459159 : CollatzResearch.WordTrace tailWord_3459159 prefixEnd_3459159 1776211227326136758204123 := by
  unfold tailWord_3459159
  simp only [CollatzResearch.WordTrace]
  refine ⟨126165893675065195168124531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84110595783376796778749687 126165893675065195168124531)
  ·
    refine ⟨189248840512597792752186797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126165893675065195168124531 189248840512597792752186797)
    ·
      refine ⟨70968315192224172282070049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189248840512597792752186797 70968315192224172282070049)
      ·
        refine ⟨53226236394168129211552537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70968315192224172282070049 53226236394168129211552537)
        ·
          refine ⟨39919677295626096908664403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53226236394168129211552537 39919677295626096908664403)
          ·
            refine ⟨59879515943439145362996605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39919677295626096908664403 59879515943439145362996605)
            ·
              refine ⟨22454818478789679511123727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59879515943439145362996605 22454818478789679511123727)
              ·
                refine ⟨33682227718184519266685591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22454818478789679511123727 33682227718184519266685591)
                ·
                  refine ⟨50523341577276778900028387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33682227718184519266685591 50523341577276778900028387)
                  ·
                    refine ⟨75785012365915168350042581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50523341577276778900028387 75785012365915168350042581)
                    ·
                      refine ⟨1776211227326136758204123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75785012365915168350042581 1776211227326136758204123)
                      ·
                        rfl

theorem cell23_3459159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_3459159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459159 prefixEnd_3459159 := by exact prefixLift 3459159
  have htrace : WordTrace (prefixWord ++ tailWord_3459159) baseStart_3459159 baseEnd_3459159 := by
    simpa [prefixWord, tailWord_3459159, baseEnd_3459159] using wordTrace_append hprefix tailTrace_3459159
  have hstable : (prefixWord ++ tailWord_3459159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459159).length < 2 ^ (prefixWord ++ tailWord_3459159).sum := by decide
  have hdescent : baseEnd_3459159 < baseStart_3459159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459164 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_3459164 : Nat := 118140960795 + 3459164 * 2 ^ 59
def prefixEnd_3459164 : Nat := 4983230072969 + 3 ^ 40 * 3459164 * 2
def baseEnd_3459164 : Nat := 1776213794729409238641601

theorem tailTrace_3459164 : CollatzResearch.WordTrace tailWord_3459164 prefixEnd_3459164 1776213794729409238641601 := by
  unfold tailWord_3459164
  simp only [CollatzResearch.WordTrace]
  refine ⟨63083038020023540511028273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84110717360031387348037697 63083038020023540511028273)
  ·
    refine ⟨47312278515017655383271205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63083038020023540511028273 47312278515017655383271205)
    ·
      refine ⟨8871052221565810384363351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47312278515017655383271205 8871052221565810384363351)
      ·
        refine ⟨13306578332348715576545027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8871052221565810384363351 13306578332348715576545027)
        ·
          refine ⟨19959867498523073364817541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306578332348715576545027 19959867498523073364817541)
          ·
            refine ⟨3742475155973076255903289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19959867498523073364817541 3742475155973076255903289)
            ·
              refine ⟨2806856366979807191927467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742475155973076255903289 2806856366979807191927467)
              ·
                refine ⟨4210284550469710787891201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806856366979807191927467 4210284550469710787891201)
                ·
                  refine ⟨3157713412852283090918401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210284550469710787891201 3157713412852283090918401)
                  ·
                    refine ⟨2368285059639212318188801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3157713412852283090918401 2368285059639212318188801)
                    ·
                      refine ⟨1776213794729409238641601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368285059639212318188801 1776213794729409238641601)
                      ·
                        rfl

theorem cell23_3459164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_3459164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459164 prefixEnd_3459164 := by exact prefixLift 3459164
  have htrace : WordTrace (prefixWord ++ tailWord_3459164) baseStart_3459164 baseEnd_3459164 := by
    simpa [prefixWord, tailWord_3459164, baseEnd_3459164] using wordTrace_append hprefix tailTrace_3459164
  have hstable : (prefixWord ++ tailWord_3459164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459164).length < 2 ^ (prefixWord ++ tailWord_3459164).sum := by decide
  have hdescent : baseEnd_3459164 < baseStart_3459164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459260 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 6]
def baseStart_3459260 : Nat := 118140960795 + 3459260 * 2 ^ 59
def prefixEnd_3459260 : Nat := 4983230072969 + 3 ^ 40 * 3459260 * 2
def baseEnd_3459260 : Nat := 197362565430248984782351

theorem tailTrace_3459260 : CollatzResearch.WordTrace tailWord_3459260 prefixEnd_3459260 197362565430248984782351 := by
  unfold tailWord_3459260
  simp only [CollatzResearch.WordTrace]
  refine ⟨63084788723849644708775617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84113051631799526278367489 63084788723849644708775617)
  ·
    refine ⟨47313591542887233531581713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63084788723849644708775617 47313591542887233531581713)
    ·
      refine ⟨35485193657165425148686285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47313591542887233531581713 35485193657165425148686285)
      ·
        refine ⟨13306947621437034430757357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35485193657165425148686285 13306947621437034430757357)
        ·
          refine ⟨4990105358038887911534009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13306947621437034430757357 4990105358038887911534009)
          ·
            refine ⟨3742579018529165933650507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990105358038887911534009 3742579018529165933650507)
            ·
              refine ⟨5613868527793748900475761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742579018529165933650507 5613868527793748900475761)
              ·
                refine ⟨4210401395845311675356821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613868527793748900475761 4210401395845311675356821)
                ·
                  refine ⟨197362565430248984782351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4210401395845311675356821 197362565430248984782351)
                  ·
                    rfl

theorem cell23_3459260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_3459260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459260 prefixEnd_3459260 := by exact prefixLift 3459260
  have htrace : WordTrace (prefixWord ++ tailWord_3459260) baseStart_3459260 baseEnd_3459260 := by
    simpa [prefixWord, tailWord_3459260, baseEnd_3459260] using wordTrace_append hprefix tailTrace_3459260
  have hstable : (prefixWord ++ tailWord_3459260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459260).length < 2 ^ (prefixWord ++ tailWord_3459260).sum := by decide
  have hdescent : baseEnd_3459260 < baseStart_3459260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459263 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 4, 3, 2]
def baseStart_3459263 : Nat := 118140960795 + 3459263 * 2 ^ 59
def prefixEnd_3459263 : Nat := 4983230072969 + 3 ^ 40 * 3459263 * 2
def baseEnd_3459263 : Nat := 1776264629314204351303645

theorem tailTrace_3459263 : CollatzResearch.WordTrace tailWord_3459263 prefixEnd_3459263 1776264629314204351303645 := by
  unfold tailWord_3459263
  simp only [CollatzResearch.WordTrace]
  refine ⟨126169686866688420929910443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84113124577792280619940295 126169686866688420929910443)
  ·
    refine ⟨189254530300032631394865665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126169686866688420929910443 189254530300032631394865665)
    ·
      refine ⟨141940897725024473546149249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189254530300032631394865665 141940897725024473546149249)
      ·
        refine ⟨106455673293768355159611937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141940897725024473546149249 106455673293768355159611937)
        ·
          refine ⟨79841754970326266369708953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106455673293768355159611937 79841754970326266369708953)
          ·
            refine ⟨59881316227744699777281715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79841754970326266369708953 59881316227744699777281715)
            ·
              refine ⟨89821974341617049665922573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59881316227744699777281715 89821974341617049665922573)
              ·
                refine ⟨33683240378106393624720965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89821974341617049665922573 33683240378106393624720965)
                ·
                  refine ⟨6315607570894948804635181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33683240378106393624720965 6315607570894948804635181)
                  ·
                    refine ⟨2368352839085605801738193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6315607570894948804635181 2368352839085605801738193)
                    ·
                      refine ⟨1776264629314204351303645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368352839085605801738193 1776264629314204351303645)
                      ·
                        rfl

theorem cell23_3459263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_3459263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459263 prefixEnd_3459263 := by exact prefixLift 3459263
  have htrace : WordTrace (prefixWord ++ tailWord_3459263) baseStart_3459263 baseEnd_3459263 := by
    simpa [prefixWord, tailWord_3459263, baseEnd_3459263] using wordTrace_append hprefix tailTrace_3459263
  have hstable : (prefixWord ++ tailWord_3459263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459263).length < 2 ^ (prefixWord ++ tailWord_3459263).sum := by decide
  have hdescent : baseEnd_3459263 < baseStart_3459263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459296 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_3459296 : Nat := 118140960795 + 3459296 * 2 ^ 59
def prefixEnd_3459296 : Nat := 4983230072969 + 3 ^ 40 * 3459296 * 2
def baseEnd_3459296 : Nat := 1776281574175802722190993

theorem tailTrace_3459296 : CollatzResearch.WordTrace tailWord_3459296 prefixEnd_3459296 1776281574175802722190993 := by
  unfold tailWord_3459296
  simp only [CollatzResearch.WordTrace]
  refine ⟨63085445237784433782930871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84113926983712578377241161 63085445237784433782930871)
  ·
    refine ⟨94628167856676650674396307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63085445237784433782930871 94628167856676650674396307)
    ·
      refine ⟨141942251785014976011594461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94628167856676650674396307 141942251785014976011594461)
      ·
        refine ⟨53228344419380616004347923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141942251785014976011594461 53228344419380616004347923)
        ·
          refine ⟨79842516629070924006521885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53228344419380616004347923 79842516629070924006521885)
          ·
            refine ⟨29940943735901596502445707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79842516629070924006521885 29940943735901596502445707)
            ·
              refine ⟨44911415603852394753668561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29940943735901596502445707 44911415603852394753668561)
              ·
                refine ⟨33683561702889296065251421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44911415603852394753668561 33683561702889296065251421)
                ·
                  refine ⟨12631335638583486024469283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33683561702889296065251421 12631335638583486024469283)
                  ·
                    refine ⟨18947003457875229036703925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12631335638583486024469283 18947003457875229036703925)
                    ·
                      refine ⟨1776281574175802722190993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18947003457875229036703925 1776281574175802722190993)
                      ·
                        rfl

theorem cell23_3459296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_3459296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459296 prefixEnd_3459296 := by exact prefixLift 3459296
  have htrace : WordTrace (prefixWord ++ tailWord_3459296) baseStart_3459296 baseEnd_3459296 := by
    simpa [prefixWord, tailWord_3459296, baseEnd_3459296] using wordTrace_append hprefix tailTrace_3459296
  have hstable : (prefixWord ++ tailWord_3459296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459296).length < 2 ^ (prefixWord ++ tailWord_3459296).sum := by decide
  have hdescent : baseEnd_3459296 < baseStart_3459296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459298 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3459298 : Nat := 118140960795 + 3459298 * 2 ^ 59
def prefixEnd_3459298 : Nat := 4983230072969 + 3 ^ 40 * 3459298 * 2
def baseEnd_3459298 : Nat := 592094200379037238121995

theorem tailTrace_3459298 : CollatzResearch.WordTrace tailWord_3459298 prefixEnd_3459298 592094200379037238121995 := by
  unfold tailWord_3459298
  simp only [CollatzResearch.WordTrace]
  refine ⟨31542740855390405476858637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84113975614374414604956365 31542740855390405476858637)
  ·
    refine ⟨11828527820771402053821989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31542740855390405476858637 11828527820771402053821989)
    ·
      refine ⟨2217848966394637885091623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11828527820771402053821989 2217848966394637885091623)
      ·
        refine ⟨3326773449591956827637435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217848966394637885091623 3326773449591956827637435)
        ·
          refine ⟨4990160174387935241456153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326773449591956827637435 4990160174387935241456153)
          ·
            refine ⟨3742620130790951431092115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990160174387935241456153 3742620130790951431092115)
            ·
              refine ⟨5613930196186427146638173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742620130790951431092115 5613930196186427146638173)
              ·
                refine ⟨2105223823569910179989315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613930196186427146638173 2105223823569910179989315)
                ·
                  refine ⟨3157835735354865269983973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105223823569910179989315 3157835735354865269983973)
                  ·
                    refine ⟨592094200379037238121995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157835735354865269983973 592094200379037238121995)
                    ·
                      rfl

theorem cell23_3459298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3459298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459298 prefixEnd_3459298 := by exact prefixLift 3459298
  have htrace : WordTrace (prefixWord ++ tailWord_3459298) baseStart_3459298 baseEnd_3459298 := by
    simpa [prefixWord, tailWord_3459298, baseEnd_3459298] using wordTrace_append hprefix tailTrace_3459298
  have hstable : (prefixWord ++ tailWord_3459298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459298).length < 2 ^ (prefixWord ++ tailWord_3459298).sum := by decide
  have hdescent : baseEnd_3459298 < baseStart_3459298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459304 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_3459304 : Nat := 118140960795 + 3459304 * 2 ^ 59
def prefixEnd_3459304 : Nat := 4983230072969 + 3 ^ 40 * 3459304 * 2
def baseEnd_3459304 : Nat := 1776285682021038690890957

theorem tailTrace_3459304 : CollatzResearch.WordTrace tailWord_3459304 prefixEnd_3459304 1776285682021038690890957 := by
  unfold tailWord_3459304
  simp only [CollatzResearch.WordTrace]
  refine ⟨63085591129769942466076483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84114121506359923288101977 63085591129769942466076483)
  ·
    refine ⟨94628386694654913699114725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63085591129769942466076483 94628386694654913699114725)
    ·
      refine ⟨17742822505247796318584011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94628386694654913699114725 17742822505247796318584011)
      ·
        refine ⟨26614233757871694477876017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17742822505247796318584011 26614233757871694477876017)
        ·
          refine ⟨19960675318403770858407013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26614233757871694477876017 19960675318403770858407013)
          ·
            refine ⟨3742626622200707035951315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19960675318403770858407013 3742626622200707035951315)
            ·
              refine ⟨5613939933301060553926973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742626622200707035951315 5613939933301060553926973)
              ·
                refine ⟨2105227474987897707722615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613939933301060553926973 2105227474987897707722615)
                ·
                  refine ⟨3157841212481846561583923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105227474987897707722615 3157841212481846561583923)
                  ·
                    refine ⟨4736761818722769842375885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3157841212481846561583923 4736761818722769842375885)
                    ·
                      refine ⟨1776285682021038690890957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736761818722769842375885 1776285682021038690890957)
                      ·
                        rfl

theorem cell23_3459304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_3459304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459304 prefixEnd_3459304 := by exact prefixLift 3459304
  have htrace : WordTrace (prefixWord ++ tailWord_3459304) baseStart_3459304 baseEnd_3459304 := by
    simpa [prefixWord, tailWord_3459304, baseEnd_3459304] using wordTrace_append hprefix tailTrace_3459304
  have hstable : (prefixWord ++ tailWord_3459304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459304).length < 2 ^ (prefixWord ++ tailWord_3459304).sum := by decide
  have hdescent : baseEnd_3459304 < baseStart_3459304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459330 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3459330 : Nat := 118140960795 + 3459330 * 2 ^ 59
def prefixEnd_3459330 : Nat := 4983230072969 + 3 ^ 40 * 3459330 * 2
def baseEnd_3459330 : Nat := 1776299032518055589165837

theorem tailTrace_3459330 : CollatzResearch.WordTrace tailWord_3459330 prefixEnd_3459330 1776299032518055589165837 := by
  unfold tailWord_3459330
  simp only [CollatzResearch.WordTrace]
  refine ⟨31543032639361422843149861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84114753704963794248399629 31543032639361422843149861)
  ·
    refine ⟨5914318619880266783090599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31543032639361422843149861 5914318619880266783090599)
    ·
      refine ⟨8871477929820400174635899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5914318619880266783090599 8871477929820400174635899)
      ·
        refine ⟨13307216894730600261953849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8871477929820400174635899 13307216894730600261953849)
        ·
          refine ⟨9980412671047950196465387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13307216894730600261953849 9980412671047950196465387)
          ·
            refine ⟨14970619006571925294698081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9980412671047950196465387 14970619006571925294698081)
            ·
              refine ⟨11227964254928943971023561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14970619006571925294698081 11227964254928943971023561)
              ·
                refine ⟨8420973191196707978267671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11227964254928943971023561 8420973191196707978267671)
                ·
                  refine ⟨12631459786795061967401507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8420973191196707978267671 12631459786795061967401507)
                  ·
                    refine ⟨18947189680192592951102261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12631459786795061967401507 18947189680192592951102261)
                    ·
                      refine ⟨1776299032518055589165837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18947189680192592951102261 1776299032518055589165837)
                      ·
                        rfl

theorem cell23_3459330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3459330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459330 prefixEnd_3459330 := by exact prefixLift 3459330
  have htrace : WordTrace (prefixWord ++ tailWord_3459330) baseStart_3459330 baseEnd_3459330 := by
    simpa [prefixWord, tailWord_3459330, baseEnd_3459330] using wordTrace_append hprefix tailTrace_3459330
  have hstable : (prefixWord ++ tailWord_3459330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459330).length < 2 ^ (prefixWord ++ tailWord_3459330).sum := by decide
  have hdescent : baseEnd_3459330 < baseStart_3459330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459337 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 2, 4]
def baseStart_3459337 : Nat := 118140960795 + 3459337 * 2 ^ 59
def prefixEnd_3459337 : Nat := 4983230072969 + 3 ^ 40 * 3459337 * 2
def baseEnd_3459337 : Nat := 592100875627545687259435

theorem tailTrace_3459337 : CollatzResearch.WordTrace tailWord_3459337 prefixEnd_3459337 592100875627545687259435 := by
  unfold tailWord_3459337
  simp only [CollatzResearch.WordTrace]
  refine ⟨126172385868420331568104265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84114923912280221045402843 126172385868420331568104265)
  ·
    refine ⟨94629289401315248676078199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126172385868420331568104265 94629289401315248676078199)
    ·
      refine ⟨141943934101972873014117299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94629289401315248676078199 141943934101972873014117299)
      ·
        refine ⟨212915901152959309521175949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141943934101972873014117299 212915901152959309521175949)
        ·
          refine ⟨79843462932359741070440981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212915901152959309521175949 79843462932359741070440981)
          ·
            refine ⟨3742662324954362862676921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79843462932359741070440981 3742662324954362862676921)
            ·
              refine ⟨2806996743715772147007691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742662324954362862676921 2806996743715772147007691)
              ·
                refine ⟨4210495115573658220511537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806996743715772147007691 4210495115573658220511537)
                ·
                  refine ⟨3157871336680243665383653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210495115573658220511537 3157871336680243665383653)
                  ·
                    refine ⟨592100875627545687259435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157871336680243665383653 592100875627545687259435)
                    ·
                      rfl

theorem cell23_3459337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 4].length) (baseStart_3459337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459337 prefixEnd_3459337 := by exact prefixLift 3459337
  have htrace : WordTrace (prefixWord ++ tailWord_3459337) baseStart_3459337 baseEnd_3459337 := by
    simpa [prefixWord, tailWord_3459337, baseEnd_3459337] using wordTrace_append hprefix tailTrace_3459337
  have hstable : (prefixWord ++ tailWord_3459337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459337).length < 2 ^ (prefixWord ++ tailWord_3459337).sum := by decide
  have hdescent : baseEnd_3459337 < baseStart_3459337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459360 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3459360 : Nat := 118140960795 + 3459360 * 2 ^ 59
def prefixEnd_3459360 : Nat := 4983230072969 + 3 ^ 40 * 3459360 * 2
def baseEnd_3459360 : Nat := 1776314436937690471790699

theorem tailTrace_3459360 : CollatzResearch.WordTrace tailWord_3459360 prefixEnd_3459360 1776314436937690471790699 := by
  unfold tailWord_3459360
  simp only [CollatzResearch.WordTrace]
  refine ⟨63086612373668503248095767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84115483164891337664127689 63086612373668503248095767)
  ·
    refine ⟨94629918560502754872143651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63086612373668503248095767 94629918560502754872143651)
    ·
      refine ⟨141944877840754132308215477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94629918560502754872143651 141944877840754132308215477)
      ·
        refine ⟨13307332297570699903895201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141944877840754132308215477 13307332297570699903895201)
        ·
          refine ⟨9980499223178024927921401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13307332297570699903895201 9980499223178024927921401)
          ·
            refine ⟨7485374417383518695941051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9980499223178024927921401 7485374417383518695941051)
            ·
              refine ⟨11228061626075278043911577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485374417383518695941051 11228061626075278043911577)
              ·
                refine ⟨8421046219556458532933683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11228061626075278043911577 8421046219556458532933683)
                ·
                  refine ⟨12631569329334687799400525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8421046219556458532933683 12631569329334687799400525)
                  ·
                    refine ⟨4736838498500507924775197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12631569329334687799400525 4736838498500507924775197)
                    ·
                      refine ⟨1776314436937690471790699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736838498500507924775197 1776314436937690471790699)
                      ·
                        rfl

theorem cell23_3459360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3459360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459360 prefixEnd_3459360 := by exact prefixLift 3459360
  have htrace : WordTrace (prefixWord ++ tailWord_3459360) baseStart_3459360 baseEnd_3459360 := by
    simpa [prefixWord, tailWord_3459360, baseEnd_3459360] using wordTrace_append hprefix tailTrace_3459360
  have hstable : (prefixWord ++ tailWord_3459360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459360).length < 2 ^ (prefixWord ++ tailWord_3459360).sum := by decide
  have hdescent : baseEnd_3459360 < baseStart_3459360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459367 : List Nat := [1, 1, 8, 1, 2, 10]
def baseStart_3459367 : Nat := 118140960795 + 3459367 * 2 ^ 59
def prefixEnd_3459367 : Nat := 4983230072969 + 3 ^ 40 * 3459367 * 2
def baseEnd_3459367 : Nat := 7309950746099884544869

theorem tailTrace_3459367 : CollatzResearch.WordTrace tailWord_3459367 prefixEnd_3459367 7309950746099884544869 := by
  unfold tailWord_3459367
  simp only [CollatzResearch.WordTrace]
  refine ⟨126173480058311646691696355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84115653372207764461130903 126173480058311646691696355)
  ·
    refine ⟨189260220087467470037544533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126173480058311646691696355 189260220087467470037544533)
    ·
      refine ⟨2217893204150009414502475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 189260220087467470037544533 2217893204150009414502475)
      ·
        refine ⟨3326839806225014121753713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217893204150009414502475 3326839806225014121753713)
        ·
          refine ⟨2495129854668760591315285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3326839806225014121753713 2495129854668760591315285)
          ·
            refine ⟨7309950746099884544869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2495129854668760591315285 7309950746099884544869)
            ·
              rfl

theorem cell23_3459367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 10].length) (baseStart_3459367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459367 prefixEnd_3459367 := by exact prefixLift 3459367
  have htrace : WordTrace (prefixWord ++ tailWord_3459367) baseStart_3459367 baseEnd_3459367 := by
    simpa [prefixWord, tailWord_3459367, baseEnd_3459367] using wordTrace_append hprefix tailTrace_3459367
  have hstable : (prefixWord ++ tailWord_3459367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459367).length < 2 ^ (prefixWord ++ tailWord_3459367).sum := by decide
  have hdescent : baseEnd_3459367 < baseStart_3459367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459378 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_3459378 : Nat := 118140960795 + 3459378 * 2 ^ 59
def prefixEnd_3459378 : Nat := 4983230072969 + 3 ^ 40 * 3459378 * 2
def baseEnd_3459378 : Nat := 1776323679589471401365617

theorem tailTrace_3459378 : CollatzResearch.WordTrace tailWord_3459378 prefixEnd_3459378 1776323679589471401365617 := by
  unfold tailWord_3459378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31543470315317948892586697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84115920840847863713564525 31543470315317948892586697)
  ·
    refine ⟨23657602736488461669440023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31543470315317948892586697 23657602736488461669440023)
    ·
      refine ⟨35486404104732692504160035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23657602736488461669440023 35486404104732692504160035)
      ·
        refine ⟨53229606157099038756240053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35486404104732692504160035 53229606157099038756240053)
        ·
          refine ⟨4990275577228034883397505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53229606157099038756240053 4990275577228034883397505)
          ·
            refine ⟨3742706682921026162548129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990275577228034883397505 3742706682921026162548129)
            ·
              refine ⟨2807030012190769621911097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742706682921026162548129 2807030012190769621911097)
              ·
                refine ⟨2105272509143077216433323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2807030012190769621911097 2105272509143077216433323)
                ·
                  refine ⟨3157908763714615824649985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105272509143077216433323 3157908763714615824649985)
                  ·
                    refine ⟨2368431572785961868487489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3157908763714615824649985 2368431572785961868487489)
                    ·
                      refine ⟨1776323679589471401365617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368431572785961868487489 1776323679589471401365617)
                      ·
                        rfl

theorem cell23_3459378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_3459378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459378 prefixEnd_3459378 := by exact prefixLift 3459378
  have htrace : WordTrace (prefixWord ++ tailWord_3459378) baseStart_3459378 baseEnd_3459378 := by
    simpa [prefixWord, tailWord_3459378, baseEnd_3459378] using wordTrace_append hprefix tailTrace_3459378
  have hstable : (prefixWord ++ tailWord_3459378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459378).length < 2 ^ (prefixWord ++ tailWord_3459378).sum := by decide
  have hdescent : baseEnd_3459378 < baseStart_3459378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459400 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_3459400 : Nat := 118140960795 + 3459400 * 2 ^ 59
def prefixEnd_3459400 : Nat := 4983230072969 + 3 ^ 40 * 3459400 * 2
def baseEnd_3459400 : Nat := 1776334976163870315290515

theorem tailTrace_3459400 : CollatzResearch.WordTrace tailWord_3459400 prefixEnd_3459400 1776334976163870315290515 := by
  unfold tailWord_3459400
  simp only [CollatzResearch.WordTrace]
  refine ⟨63087341833596046663823827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84116455778128062218431769 63087341833596046663823827)
  ·
    refine ⟨94631012750394069995735741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63087341833596046663823827 94631012750394069995735741)
    ·
      refine ⟨35486629781397776248400903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94631012750394069995735741 35486629781397776248400903)
      ·
        refine ⟨53229944672096664372601355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35486629781397776248400903 53229944672096664372601355)
        ·
          refine ⟨79844917008144996558902033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53229944672096664372601355 79844917008144996558902033)
          ·
            refine ⟨59883687756108747419176525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79844917008144996558902033 59883687756108747419176525)
            ·
              refine ⟨22456382908540780282191197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59883687756108747419176525 22456382908540780282191197)
              ·
                refine ⟨8421143590702792605821699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22456382908540780282191197 8421143590702792605821699)
                ·
                  refine ⟨12631715386054188908732549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8421143590702792605821699 12631715386054188908732549)
                  ·
                    refine ⟨2368446634885160420387353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12631715386054188908732549 2368446634885160420387353)
                    ·
                      refine ⟨1776334976163870315290515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368446634885160420387353 1776334976163870315290515)
                      ·
                        rfl

theorem cell23_3459400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_3459400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459400 prefixEnd_3459400 := by exact prefixLift 3459400
  have htrace : WordTrace (prefixWord ++ tailWord_3459400) baseStart_3459400 baseEnd_3459400 := by
    simpa [prefixWord, tailWord_3459400, baseEnd_3459400] using wordTrace_append hprefix tailTrace_3459400
  have hstable : (prefixWord ++ tailWord_3459400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459400).length < 2 ^ (prefixWord ++ tailWord_3459400).sum := by decide
  have hdescent : baseEnd_3459400 < baseStart_3459400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
