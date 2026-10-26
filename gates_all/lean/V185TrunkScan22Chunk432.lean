import V185TrunkScan22Chunk431

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3851381 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3851381 : Nat := 118140960795 + 3851381 * 2 ^ 59
def prefixEnd_3851381 : Nat := 4983230072969 + 3 ^ 40 * 3851381 * 2
def baseEnd_3851381 : Nat := 1318406424395934125216885

theorem tailTrace_3851381 : CollatzResearch.WordTrace tailWord_3851381 prefixEnd_3851381 1318406424395934125216885 := by
  unfold tailWord_3851381
  simp only [CollatzResearch.WordTrace]
  refine ⟨140471405260111875352681997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93647603506741250235121331 140471405260111875352681997)
  ·
    refine ⟨52676776972541953257255749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140471405260111875352681997 52676776972541953257255749)
    ·
      refine ⟨9876895682351616235735453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52676776972541953257255749 9876895682351616235735453)
      ·
        refine ⟨3703835880881856088400795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9876895682351616235735453 3703835880881856088400795)
        ·
          refine ⟨5555753821322784132601193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703835880881856088400795 5555753821322784132601193)
          ·
            refine ⟨4166815365992088099450895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5555753821322784132601193 4166815365992088099450895)
            ·
              refine ⟨6250223048988132149176343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166815365992088099450895 6250223048988132149176343)
              ·
                refine ⟨9375334573482198223764515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250223048988132149176343 9375334573482198223764515)
                ·
                  refine ⟨14063001860223297335646773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375334573482198223764515 14063001860223297335646773)
                  ·
                    refine ⟨1318406424395934125216885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14063001860223297335646773 1318406424395934125216885)
                    ·
                      rfl

theorem cell22_3851381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3851381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851381 prefixEnd_3851381 := by exact prefixLift 3851381
  have htrace : WordTrace (prefixWord ++ tailWord_3851381) baseStart_3851381 baseEnd_3851381 := by
    simpa [prefixWord, tailWord_3851381, baseEnd_3851381] using wordTrace_append hprefix tailTrace_3851381
  have hstable : (prefixWord ++ tailWord_3851381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851381).length < 2 ^ (prefixWord ++ tailWord_3851381).sum := by decide
  have hdescent : baseEnd_3851381 < baseStart_3851381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851392 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_3851392 : Nat := 118140960795 + 3851392 * 2 ^ 59
def prefixEnd_3851392 : Nat := 4983230072969 + 3 ^ 40 * 3851392 * 2
def baseEnd_3851392 : Nat := 1318410189920733763191851

theorem tailTrace_3851392 : CollatzResearch.WordTrace tailWord_3851392 prefixEnd_3851392 1318410189920733763191851 := by
  unfold tailWord_3851392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70235903231536012115666215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93647870975381349487554953 70235903231536012115666215)
  ·
    refine ⟨105353854847304018173499323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70235903231536012115666215 105353854847304018173499323)
    ·
      refine ⟨158030782270956027260248985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105353854847304018173499323 158030782270956027260248985)
      ·
        refine ⟨118523086703217020445186739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158030782270956027260248985 118523086703217020445186739)
        ·
          refine ⟨177784630054825530667780109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118523086703217020445186739 177784630054825530667780109)
          ·
            refine ⟨66669236270559574000417541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177784630054825530667780109 66669236270559574000417541)
            ·
              refine ⟨12500481800729920125078289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66669236270559574000417541 12500481800729920125078289)
              ·
                refine ⟨9375361350547440093808717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12500481800729920125078289 9375361350547440093808717)
                ·
                  refine ⟨3515760506455290035178269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9375361350547440093808717 3515760506455290035178269)
                  ·
                    refine ⟨1318410189920733763191851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515760506455290035178269 1318410189920733763191851)
                    ·
                      rfl

theorem cell22_3851392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_3851392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851392 prefixEnd_3851392 := by exact prefixLift 3851392
  have htrace : WordTrace (prefixWord ++ tailWord_3851392) baseStart_3851392 baseEnd_3851392 := by
    simpa [prefixWord, tailWord_3851392, baseEnd_3851392] using wordTrace_append hprefix tailTrace_3851392
  have hstable : (prefixWord ++ tailWord_3851392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851392).length < 2 ^ (prefixWord ++ tailWord_3851392).sum := by decide
  have hdescent : baseEnd_3851392 < baseStart_3851392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851450 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_3851450 : Nat := 118140960795 + 3851450 * 2 ^ 59
def prefixEnd_3851450 : Nat := 4983230072969 + 3 ^ 40 * 3851450 * 2
def baseEnd_3851450 : Nat := 439476681502013648413891

theorem tailTrace_3851450 : CollatzResearch.WordTrace tailWord_3851450 prefixEnd_3851450 439476681502013648413891 := by
  unfold tailWord_3851450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35118480474215475034235951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93649281264574600091295869 35118480474215475034235951)
  ·
    refine ⟨52677720711323212551353927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35118480474215475034235951 52677720711323212551353927)
    ·
      refine ⟨79016581066984818827030891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52677720711323212551353927 79016581066984818827030891)
      ·
        refine ⟨118524871600477228240546337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79016581066984818827030891 118524871600477228240546337)
        ·
          refine ⟨88893653700357921180409753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118524871600477228240546337 88893653700357921180409753)
          ·
            refine ⟨66670240275268440885307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88893653700357921180409753 66670240275268440885307315)
            ·
              refine ⟨100005360412902661327960973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66670240275268440885307315 100005360412902661327960973)
              ·
                refine ⟨37502010154838497997985365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100005360412902661327960973 37502010154838497997985365)
                ·
                  refine ⟨439476681502013648413891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37502010154838497997985365 439476681502013648413891)
                  ·
                    rfl

theorem cell22_3851450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_3851450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851450 prefixEnd_3851450 := by exact prefixLift 3851450
  have htrace : WordTrace (prefixWord ++ tailWord_3851450) baseStart_3851450 baseEnd_3851450 := by
    simpa [prefixWord, tailWord_3851450, baseEnd_3851450] using wordTrace_append hprefix tailTrace_3851450
  have hstable : (prefixWord ++ tailWord_3851450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851450).length < 2 ^ (prefixWord ++ tailWord_3851450).sum := by decide
  have hdescent : baseEnd_3851450 < baseStart_3851450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851499 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 2, 3]
def baseStart_3851499 : Nat := 118140960795 + 3851499 * 2 ^ 59
def prefixEnd_3851499 : Nat := 4983230072969 + 3 ^ 40 * 3851499 * 2
def baseEnd_3851499 : Nat := 1318446818207421150766523

theorem tailTrace_3851499 : CollatzResearch.WordTrace tailWord_3851499 prefixEnd_3851499 1318446818207421150766523 := by
  unfold tailWord_3851499
  simp only [CollatzResearch.WordTrace]
  refine ⟨140475709073684381505477551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93650472715789587670318367 140475709073684381505477551)
  ·
    refine ⟨210713563610526572258216327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140475709073684381505477551 210713563610526572258216327)
    ·
      refine ⟨316070345415789858387324491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210713563610526572258216327 316070345415789858387324491)
      ·
        refine ⟨474105518123684787580986737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316070345415789858387324491 474105518123684787580986737)
        ·
          refine ⟨355579138592763590685740053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474105518123684787580986737 355579138592763590685740053)
          ·
            refine ⟨16667772121535793313394065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 355579138592763590685740053 16667772121535793313394065)
            ·
              refine ⟨12500829091151844985045549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16667772121535793313394065 12500829091151844985045549)
              ·
                refine ⟨4687810909181941869392081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12500829091151844985045549 4687810909181941869392081)
                ·
                  refine ⟨3515858181886456402044061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687810909181941869392081 3515858181886456402044061)
                  ·
                    refine ⟨1318446818207421150766523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515858181886456402044061 1318446818207421150766523)
                    ·
                      rfl

theorem cell22_3851499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 3].length) (baseStart_3851499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851499 prefixEnd_3851499 := by exact prefixLift 3851499
  have htrace : WordTrace (prefixWord ++ tailWord_3851499) baseStart_3851499 baseEnd_3851499 := by
    simpa [prefixWord, tailWord_3851499, baseEnd_3851499] using wordTrace_append hprefix tailTrace_3851499
  have hstable : (prefixWord ++ tailWord_3851499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851499).length < 2 ^ (prefixWord ++ tailWord_3851499).sum := by decide
  have hdescent : baseEnd_3851499 < baseStart_3851499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851544 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_3851544 : Nat := 118140960795 + 3851544 * 2 ^ 59
def prefixEnd_3851544 : Nat := 4983230072969 + 3 ^ 40 * 3851544 * 2
def baseEnd_3851544 : Nat := 1318462222627056033391385

theorem tailTrace_3851544 : CollatzResearch.WordTrace tailWord_3851544 prefixEnd_3851544 1318462222627056033391385 := by
  unfold tailWord_3851544
  simp only [CollatzResearch.WordTrace]
  refine ⟨70238675179260677095432843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93651566905680902793910457 70238675179260677095432843)
  ·
    refine ⟨105358012768891015643149265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70238675179260677095432843 105358012768891015643149265)
    ·
      refine ⟨79018509576668261732361949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105358012768891015643149265 79018509576668261732361949)
      ·
        refine ⟨29631941091250598149635731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79018509576668261732361949 29631941091250598149635731)
        ·
          refine ⟨44447911636875897224453597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29631941091250598149635731 44447911636875897224453597)
          ·
            refine ⟨16667966863828461459170099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44447911636875897224453597 16667966863828461459170099)
            ·
              refine ⟨25001950295742692188755149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16667966863828461459170099 25001950295742692188755149)
              ·
                refine ⟨9375731360903509570783181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25001950295742692188755149 9375731360903509570783181)
                ·
                  refine ⟨3515899260338816089043693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9375731360903509570783181 3515899260338816089043693)
                  ·
                    refine ⟨1318462222627056033391385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515899260338816089043693 1318462222627056033391385)
                    ·
                      rfl

theorem cell22_3851544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_3851544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851544 prefixEnd_3851544 := by exact prefixLift 3851544
  have htrace : WordTrace (prefixWord ++ tailWord_3851544) baseStart_3851544 baseEnd_3851544 := by
    simpa [prefixWord, tailWord_3851544, baseEnd_3851544] using wordTrace_append hprefix tailTrace_3851544
  have hstable : (prefixWord ++ tailWord_3851544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851544).length < 2 ^ (prefixWord ++ tailWord_3851544).sum := by decide
  have hdescent : baseEnd_3851544 < baseStart_3851544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851550 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3851550 : Nat := 118140960795 + 3851550 * 2 ^ 59
def prefixEnd_3851550 : Nat := 4983230072969 + 3 ^ 40 * 3851550 * 2
def baseEnd_3851550 : Nat := 1318464276549674017741367

theorem tailTrace_3851550 : CollatzResearch.WordTrace tailWord_3851550 prefixEnd_3851550 1318464276549674017741367 := by
  unfold tailWord_3851550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17559696149562452151948013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93651712797666411477056069 17559696149562452151948013)
  ·
    refine ⟨6584886056085919556980505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17559696149562452151948013 6584886056085919556980505)
    ·
      refine ⟨4938664542064439667735379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6584886056085919556980505 4938664542064439667735379)
      ·
        refine ⟨7407996813096659501603069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938664542064439667735379 7407996813096659501603069)
        ·
          refine ⟨2777998804911247313101151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7407996813096659501603069 2777998804911247313101151)
          ·
            refine ⟨4166998207366870969651727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777998804911247313101151 4166998207366870969651727)
            ·
              refine ⟨6250497311050306454477591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166998207366870969651727 6250497311050306454477591)
              ·
                refine ⟨9375745966575459681716387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250497311050306454477591 9375745966575459681716387)
                ·
                  refine ⟨14063618949863189522574581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375745966575459681716387 14063618949863189522574581)
                  ·
                    refine ⟨1318464276549674017741367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14063618949863189522574581 1318464276549674017741367)
                    ·
                      rfl

theorem cell22_3851550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3851550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851550 prefixEnd_3851550 := by exact prefixLift 3851550
  have htrace : WordTrace (prefixWord ++ tailWord_3851550) baseStart_3851550 baseEnd_3851550 := by
    simpa [prefixWord, tailWord_3851550, baseEnd_3851550] using wordTrace_append hprefix tailTrace_3851550
  have hstable : (prefixWord ++ tailWord_3851550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851550).length < 2 ^ (prefixWord ++ tailWord_3851550).sum := by decide
  have hdescent : baseEnd_3851550 < baseStart_3851550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851587 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 5, 4]
def baseStart_3851587 : Nat := 118140960795 + 3851587 * 2 ^ 59
def prefixEnd_3851587 : Nat := 4983230072969 + 3 ^ 40 * 3851587 * 2
def baseEnd_3851587 : Nat := 1318476942405818254566253

theorem tailTrace_3851587 : CollatzResearch.WordTrace tailWord_3851587 prefixEnd_3851587 1318476942405818254566253 := by
  unfold tailWord_3851587
  simp only [CollatzResearch.WordTrace]
  refine ⟨140478918697365572534681015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93652612464910381689787343 140478918697365572534681015)
  ·
    refine ⟨210718378046048358802021523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140478918697365572534681015 210718378046048358802021523)
    ·
      refine ⟨316077567069072538203032285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210718378046048358802021523 316077567069072538203032285)
      ·
        refine ⟨118529087650902201826137107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316077567069072538203032285 118529087650902201826137107)
        ·
          refine ⟨177793631476353302739205661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118529087650902201826137107 177793631476353302739205661)
          ·
            refine ⟨66672611803632488527202123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177793631476353302739205661 66672611803632488527202123)
            ·
              refine ⟨100008917705448732790803185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66672611803632488527202123 100008917705448732790803185)
              ·
                refine ⟨75006688279086549593102389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100008917705448732790803185 75006688279086549593102389)
                ·
                  refine ⟨7031877026164364024353349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75006688279086549593102389 7031877026164364024353349)
                  ·
                    refine ⟨1318476942405818254566253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031877026164364024353349 1318476942405818254566253)
                    ·
                      rfl

theorem cell22_3851587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_3851587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851587 prefixEnd_3851587 := by exact prefixLift 3851587
  have htrace : WordTrace (prefixWord ++ tailWord_3851587) baseStart_3851587 baseEnd_3851587 := by
    simpa [prefixWord, tailWord_3851587, baseEnd_3851587] using wordTrace_append hprefix tailTrace_3851587
  have hstable : (prefixWord ++ tailWord_3851587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851587).length < 2 ^ (prefixWord ++ tailWord_3851587).sum := by decide
  have hdescent : baseEnd_3851587 < baseStart_3851587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851604 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3851604 : Nat := 118140960795 + 3851604 * 2 ^ 59
def prefixEnd_3851604 : Nat := 4983230072969 + 3 ^ 40 * 3851604 * 2
def baseEnd_3851604 : Nat := 1318482761853235876891201

theorem tailTrace_3851604 : CollatzResearch.WordTrace tailWord_3851604 prefixEnd_3851604 1318482761853235876891201 := by
  unfold tailWord_3851604
  simp only [CollatzResearch.WordTrace]
  refine ⟨70239769369151992219024933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93653025825535989625366577 70239769369151992219024933)
  ·
    refine ⟨13169956756715998541067175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70239769369151992219024933 13169956756715998541067175)
    ·
      refine ⟨19754935135073997811600763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13169956756715998541067175 19754935135073997811600763)
      ·
        refine ⟨29632402702610996717401145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754935135073997811600763 29632402702610996717401145)
        ·
          refine ⟨22224302026958247538050859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29632402702610996717401145 22224302026958247538050859)
          ·
            refine ⟨33336453040437371307076289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22224302026958247538050859 33336453040437371307076289)
            ·
              refine ⟨25002339780328028480307217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33336453040437371307076289 25002339780328028480307217)
              ·
                refine ⟨18751754835246021360230413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25002339780328028480307217 18751754835246021360230413)
                ·
                  refine ⟨7031908063217258010086405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18751754835246021360230413 7031908063217258010086405)
                  ·
                    refine ⟨1318482761853235876891201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031908063217258010086405 1318482761853235876891201)
                    ·
                      rfl

theorem cell22_3851604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3851604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851604 prefixEnd_3851604 := by exact prefixLift 3851604
  have htrace : WordTrace (prefixWord ++ tailWord_3851604) baseStart_3851604 baseEnd_3851604 := by
    simpa [prefixWord, tailWord_3851604, baseEnd_3851604] using wordTrace_append hprefix tailTrace_3851604
  have hstable : (prefixWord ++ tailWord_3851604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851604).length < 2 ^ (prefixWord ++ tailWord_3851604).sum := by decide
  have hdescent : baseEnd_3851604 < baseStart_3851604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851617 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3851617 : Nat := 118140960795 + 3851617 * 2 ^ 59
def prefixEnd_3851617 : Nat := 4983230072969 + 3 ^ 40 * 3851617 * 2
def baseEnd_3851617 : Nat := 1318487212018908176316161

theorem tailTrace_3851617 : CollatzResearch.WordTrace tailWord_3851617 prefixEnd_3851617 1318487212018908176316161 := by
  unfold tailWord_3851617
  simp only [CollatzResearch.WordTrace]
  refine ⟨140480012887256887658273105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93653341924837925105515403 140480012887256887658273105)
  ·
    refine ⟨105360009665442665743704829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140480012887256887658273105 105360009665442665743704829)
    ·
      refine ⟨39510003624540999653889311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105360009665442665743704829 39510003624540999653889311)
      ·
        refine ⟨59265005436811499480833967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39510003624540999653889311 59265005436811499480833967)
        ·
          refine ⟨88897508155217249221250951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59265005436811499480833967 88897508155217249221250951)
          ·
            refine ⟨133346262232825873831876427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88897508155217249221250951 133346262232825873831876427)
            ·
              refine ⟨200019393349238810747814641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133346262232825873831876427 200019393349238810747814641)
              ·
                refine ⟨150014545011929108060860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200019393349238810747814641 150014545011929108060860981)
                ·
                  refine ⟨14063863594868353880705717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150014545011929108060860981 14063863594868353880705717)
                  ·
                    refine ⟨1318487212018908176316161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14063863594868353880705717 1318487212018908176316161)
                    ·
                      rfl

theorem cell22_3851617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3851617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851617 prefixEnd_3851617 := by exact prefixLift 3851617
  have htrace : WordTrace (prefixWord ++ tailWord_3851617) baseStart_3851617 baseEnd_3851617 := by
    simpa [prefixWord, tailWord_3851617, baseEnd_3851617] using wordTrace_append hprefix tailTrace_3851617
  have hstable : (prefixWord ++ tailWord_3851617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851617).length < 2 ^ (prefixWord ++ tailWord_3851617).sum := by decide
  have hdescent : baseEnd_3851617 < baseStart_3851617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851634 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_3851634 : Nat := 118140960795 + 3851634 * 2 ^ 59
def prefixEnd_3851634 : Nat := 4983230072969 + 3 ^ 40 * 3851634 * 2
def baseEnd_3851634 : Nat := 1318493031466325798641109

theorem tailTrace_3851634 : CollatzResearch.WordTrace tailWord_3851634 prefixEnd_3851634 1318493031466325798641109 := by
  unfold tailWord_3851634
  simp only [CollatzResearch.WordTrace]
  refine ⟨35120158232048824890410489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93653755285463533041094637 35120158232048824890410489)
  ·
    refine ⟨26340118674036618667807867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35120158232048824890410489 26340118674036618667807867)
    ·
      refine ⟨39510178011054928001711801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26340118674036618667807867 39510178011054928001711801)
      ·
        refine ⟨29632633508291196001283851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39510178011054928001711801 29632633508291196001283851)
        ·
          refine ⟨44448950262436794001925777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29632633508291196001283851 44448950262436794001925777)
          ·
            refine ⟨33336712696827595501444333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44448950262436794001925777 33336712696827595501444333)
            ·
              refine ⟨12501267261310348313041625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33336712696827595501444333 12501267261310348313041625)
              ·
                refine ⟨9375950445982761234781219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12501267261310348313041625 9375950445982761234781219)
                ·
                  refine ⟨14063925668974141852171829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375950445982761234781219 14063925668974141852171829)
                  ·
                    refine ⟨1318493031466325798641109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14063925668974141852171829 1318493031466325798641109)
                    ·
                      rfl

theorem cell22_3851634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_3851634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851634 prefixEnd_3851634 := by exact prefixLift 3851634
  have htrace : WordTrace (prefixWord ++ tailWord_3851634) baseStart_3851634 baseEnd_3851634 := by
    simpa [prefixWord, tailWord_3851634, baseEnd_3851634] using wordTrace_append hprefix tailTrace_3851634
  have hstable : (prefixWord ++ tailWord_3851634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851634).length < 2 ^ (prefixWord ++ tailWord_3851634).sum := by decide
  have hdescent : baseEnd_3851634 < baseStart_3851634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851646 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3851646 : Nat := 118140960795 + 3851646 * 2 ^ 59
def prefixEnd_3851646 : Nat := 4983230072969 + 3 ^ 40 * 3851646 * 2
def baseEnd_3851646 : Nat := 1318497139311561767341073

theorem tailTrace_3851646 : CollatzResearch.WordTrace tailWord_3851646 prefixEnd_3851646 1318497139311561767341073 := by
  unfold tailWord_3851646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560133825518978201384849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93654047069434550407385861 17560133825518978201384849)
  ·
    refine ⟨13170100369139233651038637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17560133825518978201384849 13170100369139233651038637)
    ·
      refine ⟨4938787638427212619139489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13170100369139233651038637 4938787638427212619139489)
      ·
        refine ⟨3704090728820409464354617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4938787638427212619139489 3704090728820409464354617)
        ·
          refine ⟨2778068046615307098265963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3704090728820409464354617 2778068046615307098265963)
          ·
            refine ⟨4167102069922960647398945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778068046615307098265963 4167102069922960647398945)
            ·
              refine ⟨3125326552442220485549209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167102069922960647398945 3125326552442220485549209)
              ·
                refine ⟨2343994914331665364161907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125326552442220485549209 2343994914331665364161907)
                ·
                  refine ⟨3515992371497498046242861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343994914331665364161907 3515992371497498046242861)
                  ·
                    refine ⟨1318497139311561767341073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515992371497498046242861 1318497139311561767341073)
                    ·
                      rfl

theorem cell22_3851646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3851646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851646 prefixEnd_3851646 := by exact prefixLift 3851646
  have htrace : WordTrace (prefixWord ++ tailWord_3851646) baseStart_3851646 baseEnd_3851646 := by
    simpa [prefixWord, tailWord_3851646, baseEnd_3851646] using wordTrace_append hprefix tailTrace_3851646
  have hstable : (prefixWord ++ tailWord_3851646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851646).length < 2 ^ (prefixWord ++ tailWord_3851646).sum := by decide
  have hdescent : baseEnd_3851646 < baseStart_3851646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851651 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 2, 3]
def baseStart_3851651 : Nat := 118140960795 + 3851651 * 2 ^ 59
def prefixEnd_3851651 : Nat := 4983230072969 + 3 ^ 40 * 3851651 * 2
def baseEnd_3851651 : Nat := 1318498850913743420966057

theorem tailTrace_3851651 : CollatzResearch.WordTrace tailWord_3851651 prefixEnd_3851651 1318498850913743420966057 := by
  unfold tailWord_3851651
  simp only [CollatzResearch.WordTrace]
  refine ⟨140481252969133711465010807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93654168646089140976673871 140481252969133711465010807)
  ·
    refine ⟨210721879453700567197516211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140481252969133711465010807 210721879453700567197516211)
    ·
      refine ⟨316082819180550850796274317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210721879453700567197516211 316082819180550850796274317)
      ·
        refine ⟨118531057192706569048602869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316082819180550850796274317 118531057192706569048602869)
        ·
          refine ⟨11112286611816240848306519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118531057192706569048602869 11112286611816240848306519)
          ·
            refine ⟨16668429917724361272459779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112286611816240848306519 16668429917724361272459779)
            ·
              refine ⟨25002644876586541908689669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16668429917724361272459779 25002644876586541908689669)
              ·
                refine ⟨4687995914359976607879313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25002644876586541908689669 4687995914359976607879313)
                ·
                  refine ⟨3515996935769982455909485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687995914359976607879313 3515996935769982455909485)
                  ·
                    refine ⟨1318498850913743420966057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515996935769982455909485 1318498850913743420966057)
                    ·
                      rfl

theorem cell22_3851651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 3].length) (baseStart_3851651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851651 prefixEnd_3851651 := by exact prefixLift 3851651
  have htrace : WordTrace (prefixWord ++ tailWord_3851651) baseStart_3851651 baseEnd_3851651 := by
    simpa [prefixWord, tailWord_3851651, baseEnd_3851651] using wordTrace_append hprefix tailTrace_3851651
  have hstable : (prefixWord ++ tailWord_3851651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851651).length < 2 ^ (prefixWord ++ tailWord_3851651).sum := by decide
  have hdescent : baseEnd_3851651 < baseStart_3851651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851668 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3851668 : Nat := 118140960795 + 3851668 * 2 ^ 59
def prefixEnd_3851668 : Nat := 4983230072969 + 3 ^ 40 * 3851668 * 2
def baseEnd_3851668 : Nat := 1318504670361161043291005

theorem tailTrace_3851668 : CollatzResearch.WordTrace tailWord_3851668 prefixEnd_3851668 1318504670361161043291005 := by
  unfold tailWord_3851668
  simp only [CollatzResearch.WordTrace]
  refine ⟨70240936505036061684189829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93654582006714748912253105 70240936505036061684189829)
  ·
    refine ⟨13170175594694261565785593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70240936505036061684189829 13170175594694261565785593)
    ·
      refine ⟨9877631696020696174339195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13170175594694261565785593 9877631696020696174339195)
      ·
        refine ⟨14816447544031044261508793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9877631696020696174339195 14816447544031044261508793)
        ·
          refine ⟨11112335658023283196131595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14816447544031044261508793 11112335658023283196131595)
          ·
            refine ⟨16668503487034924794197393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112335658023283196131595 16668503487034924794197393)
            ·
              refine ⟨12501377615276193595648045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16668503487034924794197393 12501377615276193595648045)
              ·
                refine ⟨4688016605728572598368017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12501377615276193595648045 4688016605728572598368017)
                ·
                  refine ⟨3516012454296429448776013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4688016605728572598368017 3516012454296429448776013)
                  ·
                    refine ⟨1318504670361161043291005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516012454296429448776013 1318504670361161043291005)
                    ·
                      rfl

theorem cell22_3851668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3851668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851668 prefixEnd_3851668 := by exact prefixLift 3851668
  have htrace : WordTrace (prefixWord ++ tailWord_3851668) baseStart_3851668 baseEnd_3851668 := by
    simpa [prefixWord, tailWord_3851668, baseEnd_3851668] using wordTrace_append hprefix tailTrace_3851668
  have hstable : (prefixWord ++ tailWord_3851668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851668).length < 2 ^ (prefixWord ++ tailWord_3851668).sum := by decide
  have hdescent : baseEnd_3851668 < baseStart_3851668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851709 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3851709 : Nat := 118140960795 + 3851709 * 2 ^ 59
def prefixEnd_3851709 : Nat := 4983230072969 + 3 ^ 40 * 3851709 * 2
def baseEnd_3851709 : Nat := 439506235166350201005293

theorem tailTrace_3851709 : CollatzResearch.WordTrace tailWord_3851709 prefixEnd_3851709 439506235166350201005293 := by
  unfold tailWord_3851709
  simp only [CollatzResearch.WordTrace]
  refine ⟨140483368402923587370622181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93655578935282391580414787 140483368402923587370622181)
  ·
    refine ⟨26340631575548172631991659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140483368402923587370622181 26340631575548172631991659)
    ·
      refine ⟨39510947363322258947987489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26340631575548172631991659 39510947363322258947987489)
      ·
        refine ⟨29633210522491694210990617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39510947363322258947987489 29633210522491694210990617)
        ·
          refine ⟨22224907891868770658242963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29633210522491694210990617 22224907891868770658242963)
          ·
            refine ⟨33337361837803155987364445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22224907891868770658242963 33337361837803155987364445)
            ·
              refine ⟨12501510689176183495261667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33337361837803155987364445 12501510689176183495261667)
              ·
                refine ⟨18752266033764275242892501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501510689176183495261667 18752266033764275242892501)
                ·
                  refine ⟨439506235166350201005293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18752266033764275242892501 439506235166350201005293)
                  ·
                    rfl

theorem cell22_3851709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3851709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851709 prefixEnd_3851709 := by exact prefixLift 3851709
  have htrace : WordTrace (prefixWord ++ tailWord_3851709) baseStart_3851709 baseEnd_3851709 := by
    simpa [prefixWord, tailWord_3851709, baseEnd_3851709] using wordTrace_append hprefix tailTrace_3851709
  have hstable : (prefixWord ++ tailWord_3851709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851709).length < 2 ^ (prefixWord ++ tailWord_3851709).sum := by decide
  have hdescent : baseEnd_3851709 < baseStart_3851709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851784 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3851784 : Nat := 118140960795 + 3851784 * 2 ^ 59
def prefixEnd_3851784 : Nat := 4983230072969 + 3 ^ 40 * 3851784 * 2
def baseEnd_3851784 : Nat := 1318544379531775407390649

theorem tailTrace_3851784 : CollatzResearch.WordTrace tailWord_3851784 prefixEnd_3851784 1318544379531775407390649 := by
  unfold tailWord_3851784
  simp only [CollatzResearch.WordTrace]
  refine ⟨70243051938825937589801203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93657402585101250119734937 70243051938825937589801203)
  ·
    refine ⟨105364577908238906384701805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70243051938825937589801203 105364577908238906384701805)
    ·
      refine ⟨39511716715589589894263177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105364577908238906384701805 39511716715589589894263177)
      ·
        refine ⟨29633787536692192420697383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39511716715589589894263177 29633787536692192420697383)
        ·
          refine ⟨44450681305038288631046075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29633787536692192420697383 44450681305038288631046075)
          ·
            refine ⟨66676021957557432946569113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44450681305038288631046075 66676021957557432946569113)
            ·
              refine ⟨50007016468168074709926835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66676021957557432946569113 50007016468168074709926835)
              ·
                refine ⟨75010524702252112064890253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50007016468168074709926835 75010524702252112064890253)
                ·
                  refine ⟨28128946763344542024333845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75010524702252112064890253 28128946763344542024333845)
                  ·
                    refine ⟨1318544379531775407390649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28128946763344542024333845 1318544379531775407390649)
                    ·
                      rfl

theorem cell22_3851784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3851784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851784 prefixEnd_3851784 := by exact prefixLift 3851784
  have htrace : WordTrace (prefixWord ++ tailWord_3851784) baseStart_3851784 baseEnd_3851784 := by
    simpa [prefixWord, tailWord_3851784, baseEnd_3851784] using wordTrace_append hprefix tailTrace_3851784
  have hstable : (prefixWord ++ tailWord_3851784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851784).length < 2 ^ (prefixWord ++ tailWord_3851784).sum := by decide
  have hdescent : baseEnd_3851784 < baseStart_3851784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851790 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_3851790 : Nat := 118140960795 + 3851790 * 2 ^ 59
def prefixEnd_3851790 : Nat := 4983230072969 + 3 ^ 40 * 3851790 * 2
def baseEnd_3851790 : Nat := 1318546433454393391740631

theorem tailTrace_3851790 : CollatzResearch.WordTrace tailWord_3851790 prefixEnd_3851790 1318546433454393391740631 := by
  unfold tailWord_3851790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560790339453767275540103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93657548477086758802880549 17560790339453767275540103)
  ·
    refine ⟨26341185509180650913310155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17560790339453767275540103 26341185509180650913310155)
    ·
      refine ⟨39511778263770976369965233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26341185509180650913310155 39511778263770976369965233)
      ·
        refine ⟨29633833697828232277473925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39511778263770976369965233 29633833697828232277473925)
        ·
          refine ⟨5556343818342793552026361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29633833697828232277473925 5556343818342793552026361)
          ·
            refine ⟨4167257863757095164019771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5556343818342793552026361 4167257863757095164019771)
            ·
              refine ⟨6250886795635642746029657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167257863757095164019771 6250886795635642746029657)
              ·
                refine ⟨4688165096726732059522243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250886795635642746029657 4688165096726732059522243)
                ·
                  refine ⟨7032247645090098089283365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688165096726732059522243 7032247645090098089283365)
                  ·
                    refine ⟨1318546433454393391740631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7032247645090098089283365 1318546433454393391740631)
                    ·
                      rfl

theorem cell22_3851790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_3851790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851790 prefixEnd_3851790 := by exact prefixLift 3851790
  have htrace : WordTrace (prefixWord ++ tailWord_3851790) baseStart_3851790 baseEnd_3851790 := by
    simpa [prefixWord, tailWord_3851790, baseEnd_3851790] using wordTrace_append hprefix tailTrace_3851790
  have hstable : (prefixWord ++ tailWord_3851790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851790).length < 2 ^ (prefixWord ++ tailWord_3851790).sum := by decide
  have hdescent : baseEnd_3851790 < baseStart_3851790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851816 : List Nat := [2, 1, 5, 2, 2, 10]
def baseStart_3851816 : Nat := 118140960795 + 3851816 * 2 ^ 59
def prefixEnd_3851816 : Nat := 4983230072969 + 3 ^ 40 * 3851816 * 2
def baseEnd_3851816 : Nat := 16278460910935036920871

theorem tailTrace_3851816 : CollatzResearch.WordTrace tailWord_3851816 prefixEnd_3851816 16278460910935036920871 := by
  unfold tailWord_3851816
  simp only [CollatzResearch.WordTrace]
  refine ⟨70243635506767972322383651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93658180675690629763178201 70243635506767972322383651)
  ·
    refine ⟨105365453260151958483575477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70243635506767972322383651 105365453260151958483575477)
    ·
      refine ⟨9878011243139246107835201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105365453260151958483575477 9878011243139246107835201)
      ·
        refine ⟨7408508432354434580876401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9878011243139246107835201 7408508432354434580876401)
        ·
          refine ⟨5556381324265825935657301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7408508432354434580876401 5556381324265825935657301)
          ·
            refine ⟨16278460910935036920871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5556381324265825935657301 16278460910935036920871)
            ·
              rfl

theorem cell22_3851816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 10].length) (baseStart_3851816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851816 prefixEnd_3851816 := by exact prefixLift 3851816
  have htrace : WordTrace (prefixWord ++ tailWord_3851816) baseStart_3851816 baseEnd_3851816 := by
    simpa [prefixWord, tailWord_3851816, baseEnd_3851816] using wordTrace_append hprefix tailTrace_3851816
  have hstable : (prefixWord ++ tailWord_3851816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851816).length < 2 ^ (prefixWord ++ tailWord_3851816).sum := by decide
  have hdescent : baseEnd_3851816 < baseStart_3851816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851822 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_3851822 : Nat := 118140960795 + 3851822 * 2 ^ 59
def prefixEnd_3851822 : Nat := 4983230072969 + 3 ^ 40 * 3851822 * 2
def baseEnd_3851822 : Nat := 439519129236118658313511

theorem tailTrace_3851822 : CollatzResearch.WordTrace tailWord_3851822 prefixEnd_3851822 439519129236118658313511 := by
  unfold tailWord_3851822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560936231439275958685715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93658326567676138446323813 17560936231439275958685715)
  ·
    refine ⟨26341404347158913938028573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17560936231439275958685715 26341404347158913938028573)
    ·
      refine ⟨9878026630184592726760715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26341404347158913938028573 9878026630184592726760715)
      ·
        refine ⟨14817039945276889090141073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9878026630184592726760715 14817039945276889090141073)
        ·
          refine ⟨11112779958957666817605805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14817039945276889090141073 11112779958957666817605805)
          ·
            refine ⟨4167292484609125056602177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11112779958957666817605805 4167292484609125056602177)
            ·
              refine ⟨3125469363456843792451633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167292484609125056602177 3125469363456843792451633)
              ·
                refine ⟨2344102022592632844338725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125469363456843792451633 2344102022592632844338725)
                ·
                  refine ⟨439519129236118658313511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344102022592632844338725 439519129236118658313511)
                  ·
                    rfl

theorem cell22_3851822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_3851822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851822 prefixEnd_3851822 := by exact prefixLift 3851822
  have htrace : WordTrace (prefixWord ++ tailWord_3851822) baseStart_3851822 baseEnd_3851822 := by
    simpa [prefixWord, tailWord_3851822, baseEnd_3851822] using wordTrace_append hprefix tailTrace_3851822
  have hstable : (prefixWord ++ tailWord_3851822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851822).length < 2 ^ (prefixWord ++ tailWord_3851822).sum := by decide
  have hdescent : baseEnd_3851822 < baseStart_3851822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851876 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3851876 : Nat := 118140960795 + 3851876 * 2 ^ 59
def prefixEnd_3851876 : Nat := 4983230072969 + 3 ^ 40 * 3851876 * 2
def baseEnd_3851876 : Nat := 1318575873011917834090367

theorem tailTrace_3851876 : CollatzResearch.WordTrace tailWord_3851876 prefixEnd_3851876 1318575873011917834090367 := by
  unfold tailWord_3851876
  simp only [CollatzResearch.WordTrace]
  refine ⟨70244729696659287445975741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93659639595545716594634321 70244729696659287445975741)
  ·
    refine ⟨26341773636247232792240903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70244729696659287445975741 26341773636247232792240903)
    ·
      refine ⟨39512660454370849188361355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26341773636247232792240903 39512660454370849188361355)
      ·
        refine ⟨59268990681556273782542033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39512660454370849188361355 59268990681556273782542033)
        ·
          refine ⟨44451743011167205336906525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59268990681556273782542033 44451743011167205336906525)
          ·
            refine ⟨16669403629187702001339947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44451743011167205336906525 16669403629187702001339947)
            ·
              refine ⟨25004105443781553002009921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16669403629187702001339947 25004105443781553002009921)
              ·
                refine ⟨18753079082836164751507441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25004105443781553002009921 18753079082836164751507441)
                ·
                  refine ⟨14064809312127123563630581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18753079082836164751507441 14064809312127123563630581)
                  ·
                    refine ⟨1318575873011917834090367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14064809312127123563630581 1318575873011917834090367)
                    ·
                      rfl

theorem cell22_3851876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3851876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851876 prefixEnd_3851876 := by exact prefixLift 3851876
  have htrace : WordTrace (prefixWord ++ tailWord_3851876) baseStart_3851876 baseEnd_3851876 := by
    simpa [prefixWord, tailWord_3851876, baseEnd_3851876] using wordTrace_append hprefix tailTrace_3851876
  have hstable : (prefixWord ++ tailWord_3851876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851876).length < 2 ^ (prefixWord ++ tailWord_3851876).sum := by decide
  have hdescent : baseEnd_3851876 < baseStart_3851876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851893 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3851893 : Nat := 118140960795 + 3851893 * 2 ^ 59
def prefixEnd_3851893 : Nat := 4983230072969 + 3 ^ 40 * 3851893 * 2
def baseEnd_3851893 : Nat := 1318581692459335456415315

theorem tailTrace_3851893 : CollatzResearch.WordTrace tailWord_3851893 prefixEnd_3851893 1318581692459335456415315 := by
  unfold tailWord_3851893
  simp only [CollatzResearch.WordTrace]
  refine ⟨140490079434256986795320333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93660052956171324530213555 140490079434256986795320333)
  ·
    refine ⟨52683779787846370048245125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140490079434256986795320333 52683779787846370048245125)
    ·
      refine ⟨9878208710221194384045961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52683779787846370048245125 9878208710221194384045961)
      ·
        refine ⟨7408656532665895788034471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9878208710221194384045961 7408656532665895788034471)
        ·
          refine ⟨11112984798998843682051707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408656532665895788034471 11112984798998843682051707)
          ·
            refine ⟨16669477198498265523077561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112984798998843682051707 16669477198498265523077561)
            ·
              refine ⟨12502107898873699142308171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16669477198498265523077561 12502107898873699142308171)
              ·
                refine ⟨18753161848310548713462257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12502107898873699142308171 18753161848310548713462257)
                ·
                  refine ⟨14064871386232911535096693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18753161848310548713462257 14064871386232911535096693)
                  ·
                    refine ⟨1318581692459335456415315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14064871386232911535096693 1318581692459335456415315)
                    ·
                      rfl

theorem cell22_3851893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3851893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851893 prefixEnd_3851893 := by exact prefixLift 3851893
  have htrace : WordTrace (prefixWord ++ tailWord_3851893) baseStart_3851893 baseEnd_3851893 := by
    simpa [prefixWord, tailWord_3851893, baseEnd_3851893] using wordTrace_append hprefix tailTrace_3851893
  have hstable : (prefixWord ++ tailWord_3851893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851893).length < 2 ^ (prefixWord ++ tailWord_3851893).sum := by decide
  have hdescent : baseEnd_3851893 < baseStart_3851893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851951 : List Nat := [1, 1, 2, 1, 2, 4, 4, 7]
def baseStart_3851951 : Nat := 118140960795 + 3851951 * 2 ^ 59
def prefixEnd_3851951 : Nat := 4983230072969 + 3 ^ 40 * 3851951 * 2
def baseEnd_3851951 : Nat := 146511283004960293162793

theorem tailTrace_3851951 : CollatzResearch.WordTrace tailWord_3851951 prefixEnd_3851951 146511283004960293162793 := by
  unfold tailWord_3851951
  simp only [CollatzResearch.WordTrace]
  refine ⟨140492194868046862700931707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93661463245364575133954471 140492194868046862700931707)
  ·
    refine ⟨210738292302070294051397561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140492194868046862700931707 210738292302070294051397561)
    ·
      refine ⟨158053719226552720538548171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210738292302070294051397561 158053719226552720538548171)
      ·
        refine ⟨237080578839829080807822257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158053719226552720538548171 237080578839829080807822257)
        ·
          refine ⟨177810434129871810605866693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237080578839829080807822257 177810434129871810605866693)
          ·
            refine ⟨33339456399350964488600005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177810434129871810605866693 33339456399350964488600005)
            ·
              refine ⟨6251148074878305841612501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33339456399350964488600005 6251148074878305841612501)
              ·
                refine ⟨146511283004960293162793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6251148074878305841612501 146511283004960293162793)
                ·
                  rfl

theorem cell22_3851951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 7].length) (baseStart_3851951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851951 prefixEnd_3851951 := by exact prefixLift 3851951
  have htrace : WordTrace (prefixWord ++ tailWord_3851951) baseStart_3851951 baseEnd_3851951 := by
    simpa [prefixWord, tailWord_3851951, baseEnd_3851951] using wordTrace_append hprefix tailTrace_3851951
  have hstable : (prefixWord ++ tailWord_3851951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851951).length < 2 ^ (prefixWord ++ tailWord_3851951).sum := by decide
  have hdescent : baseEnd_3851951 < baseStart_3851951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852011 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_3852011 : Nat := 118140960795 + 3852011 * 2 ^ 59
def prefixEnd_3852011 : Nat := 4983230072969 + 3 ^ 40 * 3852011 * 2
def baseEnd_3852011 : Nat := 1318622086270822481964953

theorem tailTrace_3852011 : CollatzResearch.WordTrace tailWord_3852011 prefixEnd_3852011 1318622086270822481964953 := by
  unfold tailWord_3852011
  simp only [CollatzResearch.WordTrace]
  refine ⟨140494383247829492948115887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93662922165219661965410591 140494383247829492948115887)
  ·
    refine ⟨210741574871744239422173831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140494383247829492948115887 210741574871744239422173831)
    ·
      refine ⟨316112362307616359133260747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210741574871744239422173831 316112362307616359133260747)
      ·
        refine ⟨474168543461424538699891121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316112362307616359133260747 474168543461424538699891121)
        ·
          refine ⟨355626407596068404024918341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474168543461424538699891121 355626407596068404024918341)
          ·
            refine ⟨66679951424262825754672189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355626407596068404024918341 66679951424262825754672189)
            ·
              refine ⟨25004981784098559658002071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66679951424262825754672189 25004981784098559658002071)
              ·
                refine ⟨37507472676147839487003107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25004981784098559658002071 37507472676147839487003107)
                ·
                  refine ⟨56261209014221759230504661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37507472676147839487003107 56261209014221759230504661)
                  ·
                    refine ⟨1318622086270822481964953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56261209014221759230504661 1318622086270822481964953)
                    ·
                      rfl

theorem cell22_3852011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_3852011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852011 prefixEnd_3852011 := by exact prefixLift 3852011
  have htrace : WordTrace (prefixWord ++ tailWord_3852011) baseStart_3852011 baseEnd_3852011 := by
    simpa [prefixWord, tailWord_3852011, baseEnd_3852011] using wordTrace_append hprefix tailTrace_3852011
  have hstable : (prefixWord ++ tailWord_3852011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852011).length < 2 ^ (prefixWord ++ tailWord_3852011).sum := by decide
  have hdescent : baseEnd_3852011 < baseStart_3852011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852034 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3852034 : Nat := 118140960795 + 3852034 * 2 ^ 59
def prefixEnd_3852034 : Nat := 4983230072969 + 3 ^ 40 * 3852034 * 2
def baseEnd_3852034 : Nat := 1318629959640858088639883

theorem tailTrace_3852034 : CollatzResearch.WordTrace tailWord_3852034 prefixEnd_3852034 1318629959640858088639883 := by
  unfold tailWord_3852034
  simp only [CollatzResearch.WordTrace]
  refine ⟨35123805531686541969050789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93663481417830778584135437 35123805531686541969050789)
  ·
    refine ⟨6585713537191226619197023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35123805531686541969050789 6585713537191226619197023)
    ·
      refine ⟨9878570305786839928795535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585713537191226619197023 9878570305786839928795535)
      ·
        refine ⟨14817855458680259893193303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9878570305786839928795535 14817855458680259893193303)
        ·
          refine ⟨22226783188020389839789955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14817855458680259893193303 22226783188020389839789955)
          ·
            refine ⟨33340174782030584759684933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22226783188020389839789955 33340174782030584759684933)
            ·
              refine ⟨6251282771630734642440925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33340174782030584759684933 6251282771630734642440925)
              ·
                refine ⟨2344231039361525490915347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6251282771630734642440925 2344231039361525490915347)
                ·
                  refine ⟨3516346559042288236373021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344231039361525490915347 3516346559042288236373021)
                  ·
                    refine ⟨1318629959640858088639883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516346559042288236373021 1318629959640858088639883)
                    ·
                      rfl

theorem cell22_3852034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3852034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852034 prefixEnd_3852034 := by exact prefixLift 3852034
  have htrace : WordTrace (prefixWord ++ tailWord_3852034) baseStart_3852034 baseEnd_3852034 := by
    simpa [prefixWord, tailWord_3852034, baseEnd_3852034] using wordTrace_append hprefix tailTrace_3852034
  have hstable : (prefixWord ++ tailWord_3852034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852034).length < 2 ^ (prefixWord ++ tailWord_3852034).sum := by decide
  have hdescent : baseEnd_3852034 < baseStart_3852034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852041 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 10]
def baseStart_3852041 : Nat := 118140960795 + 3852041 * 2 ^ 59
def prefixEnd_3852041 : Nat := 4983230072969 + 3 ^ 40 * 3852041 * 2
def baseEnd_3852041 : Nat := 439544118627970801238287

theorem tailTrace_3852041 : CollatzResearch.WordTrace tailWord_3852041 prefixEnd_3852041 439544118627970801238287 := by
  unfold tailWord_3852041
  simp only [CollatzResearch.WordTrace]
  refine ⟨140495477437720808071707977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93663651625147205381138651 140495477437720808071707977)
  ·
    refine ⟨105371608078290606053780983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140495477437720808071707977 105371608078290606053780983)
    ·
      refine ⟨158057412117435909080671475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105371608078290606053780983 158057412117435909080671475)
      ·
        refine ⟨237086118176153863621007213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158057412117435909080671475 237086118176153863621007213)
        ·
          refine ⟨88907294316057698857877705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237086118176153863621007213 88907294316057698857877705)
          ·
            refine ⟨66680470737043274143408279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88907294316057698857877705 66680470737043274143408279)
            ·
              refine ⟨100020706105564911215112419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66680470737043274143408279 100020706105564911215112419)
              ·
                refine ⟨150031059158347366822668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100020706105564911215112419 150031059158347366822668629)
                ·
                  refine ⟨439544118627970801238287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150031059158347366822668629 439544118627970801238287)
                  ·
                    rfl

theorem cell22_3852041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_3852041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852041 prefixEnd_3852041 := by exact prefixLift 3852041
  have htrace : WordTrace (prefixWord ++ tailWord_3852041) baseStart_3852041 baseEnd_3852041 := by
    simpa [prefixWord, tailWord_3852041, baseEnd_3852041] using wordTrace_append hprefix tailTrace_3852041
  have hstable : (prefixWord ++ tailWord_3852041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852041).length < 2 ^ (prefixWord ++ tailWord_3852041).sum := by decide
  have hdescent : baseEnd_3852041 < baseStart_3852041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852058 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_3852058 : Nat := 118140960795 + 3852058 * 2 ^ 59
def prefixEnd_3852058 : Nat := 4983230072969 + 3 ^ 40 * 3852058 * 2
def baseEnd_3852058 : Nat := 439546058443776675346603

theorem tailTrace_3852058 : CollatzResearch.WordTrace tailWord_3852058 prefixEnd_3852058 439546058443776675346603 := by
  unfold tailWord_3852058
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124024369664804993769207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93664064985772813316717885 35124024369664804993769207)
  ·
    refine ⟨52686036554497207490653811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35124024369664804993769207 52686036554497207490653811)
    ·
      refine ⟨79029054831745811235980717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52686036554497207490653811 79029054831745811235980717)
      ·
        refine ⟨29635895561904679213492769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79029054831745811235980717 29635895561904679213492769)
        ·
          refine ⟨22226921671428509410119577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29635895561904679213492769 22226921671428509410119577)
          ·
            refine ⟨16670191253571382057589683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22226921671428509410119577 16670191253571382057589683)
            ·
              refine ⟨25005286880357073086384525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16670191253571382057589683 25005286880357073086384525)
              ·
                refine ⟨9376982580133902407394197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25005286880357073086384525 9376982580133902407394197)
                ·
                  refine ⟨439546058443776675346603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9376982580133902407394197 439546058443776675346603)
                  ·
                    rfl

theorem cell22_3852058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_3852058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852058 prefixEnd_3852058 := by exact prefixLift 3852058
  have htrace : WordTrace (prefixWord ++ tailWord_3852058) baseStart_3852058 baseEnd_3852058 := by
    simpa [prefixWord, tailWord_3852058, baseEnd_3852058] using wordTrace_append hprefix tailTrace_3852058
  have hstable : (prefixWord ++ tailWord_3852058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852058).length < 2 ^ (prefixWord ++ tailWord_3852058).sum := by decide
  have hdescent : baseEnd_3852058 < baseStart_3852058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_3852073 : Nat := 118140960795 + 3852073 * 2 ^ 59
def prefixEnd_3852073 : Nat := 4983230072969 + 3 ^ 40 * 3852073 * 2
def baseEnd_3852073 : Nat := 1318643310137874986914763

theorem tailTrace_3852073 : CollatzResearch.WordTrace tailWord_3852073 prefixEnd_3852073 1318643310137874986914763 := by
  unfold tailWord_3852073
  simp only [CollatzResearch.WordTrace]
  refine ⟨140496644573604877536872873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93664429715736585024581915 140496644573604877536872873)
  ·
    refine ⟨105372483430203658152654655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140496644573604877536872873 105372483430203658152654655)
    ·
      refine ⟨158058725145305487228981983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105372483430203658152654655 158058725145305487228981983)
      ·
        refine ⟨237088087717958230843472975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158058725145305487228981983 237088087717958230843472975)
        ·
          refine ⟨355632131576937346265209463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237088087717958230843472975 355632131576937346265209463)
          ·
            refine ⟨533448197365406019397814195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355632131576937346265209463 533448197365406019397814195)
            ·
              refine ⟨800172296048109029096721293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533448197365406019397814195 800172296048109029096721293)
              ·
                refine ⟨300064611018040885911270485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 800172296048109029096721293 300064611018040885911270485)
                ·
                  refine ⟨3516382160367666631772701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 300064611018040885911270485 3516382160367666631772701)
                  ·
                    refine ⟨1318643310137874986914763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516382160367666631772701 1318643310137874986914763)
                    ·
                      rfl

theorem cell22_3852073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_3852073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852073 prefixEnd_3852073 := by exact prefixLift 3852073
  have htrace : WordTrace (prefixWord ++ tailWord_3852073) baseStart_3852073 baseEnd_3852073 := by
    simpa [prefixWord, tailWord_3852073, baseEnd_3852073] using wordTrace_append hprefix tailTrace_3852073
  have hstable : (prefixWord ++ tailWord_3852073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852073).length < 2 ^ (prefixWord ++ tailWord_3852073).sum := by decide
  have hdescent : baseEnd_3852073 < baseStart_3852073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852088 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_3852088 : Nat := 118140960795 + 3852088 * 2 ^ 59
def prefixEnd_3852088 : Nat := 4983230072969 + 3 ^ 40 * 3852088 * 2
def baseEnd_3852088 : Nat := 1318648444944419947789717

theorem tailTrace_3852088 : CollatzResearch.WordTrace tailWord_3852088 prefixEnd_3852088 1318648444944419947789717 := by
  unfold tailWord_3852088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70248595834275267549334459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93664794445700356732445945 70248595834275267549334459)
  ·
    refine ⟨105372893751412901324001689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70248595834275267549334459 105372893751412901324001689)
    ·
      refine ⟨79029670313559675993001267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105372893751412901324001689 79029670313559675993001267)
      ·
        refine ⟨118544505470339513989501901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79029670313559675993001267 118544505470339513989501901)
        ·
          refine ⟨44454189551377317746063213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118544505470339513989501901 44454189551377317746063213)
          ·
            refine ⟨16670321081766494154773705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44454189551377317746063213 16670321081766494154773705)
            ·
              refine ⟨12502740811324870616080279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16670321081766494154773705 12502740811324870616080279)
              ·
                refine ⟨18754111216987305924120419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12502740811324870616080279 18754111216987305924120419)
                ·
                  refine ⟨28131166825480958886180629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18754111216987305924120419 28131166825480958886180629)
                  ·
                    refine ⟨1318648444944419947789717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28131166825480958886180629 1318648444944419947789717)
                    ·
                      rfl

theorem cell22_3852088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_3852088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852088 prefixEnd_3852088 := by exact prefixLift 3852088
  have htrace : WordTrace (prefixWord ++ tailWord_3852088) baseStart_3852088 baseEnd_3852088 := by
    simpa [prefixWord, tailWord_3852088, baseEnd_3852088] using wordTrace_append hprefix tailTrace_3852088
  have hstable : (prefixWord ++ tailWord_3852088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852088).length < 2 ^ (prefixWord ++ tailWord_3852088).sum := by decide
  have hdescent : baseEnd_3852088 < baseStart_3852088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852090 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_3852090 : Nat := 118140960795 + 3852090 * 2 ^ 59
def prefixEnd_3852090 : Nat := 4983230072969 + 3 ^ 40 * 3852090 * 2
def baseEnd_3852090 : Nat := 1318649129585292609239711

theorem tailTrace_3852090 : CollatzResearch.WordTrace tailWord_3852090 prefixEnd_3852090 1318649129585292609239711 := by
  unfold tailWord_3852090
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124316153635822360060431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93664843076362192960161149 35124316153635822360060431)
  ·
    refine ⟨52686474230453733540090647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35124316153635822360060431 52686474230453733540090647)
    ·
      refine ⟨79029711345680600310135971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52686474230453733540090647 79029711345680600310135971)
      ·
        refine ⟨118544567018520900465203957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79029711345680600310135971 118544567018520900465203957)
        ·
          refine ⟨11113553157986334418612871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118544567018520900465203957 11113553157986334418612871)
          ·
            refine ⟨16670329736979501627919307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113553157986334418612871 16670329736979501627919307)
            ·
              refine ⟨25005494605469252441878961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16670329736979501627919307 25005494605469252441878961)
              ·
                refine ⟨18754120954101939331409221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25005494605469252441878961 18754120954101939331409221)
                ·
                  refine ⟨3516397678894113624639229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18754120954101939331409221 3516397678894113624639229)
                  ·
                    refine ⟨1318649129585292609239711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516397678894113624639229 1318649129585292609239711)
                    ·
                      rfl

theorem cell22_3852090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_3852090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852090 prefixEnd_3852090 := by exact prefixLift 3852090
  have htrace : WordTrace (prefixWord ++ tailWord_3852090) baseStart_3852090 baseEnd_3852090 := by
    simpa [prefixWord, tailWord_3852090, baseEnd_3852090] using wordTrace_append hprefix tailTrace_3852090
  have hstable : (prefixWord ++ tailWord_3852090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852090).length < 2 ^ (prefixWord ++ tailWord_3852090).sum := by decide
  have hdescent : baseEnd_3852090 < baseStart_3852090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852124 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3852124 : Nat := 118140960795 + 3852124 * 2 ^ 59
def prefixEnd_3852124 : Nat := 4983230072969 + 3 ^ 40 * 3852124 * 2
def baseEnd_3852124 : Nat := 1318660768480127853889607

theorem tailTrace_3852124 : CollatzResearch.WordTrace tailWord_3852124 prefixEnd_3852124 1318660768480127853889607 := by
  unfold tailWord_3852124
  simp only [CollatzResearch.WordTrace]
  refine ⟨70249252348210056623489713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93665669797613408831319617 70249252348210056623489713)
  ·
    refine ⟨52686939261157542467617285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70249252348210056623489713 52686939261157542467617285)
    ·
      refine ⟨9878801111467039212678241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52686939261157542467617285 9878801111467039212678241)
      ·
        refine ⟨7409100833600279409508681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9878801111467039212678241 7409100833600279409508681)
        ·
          refine ⟨5556825625200209557131511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409100833600279409508681 5556825625200209557131511)
          ·
            refine ⟨8335238437800314335697267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556825625200209557131511 8335238437800314335697267)
            ·
              refine ⟨12502857656700471503545901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335238437800314335697267 12502857656700471503545901)
              ·
                refine ⟨4688571621262676813829713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12502857656700471503545901 4688571621262676813829713)
                ·
                  refine ⟨3516428715947007610372285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4688571621262676813829713 3516428715947007610372285)
                  ·
                    refine ⟨1318660768480127853889607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516428715947007610372285 1318660768480127853889607)
                    ·
                      rfl

theorem cell22_3852124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3852124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852124 prefixEnd_3852124 := by exact prefixLift 3852124
  have htrace : WordTrace (prefixWord ++ tailWord_3852124) baseStart_3852124 baseEnd_3852124 := by
    simpa [prefixWord, tailWord_3852124, baseEnd_3852124] using wordTrace_append hprefix tailTrace_3852124
  have hstable : (prefixWord ++ tailWord_3852124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852124).length < 2 ^ (prefixWord ++ tailWord_3852124).sum := by decide
  have hdescent : baseEnd_3852124 < baseStart_3852124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852135 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3852135 : Nat := 118140960795 + 3852135 * 2 ^ 59
def prefixEnd_3852135 : Nat := 4983230072969 + 3 ^ 40 * 3852135 * 2
def baseEnd_3852135 : Nat := 1318664534004927491864573

theorem tailTrace_3852135 : CollatzResearch.WordTrace tailWord_3852135 prefixEnd_3852135 1318664534004927491864573 := by
  unfold tailWord_3852135
  simp only [CollatzResearch.WordTrace]
  refine ⟨140498905899380262125629859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93665937266253508083753239 140498905899380262125629859)
  ·
    refine ⟨210748358849070393188444789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140498905899380262125629859 210748358849070393188444789)
    ·
      refine ⟨19757658642100349361416699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210748358849070393188444789 19757658642100349361416699)
      ·
        refine ⟨29636487963150524042125049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19757658642100349361416699 29636487963150524042125049)
        ·
          refine ⟨22227365972362893031593787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29636487963150524042125049 22227365972362893031593787)
          ·
            refine ⟨33341048958544339547390681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22227365972362893031593787 33341048958544339547390681)
            ·
              refine ⟨25005786718908254660543011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33341048958544339547390681 25005786718908254660543011)
              ·
                refine ⟨37508680078362381990814517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25005786718908254660543011 37508680078362381990814517)
                ·
                  refine ⟨3516438757346473311638861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37508680078362381990814517 3516438757346473311638861)
                  ·
                    refine ⟨1318664534004927491864573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516438757346473311638861 1318664534004927491864573)
                    ·
                      rfl

theorem cell22_3852135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3852135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852135 prefixEnd_3852135 := by exact prefixLift 3852135
  have htrace : WordTrace (prefixWord ++ tailWord_3852135) baseStart_3852135 baseEnd_3852135 := by
    simpa [prefixWord, tailWord_3852135, baseEnd_3852135] using wordTrace_append hprefix tailTrace_3852135
  have hstable : (prefixWord ++ tailWord_3852135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852135).length < 2 ^ (prefixWord ++ tailWord_3852135).sum := by decide
  have hdescent : baseEnd_3852135 < baseStart_3852135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852165 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 5]
def baseStart_3852165 : Nat := 118140960795 + 3852165 * 2 ^ 59
def prefixEnd_3852165 : Nat := 4983230072969 + 3 ^ 40 * 3852165 * 2
def baseEnd_3852165 : Nat := 439558267872672471204827

theorem tailTrace_3852165 : CollatzResearch.WordTrace tailWord_3852165 prefixEnd_3852165 439558267872672471204827 := by
  unfold tailWord_3852165
  simp only [CollatzResearch.WordTrace]
  refine ⟨140500000089271577249221949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93666666726181051499481299 140500000089271577249221949)
  ·
    refine ⟨52687500033476841468458231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140500000089271577249221949 52687500033476841468458231)
    ·
      refine ⟨79031250050215262202687347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52687500033476841468458231 79031250050215262202687347)
      ·
        refine ⟨118546875075322893304031021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79031250050215262202687347 118546875075322893304031021)
        ·
          refine ⟨44455078153246084989011633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118546875075322893304031021 44455078153246084989011633)
          ·
            refine ⟨33341308614934563741758725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44455078153246084989011633 33341308614934563741758725)
            ·
              refine ⟨6251495365300230701579761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33341308614934563741758725 6251495365300230701579761)
              ·
                refine ⟨4688621523975173026184821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251495365300230701579761 4688621523975173026184821)
                ·
                  refine ⟨439558267872672471204827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4688621523975173026184821 439558267872672471204827)
                  ·
                    rfl

theorem cell22_3852165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_3852165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852165 prefixEnd_3852165 := by exact prefixLift 3852165
  have htrace : WordTrace (prefixWord ++ tailWord_3852165) baseStart_3852165 baseEnd_3852165 := by
    simpa [prefixWord, tailWord_3852165, baseEnd_3852165] using wordTrace_append hprefix tailTrace_3852165
  have hstable : (prefixWord ++ tailWord_3852165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852165).length < 2 ^ (prefixWord ++ tailWord_3852165).sum := by decide
  have hdescent : baseEnd_3852165 < baseStart_3852165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852180 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3852180 : Nat := 118140960795 + 3852180 * 2 ^ 59
def prefixEnd_3852180 : Nat := 4983230072969 + 3 ^ 40 * 3852180 * 2
def baseEnd_3852180 : Nat := 1318679938424562374489435

theorem tailTrace_3852180 : CollatzResearch.WordTrace tailWord_3852180 prefixEnd_3852180 1318679938424562374489435 := by
  unfold tailWord_3852180
  simp only [CollatzResearch.WordTrace]
  refine ⟨70250273592108617405508997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93667031456144823207345329 70250273592108617405508997)
  ·
    refine ⟨13171926298520365763532937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70250273592108617405508997 13171926298520365763532937)
    ·
      refine ⟨9878944723890274322649703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13171926298520365763532937 9878944723890274322649703)
      ·
        refine ⟨14818417085835411483974555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9878944723890274322649703 14818417085835411483974555)
        ·
          refine ⟨22227625628753117225961833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14818417085835411483974555 22227625628753117225961833)
          ·
            refine ⟨16670719221564837919471375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22227625628753117225961833 16670719221564837919471375)
            ·
              refine ⟨25006078832347256879207063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16670719221564837919471375 25006078832347256879207063)
              ·
                refine ⟨37509118248520885318810595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25006078832347256879207063 37509118248520885318810595)
                ·
                  refine ⟨56263677372781327978215893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37509118248520885318810595 56263677372781327978215893)
                  ·
                    refine ⟨1318679938424562374489435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56263677372781327978215893 1318679938424562374489435)
                    ·
                      rfl

theorem cell22_3852180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3852180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852180 prefixEnd_3852180 := by exact prefixLift 3852180
  have htrace : WordTrace (prefixWord ++ tailWord_3852180) baseStart_3852180 baseEnd_3852180 := by
    simpa [prefixWord, tailWord_3852180, baseEnd_3852180] using wordTrace_append hprefix tailTrace_3852180
  have hstable : (prefixWord ++ tailWord_3852180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852180).length < 2 ^ (prefixWord ++ tailWord_3852180).sum := by decide
  have hdescent : baseEnd_3852180 < baseStart_3852180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852195 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 1, 4]
def baseStart_3852195 : Nat := 118140960795 + 3852195 * 2 ^ 59
def prefixEnd_3852195 : Nat := 4983230072969 + 3 ^ 40 * 3852195 * 2
def baseEnd_3852195 : Nat := 1318685073231107335364389

theorem tailTrace_3852195 : CollatzResearch.WordTrace tailWord_3852195 prefixEnd_3852195 1318685073231107335364389 := by
  unfold tailWord_3852195
  simp only [CollatzResearch.WordTrace]
  refine ⟨140501094279162892372814039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93667396186108594915209359 140501094279162892372814039)
  ·
    refine ⟨210751641418744338559221059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140501094279162892372814039 210751641418744338559221059)
    ·
      refine ⟨316127462128116507838831589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210751641418744338559221059 316127462128116507838831589)
      ·
        refine ⟨59273899149021845219780923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316127462128116507838831589 59273899149021845219780923)
        ·
          refine ⟨88910848723532767829671385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59273899149021845219780923 88910848723532767829671385)
          ·
            refine ⟨66683136542649575872253539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88910848723532767829671385 66683136542649575872253539)
            ·
              refine ⟨100024704813974363808380309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66683136542649575872253539 100024704813974363808380309)
              ·
                refine ⟨4688658038155048303517827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100024704813974363808380309 4688658038155048303517827)
                ·
                  refine ⟨7032987057232572455276741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688658038155048303517827 7032987057232572455276741)
                  ·
                    refine ⟨1318685073231107335364389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7032987057232572455276741 1318685073231107335364389)
                    ·
                      rfl

theorem cell22_3852195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 4].length) (baseStart_3852195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852195 prefixEnd_3852195 := by exact prefixLift 3852195
  have htrace : WordTrace (prefixWord ++ tailWord_3852195) baseStart_3852195 baseEnd_3852195 := by
    simpa [prefixWord, tailWord_3852195, baseEnd_3852195] using wordTrace_append hprefix tailTrace_3852195
  have hstable : (prefixWord ++ tailWord_3852195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852195).length < 2 ^ (prefixWord ++ tailWord_3852195).sum := by decide
  have hdescent : baseEnd_3852195 < baseStart_3852195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852246 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3852246 : Nat := 118140960795 + 3852246 * 2 ^ 59
def prefixEnd_3852246 : Nat := 4983230072969 + 3 ^ 40 * 3852246 * 2
def baseEnd_3852246 : Nat := 1318702531573360202339233

theorem tailTrace_3852246 : CollatzResearch.WordTrace tailWord_3852246 prefixEnd_3852246 1318702531573360202339233 := by
  unfold tailWord_3852246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781434650123633005182537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93668636267985418721947061 8781434650123633005182537)
  ·
    refine ⟨6586075987592724753886903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8781434650123633005182537 6586075987592724753886903)
    ·
      refine ⟨9879113981389087130830355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6586075987592724753886903 9879113981389087130830355)
      ·
        refine ⟨14818670972083630696245533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879113981389087130830355 14818670972083630696245533)
        ·
          refine ⟨5557001614531361511092075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14818670972083630696245533 5557001614531361511092075)
          ·
            refine ⟨8335502421797042266638113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557001614531361511092075 8335502421797042266638113)
            ·
              refine ⟨6251626816347781699978585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335502421797042266638113 6251626816347781699978585)
              ·
                refine ⟨4688720112260836274983939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251626816347781699978585 4688720112260836274983939)
                ·
                  refine ⟨7033080168391254412475909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688720112260836274983939 7033080168391254412475909)
                  ·
                    refine ⟨1318702531573360202339233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033080168391254412475909 1318702531573360202339233)
                    ·
                      rfl

theorem cell22_3852246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3852246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852246 prefixEnd_3852246 := by exact prefixLift 3852246
  have htrace : WordTrace (prefixWord ++ tailWord_3852246) baseStart_3852246 baseEnd_3852246 := by
    simpa [prefixWord, tailWord_3852246, baseEnd_3852246] using wordTrace_append hprefix tailTrace_3852246
  have hstable : (prefixWord ++ tailWord_3852246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852246).length < 2 ^ (prefixWord ++ tailWord_3852246).sum := by decide
  have hdescent : baseEnd_3852246 < baseStart_3852246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852255 : List Nat := [1, 1, 2, 3, 4, 2, 1, 8]
def baseStart_3852255 : Nat := 118140960795 + 3852255 * 2 ^ 59
def prefixEnd_3852255 : Nat := 4983230072969 + 3 ^ 40 * 3852255 * 2
def baseEnd_3852255 : Nat := 146522845828587464318245

theorem tailTrace_3852255 : CollatzResearch.WordTrace tailWord_3852255 prefixEnd_3852255 146522845828587464318245 := by
  unfold tailWord_3852255
  simp only [CollatzResearch.WordTrace]
  refine ⟨140503282658945522619998219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93668855105963681746665479 140503282658945522619998219)
  ·
    refine ⟨210754923988418283929997329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140503282658945522619998219 210754923988418283929997329)
    ·
      refine ⟨158066192991313712947497997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210754923988418283929997329 158066192991313712947497997)
      ·
        refine ⟨59274822371742642355311749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158066192991313712947497997 59274822371742642355311749)
        ·
          refine ⟨11114029194701745441620953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59274822371742642355311749 11114029194701745441620953)
          ·
            refine ⟨8335521896026309081215715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114029194701745441620953 8335521896026309081215715)
            ·
              refine ⟨12503282844039463621823573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335521896026309081215715 12503282844039463621823573)
              ·
                refine ⟨146522845828587464318245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12503282844039463621823573 146522845828587464318245)
                ·
                  rfl

theorem cell22_3852255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 8].length) (baseStart_3852255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852255 prefixEnd_3852255 := by exact prefixLift 3852255
  have htrace : WordTrace (prefixWord ++ tailWord_3852255) baseStart_3852255 baseEnd_3852255 := by
    simpa [prefixWord, tailWord_3852255, baseEnd_3852255] using wordTrace_append hprefix tailTrace_3852255
  have hstable : (prefixWord ++ tailWord_3852255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852255).length < 2 ^ (prefixWord ++ tailWord_3852255).sum := by decide
  have hdescent : baseEnd_3852255 < baseStart_3852255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852334 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3852334 : Nat := 118140960795 + 3852334 * 2 ^ 59
def prefixEnd_3852334 : Nat := 4983230072969 + 3 ^ 40 * 3852334 * 2
def baseEnd_3852334 : Nat := 439577551923919102046321

theorem tailTrace_3852334 : CollatzResearch.WordTrace tailWord_3852334 prefixEnd_3852334 439577551923919102046321 := by
  unfold tailWord_3852334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563270503207414889015507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93670776017106212741416037 17563270503207414889015507)
  ·
    refine ⟨26344905754811122333523261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17563270503207414889015507 26344905754811122333523261)
    ·
      refine ⟨9879339658054170875071223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26344905754811122333523261 9879339658054170875071223)
      ·
        refine ⟨14819009487081256312606835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879339658054170875071223 14819009487081256312606835)
        ·
          refine ⟨22228514230621884468910253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14819009487081256312606835 22228514230621884468910253)
          ·
            refine ⟨8335692836483206675841345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22228514230621884468910253 8335692836483206675841345)
            ·
              refine ⟨6251769627362405006881009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335692836483206675841345 6251769627362405006881009)
              ·
                refine ⟨4688827220521803755160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251769627362405006881009 4688827220521803755160757)
                ·
                  refine ⟨439577551923919102046321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4688827220521803755160757 439577551923919102046321)
                  ·
                    rfl

theorem cell22_3852334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3852334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852334 prefixEnd_3852334 := by exact prefixLift 3852334
  have htrace : WordTrace (prefixWord ++ tailWord_3852334) baseStart_3852334 baseEnd_3852334 := by
    simpa [prefixWord, tailWord_3852334, baseEnd_3852334] using wordTrace_append hprefix tailTrace_3852334
  have hstable : (prefixWord ++ tailWord_3852334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852334).length < 2 ^ (prefixWord ++ tailWord_3852334).sum := by decide
  have hdescent : baseEnd_3852334 < baseStart_3852334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852338 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_3852338 : Nat := 118140960795 + 3852338 * 2 ^ 59
def prefixEnd_3852338 : Nat := 4983230072969 + 3 ^ 40 * 3852338 * 2
def baseEnd_3852338 : Nat := 1318734025053502629038951

theorem tailTrace_3852338 : CollatzResearch.WordTrace tailWord_3852338 prefixEnd_3852338 1318734025053502629038951 := by
  unfold tailWord_3852338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35126577479411206948817417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93670873278429885196846445 35126577479411206948817417)
  ·
    refine ⟨26344933109558405211613063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35126577479411206948817417 26344933109558405211613063)
    ·
      refine ⟨39517399664337607817419595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26344933109558405211613063 39517399664337607817419595)
      ·
        refine ⟨59276099496506411726129393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39517399664337607817419595 59276099496506411726129393)
        ·
          refine ⟨44457074622379808794597045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59276099496506411726129393 44457074622379808794597045)
          ·
            refine ⟨4167850745848107074493473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44457074622379808794597045 4167850745848107074493473)
            ·
              refine ⟨3125888059386080305870105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167850745848107074493473 3125888059386080305870105)
              ·
                refine ⟨2344416044539560229402579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125888059386080305870105 2344416044539560229402579)
                ·
                  refine ⟨3516624066809340344103869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344416044539560229402579 3516624066809340344103869)
                  ·
                    refine ⟨1318734025053502629038951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516624066809340344103869 1318734025053502629038951)
                    ·
                      rfl

theorem cell22_3852338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_3852338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852338 prefixEnd_3852338 := by exact prefixLift 3852338
  have htrace : WordTrace (prefixWord ++ tailWord_3852338) baseStart_3852338 baseEnd_3852338 := by
    simpa [prefixWord, tailWord_3852338, baseEnd_3852338] using wordTrace_append hprefix tailTrace_3852338
  have hstable : (prefixWord ++ tailWord_3852338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852338).length < 2 ^ (prefixWord ++ tailWord_3852338).sum := by decide
  have hdescent : baseEnd_3852338 < baseStart_3852338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852377 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_3852377 : Nat := 118140960795 + 3852377 * 2 ^ 59
def prefixEnd_3852377 : Nat := 4983230072969 + 3 ^ 40 * 3852377 * 2
def baseEnd_3852377 : Nat := 1318747375550519527313831

theorem tailTrace_3852377 : CollatzResearch.WordTrace tailWord_3852377 prefixEnd_3852377 1318747375550519527313831 := by
  unfold tailWord_3852377
  simp only [CollatzResearch.WordTrace]
  refine ⟨140507732364503537455939385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93671821576335691637292923 140507732364503537455939385)
  ·
    refine ⟨105380799273377653091954539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140507732364503537455939385 105380799273377653091954539)
    ·
      refine ⟨158071198910066479637931809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105380799273377653091954539 158071198910066479637931809)
      ·
        refine ⟨118553399182549859728448857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158071198910066479637931809 118553399182549859728448857)
        ·
          refine ⟨88915049386912394796336643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118553399182549859728448857 88915049386912394796336643)
          ·
            refine ⟨133372574080368592194504965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88915049386912394796336643 133372574080368592194504965)
            ·
              refine ⟨25007357640069111036469681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133372574080368592194504965 25007357640069111036469681)
              ·
                refine ⟨18755518230051833277352261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25007357640069111036469681 18755518230051833277352261)
                ·
                  refine ⟨3516659668134718739503549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18755518230051833277352261 3516659668134718739503549)
                  ·
                    refine ⟨1318747375550519527313831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516659668134718739503549 1318747375550519527313831)
                    ·
                      rfl

theorem cell22_3852377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_3852377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852377 prefixEnd_3852377 := by exact prefixLift 3852377
  have htrace : WordTrace (prefixWord ++ tailWord_3852377) baseStart_3852377 baseEnd_3852377 := by
    simpa [prefixWord, tailWord_3852377, baseEnd_3852377] using wordTrace_append hprefix tailTrace_3852377
  have hstable : (prefixWord ++ tailWord_3852377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852377).length < 2 ^ (prefixWord ++ tailWord_3852377).sum := by decide
  have hdescent : baseEnd_3852377 < baseStart_3852377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852381 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3852381 : Nat := 118140960795 + 3852381 * 2 ^ 59
def prefixEnd_3852381 : Nat := 4983230072969 + 3 ^ 40 * 3852381 * 2
def baseEnd_3852381 : Nat := 1318748744832264850213819

theorem tailTrace_3852381 : CollatzResearch.WordTrace tailWord_3852381 prefixEnd_3852381 1318748744832264850213819 := by
  unfold tailWord_3852381
  simp only [CollatzResearch.WordTrace]
  refine ⟨140507878256489046139084997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93671918837659364092723331 140507878256489046139084997)
  ·
    refine ⟨26345227173091696151078437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140507878256489046139084997 26345227173091696151078437)
    ·
      refine ⟨4939730094954693028327207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26345227173091696151078437 4939730094954693028327207)
      ·
        refine ⟨7409595142432039542490811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939730094954693028327207 7409595142432039542490811)
        ·
          refine ⟨11114392713648059313736217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409595142432039542490811 11114392713648059313736217)
          ·
            refine ⟨8335794535236044485302163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114392713648059313736217 8335794535236044485302163)
            ·
              refine ⟨12503691802854066727953245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335794535236044485302163 12503691802854066727953245)
              ·
                refine ⟨4688884426070275022982467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12503691802854066727953245 4688884426070275022982467)
                ·
                  refine ⟨7033326639105412534473701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688884426070275022982467 7033326639105412534473701)
                  ·
                    refine ⟨1318748744832264850213819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033326639105412534473701 1318748744832264850213819)
                    ·
                      rfl

theorem cell22_3852381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3852381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852381 prefixEnd_3852381 := by exact prefixLift 3852381
  have htrace : WordTrace (prefixWord ++ tailWord_3852381) baseStart_3852381 baseEnd_3852381 := by
    simpa [prefixWord, tailWord_3852381, baseEnd_3852381] using wordTrace_append hprefix tailTrace_3852381
  have hstable : (prefixWord ++ tailWord_3852381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852381).length < 2 ^ (prefixWord ++ tailWord_3852381).sum := by decide
  have hdescent : baseEnd_3852381 < baseStart_3852381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852424 : List Nat := [2, 1, 3, 4, 1, 1, 4, 6]
def baseStart_3852424 : Nat := 118140960795 + 3852424 * 2 ^ 59
def prefixEnd_3852424 : Nat := 4983230072969 + 3 ^ 40 * 3852424 * 2
def baseEnd_3852424 : Nat := 146529273845669674598743

theorem tailTrace_3852424 : CollatzResearch.WordTrace tailWord_3852424 prefixEnd_3852424 146529273845669674598743 := by
  unfold tailWord_3852424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70254723297666632241450163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93672964396888842988600217 70254723297666632241450163)
  ·
    refine ⟨105382084946499948362175245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70254723297666632241450163 105382084946499948362175245)
    ·
      refine ⟨39518281854937480635815717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105382084946499948362175245 39518281854937480635815717)
      ·
        refine ⟨7409677847800777619215447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39518281854937480635815717 7409677847800777619215447)
        ·
          refine ⟨11114516771701166428823171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409677847800777619215447 11114516771701166428823171)
          ·
            refine ⟨16671775157551749643234757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11114516771701166428823171 16671775157551749643234757)
            ·
              refine ⟨3125957842040953058106517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16671775157551749643234757 3125957842040953058106517)
              ·
                refine ⟨146529273845669674598743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3125957842040953058106517 146529273845669674598743)
                ·
                  rfl

theorem cell22_3852424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_3852424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852424 prefixEnd_3852424 := by exact prefixLift 3852424
  have htrace : WordTrace (prefixWord ++ tailWord_3852424) baseStart_3852424 baseEnd_3852424 := by
    simpa [prefixWord, tailWord_3852424, baseEnd_3852424] using wordTrace_append hprefix tailTrace_3852424
  have hstable : (prefixWord ++ tailWord_3852424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852424).length < 2 ^ (prefixWord ++ tailWord_3852424).sum := by decide
  have hdescent : baseEnd_3852424 < baseStart_3852424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852462 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3852462 : Nat := 118140960795 + 3852462 * 2 ^ 59
def prefixEnd_3852462 : Nat := 4983230072969 + 3 ^ 40 * 3852462 * 2
def baseEnd_3852462 : Nat := 1318776472787607638938571

theorem tailTrace_3852462 : CollatzResearch.WordTrace tailWord_3852462 prefixEnd_3852462 1318776472787607638938571 := by
  unfold tailWord_3852462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563854071149449621597955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93673888379463731315189093 17563854071149449621597955)
  ·
    refine ⟨26345781106724174432396933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17563854071149449621597955 26345781106724174432396933)
    ·
      refine ⟨4939833957510782706074425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26345781106724174432396933 4939833957510782706074425)
      ·
        refine ⟨3704875468133087029555819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4939833957510782706074425 3704875468133087029555819)
        ·
          refine ⟨5557313202199630544333729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704875468133087029555819 5557313202199630544333729)
          ·
            refine ⟨4167984901649722908250297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557313202199630544333729 4167984901649722908250297)
            ·
              refine ⟨3125988676237292181187723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167984901649722908250297 3125988676237292181187723)
              ·
                refine ⟨4688983014355938271781585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125988676237292181187723 4688983014355938271781585)
                ·
                  refine ⟨3516737260766953703836189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4688983014355938271781585 3516737260766953703836189)
                  ·
                    refine ⟨1318776472787607638938571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516737260766953703836189 1318776472787607638938571)
                    ·
                      rfl

theorem cell22_3852462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3852462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852462 prefixEnd_3852462 := by exact prefixLift 3852462
  have htrace : WordTrace (prefixWord ++ tailWord_3852462) baseStart_3852462 baseEnd_3852462 := by
    simpa [prefixWord, tailWord_3852462, baseEnd_3852462] using wordTrace_append hprefix tailTrace_3852462
  have hstable : (prefixWord ++ tailWord_3852462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852462).length < 2 ^ (prefixWord ++ tailWord_3852462).sum := by decide
  have hdescent : baseEnd_3852462 < baseStart_3852462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852512 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_3852512 : Nat := 118140960795 + 3852512 * 2 ^ 59
def prefixEnd_3852512 : Nat := 4983230072969 + 3 ^ 40 * 3852512 * 2
def baseEnd_3852512 : Nat := 1318793588809424175188417

theorem tailTrace_3852512 : CollatzResearch.WordTrace tailWord_3852512 prefixEnd_3852512 1318793588809424175188417 := by
  unfold tailWord_3852512
  simp only [CollatzResearch.WordTrace]
  refine ⟨70256328109507227756051895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93675104146009637008069193 70256328109507227756051895)
  ·
    refine ⟨105384492164260841634077843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70256328109507227756051895 105384492164260841634077843)
    ·
      refine ⟨158076738246391262451116765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105384492164260841634077843 158076738246391262451116765)
      ·
        refine ⟨59278776842396723419168787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158076738246391262451116765 59278776842396723419168787)
        ·
          refine ⟨88918165263595085128753181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59278776842396723419168787 88918165263595085128753181)
          ·
            refine ⟨33344311973848156923282443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88918165263595085128753181 33344311973848156923282443)
            ·
              refine ⟨50016467960772235384923665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33344311973848156923282443 50016467960772235384923665)
              ·
                refine ⟨37512350970579176538692749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50016467960772235384923665 37512350970579176538692749)
                ·
                  refine ⟨14067131613967191202009781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37512350970579176538692749 14067131613967191202009781)
                  ·
                    refine ⟨1318793588809424175188417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14067131613967191202009781 1318793588809424175188417)
                    ·
                      rfl

theorem cell22_3852512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_3852512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852512 prefixEnd_3852512 := by exact prefixLift 3852512
  have htrace : WordTrace (prefixWord ++ tailWord_3852512) baseStart_3852512 baseEnd_3852512 := by
    simpa [prefixWord, tailWord_3852512, baseEnd_3852512] using wordTrace_append hprefix tailTrace_3852512
  have hstable : (prefixWord ++ tailWord_3852512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852512).length < 2 ^ (prefixWord ++ tailWord_3852512).sum := by decide
  have hdescent : baseEnd_3852512 < baseStart_3852512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852544 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_3852544 : Nat := 118140960795 + 3852544 * 2 ^ 59
def prefixEnd_3852544 : Nat := 4983230072969 + 3 ^ 40 * 3852544 * 2
def baseEnd_3852544 : Nat := 1318804543063386758388319

theorem tailTrace_3852544 : CollatzResearch.WordTrace tailWord_3852544 prefixEnd_3852544 1318804543063386758388319 := by
  unfold tailWord_3852544
  simp only [CollatzResearch.WordTrace]
  refine ⟨70256911677449262488634343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93675882236599016651512457 70256911677449262488634343)
  ·
    refine ⟨105385367516173893732951515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70256911677449262488634343 105385367516173893732951515)
    ·
      refine ⟨158078051274260840599427273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105385367516173893732951515 158078051274260840599427273)
      ·
        refine ⟨118558538455695630449570455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158078051274260840599427273 118558538455695630449570455)
        ·
          refine ⟨177837807683543445674355683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118558538455695630449570455 177837807683543445674355683)
          ·
            refine ⟨266756711525315168511533525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177837807683543445674355683 266756711525315168511533525)
            ·
              refine ⟨6252110426374574261989067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 266756711525315168511533525 6252110426374574261989067)
              ·
                refine ⟨9378165639561861392983601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252110426374574261989067 9378165639561861392983601)
                ·
                  refine ⟨7033624229671396044737701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9378165639561861392983601 7033624229671396044737701)
                  ·
                    refine ⟨1318804543063386758388319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033624229671396044737701 1318804543063386758388319)
                    ·
                      rfl

theorem cell22_3852544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_3852544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852544 prefixEnd_3852544 := by exact prefixLift 3852544
  have htrace : WordTrace (prefixWord ++ tailWord_3852544) baseStart_3852544 baseEnd_3852544 := by
    simpa [prefixWord, tailWord_3852544, baseEnd_3852544] using wordTrace_append hprefix tailTrace_3852544
  have hstable : (prefixWord ++ tailWord_3852544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852544).length < 2 ^ (prefixWord ++ tailWord_3852544).sum := by decide
  have hdescent : baseEnd_3852544 < baseStart_3852544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852546 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3852546 : Nat := 118140960795 + 3852546 * 2 ^ 59
def prefixEnd_3852546 : Nat := 4983230072969 + 3 ^ 40 * 3852546 * 2
def baseEnd_3852546 : Nat := 1318805227704259419838313

theorem tailTrace_3852546 : CollatzResearch.WordTrace tailWord_3852546 prefixEnd_3852546 1318805227704259419838313 := by
  unfold tailWord_3852546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35128474075222819829710373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93675930867260852879227661 35128474075222819829710373)
  ·
    refine ⟨6586588889104278718070695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35128474075222819829710373 6586588889104278718070695)
    ·
      refine ⟨9879883333656418077106043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6586588889104278718070695 9879883333656418077106043)
      ·
        refine ⟨14819825000484627115659065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879883333656418077106043 14819825000484627115659065)
        ·
          refine ⟨11114868750363470336744299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14819825000484627115659065 11114868750363470336744299)
          ·
            refine ⟨16672303125545205505116449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11114868750363470336744299 16672303125545205505116449)
            ·
              refine ⟨12504227344158904128837337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16672303125545205505116449 12504227344158904128837337)
              ·
                refine ⟨9378170508119178096628003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12504227344158904128837337 9378170508119178096628003)
                ·
                  refine ⟨14067255762178767144942005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378170508119178096628003 14067255762178767144942005)
                  ·
                    refine ⟨1318805227704259419838313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14067255762178767144942005 1318805227704259419838313)
                    ·
                      rfl

theorem cell22_3852546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3852546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852546 prefixEnd_3852546 := by exact prefixLift 3852546
  have htrace : WordTrace (prefixWord ++ tailWord_3852546) baseStart_3852546 baseEnd_3852546 := by
    simpa [prefixWord, tailWord_3852546, baseEnd_3852546] using wordTrace_append hprefix tailTrace_3852546
  have hstable : (prefixWord ++ tailWord_3852546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852546).length < 2 ^ (prefixWord ++ tailWord_3852546).sum := by decide
  have hdescent : baseEnd_3852546 < baseStart_3852546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852548 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 4]
def baseStart_3852548 : Nat := 118140960795 + 3852548 * 2 ^ 59
def prefixEnd_3852548 : Nat := 4983230072969 + 3 ^ 40 * 3852548 * 2
def baseEnd_3852548 : Nat := 439601970781710693762769

theorem tailTrace_3852548 : CollatzResearch.WordTrace tailWord_3852548 prefixEnd_3852548 439601970781710693762769 := by
  unfold tailWord_3852548
  simp only [CollatzResearch.WordTrace]
  refine ⟨70256984623442016830207149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93675979497922689106942865 70256984623442016830207149)
  ·
    refine ⟨26346369233790756311327681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70256984623442016830207149 26346369233790756311327681)
    ·
      refine ⟨19759776925343067233495761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26346369233790756311327681 19759776925343067233495761)
      ·
        refine ⟨14819832694007300425121821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19759776925343067233495761 14819832694007300425121821)
        ·
          refine ⟨5557437260252737659420683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14819832694007300425121821 5557437260252737659420683)
          ·
            refine ⟨8336155890379106489131025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557437260252737659420683 8336155890379106489131025)
            ·
              refine ⟨6252116917784329866848269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8336155890379106489131025 6252116917784329866848269)
              ·
                refine ⟨2344543844169123700068101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252116917784329866848269 2344543844169123700068101)
                ·
                  refine ⟨439601970781710693762769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344543844169123700068101 439601970781710693762769)
                  ·
                    rfl

theorem cell22_3852548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_3852548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852548 prefixEnd_3852548 := by exact prefixLift 3852548
  have htrace : WordTrace (prefixWord ++ tailWord_3852548) baseStart_3852548 baseEnd_3852548 := by
    simpa [prefixWord, tailWord_3852548, baseEnd_3852548] using wordTrace_append hprefix tailTrace_3852548
  have hstable : (prefixWord ++ tailWord_3852548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852548).length < 2 ^ (prefixWord ++ tailWord_3852548).sum := by decide
  have hdescent : baseEnd_3852548 < baseStart_3852548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852593 : List Nat := [1, 2, 2, 3, 5, 1, 2, 6]
def baseStart_3852593 : Nat := 118140960795 + 3852593 * 2 ^ 59
def prefixEnd_3852593 : Nat := 4983230072969 + 3 ^ 40 * 3852593 * 2
def baseEnd_3852593 : Nat := 146535701862751884879241

theorem tailTrace_3852593 : CollatzResearch.WordTrace tailWord_3852593 prefixEnd_3852593 146535701862751884879241 := by
  unfold tailWord_3852593
  simp only [CollatzResearch.WordTrace]
  refine ⟨140515610531721006345802433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93677073687814004230534955 140515610531721006345802433)
  ·
    refine ⟨105386707898790754759351825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140515610531721006345802433 105386707898790754759351825)
    ·
      refine ⟨79040030924093066069513869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105386707898790754759351825 79040030924093066069513869)
      ·
        refine ⟨29640011596534899776067701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79040030924093066069513869 29640011596534899776067701)
        ·
          refine ⟨2778751087175146854006347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29640011596534899776067701 2778751087175146854006347)
          ·
            refine ⟨4168126630762720281009521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778751087175146854006347 4168126630762720281009521)
            ·
              refine ⟨3126094973072040210757141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168126630762720281009521 3126094973072040210757141)
              ·
                refine ⟨146535701862751884879241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3126094973072040210757141 146535701862751884879241)
                ·
                  rfl

theorem cell22_3852593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 6].length) (baseStart_3852593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852593 prefixEnd_3852593 := by exact prefixLift 3852593
  have htrace : WordTrace (prefixWord ++ tailWord_3852593) baseStart_3852593 baseEnd_3852593 := by
    simpa [prefixWord, tailWord_3852593, baseEnd_3852593] using wordTrace_append hprefix tailTrace_3852593
  have hstable : (prefixWord ++ tailWord_3852593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852593).length < 2 ^ (prefixWord ++ tailWord_3852593).sum := by decide
  have hdescent : baseEnd_3852593 < baseStart_3852593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852625 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 1, 3]
def baseStart_3852625 : Nat := 118140960795 + 3852625 * 2 ^ 59
def prefixEnd_3852625 : Nat := 4983230072969 + 3 ^ 40 * 3852625 * 2
def baseEnd_3852625 : Nat := 1318832271018729547113071

theorem tailTrace_3852625 : CollatzResearch.WordTrace tailWord_3852625 prefixEnd_3852625 1318832271018729547113071 := by
  unfold tailWord_3852625
  simp only [CollatzResearch.WordTrace]
  refine ⟨140516777667605075810967329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93677851778403383873978219 140516777667605075810967329)
  ·
    refine ⟨105387583250703806858225497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140516777667605075810967329 105387583250703806858225497)
    ·
      refine ⟨79040687438027855143669123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105387583250703806858225497 79040687438027855143669123)
      ·
        refine ⟨118561031157041782715503685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79040687438027855143669123 118561031157041782715503685)
        ·
          refine ⟨22230193341945334259156941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118561031157041782715503685 22230193341945334259156941)
          ·
            refine ⟨8336322503229500347183853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22230193341945334259156941 8336322503229500347183853)
            ·
              refine ⟨3126120938711062630193945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8336322503229500347183853 3126120938711062630193945)
              ·
                refine ⟨2344590704033296972645459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126120938711062630193945 2344590704033296972645459)
                ·
                  refine ⟨3516886056049945458968189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344590704033296972645459 3516886056049945458968189)
                  ·
                    refine ⟨1318832271018729547113071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516886056049945458968189 1318832271018729547113071)
                    ·
                      rfl

theorem cell22_3852625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_3852625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852625 prefixEnd_3852625 := by exact prefixLift 3852625
  have htrace : WordTrace (prefixWord ++ tailWord_3852625) baseStart_3852625 baseEnd_3852625 := by
    simpa [prefixWord, tailWord_3852625, baseEnd_3852625] using wordTrace_append hprefix tailTrace_3852625
  have hstable : (prefixWord ++ tailWord_3852625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852625).length < 2 ^ (prefixWord ++ tailWord_3852625).sum := by decide
  have hdescent : baseEnd_3852625 < baseStart_3852625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852634 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_3852634 : Nat := 118140960795 + 3852634 * 2 ^ 59
def prefixEnd_3852634 : Nat := 4983230072969 + 3 ^ 40 * 3852634 * 2
def baseEnd_3852634 : Nat := 1318835351902656523638043

theorem tailTrace_3852634 : CollatzResearch.WordTrace tailWord_3852634 prefixEnd_3852634 1318835351902656523638043 := by
  unfold tailWord_3852634
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129276481143117587011239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93678070616381646898696637 35129276481143117587011239)
  ·
    refine ⟨52693914721714676380516859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35129276481143117587011239 52693914721714676380516859)
    ·
      refine ⟨79040872082572014570775289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52693914721714676380516859 79040872082572014570775289)
      ·
        refine ⟨59280654061929010928081467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79040872082572014570775289 59280654061929010928081467)
        ·
          refine ⟨88920981092893516392122201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59280654061929010928081467 88920981092893516392122201)
          ·
            refine ⟨66690735819670137294091651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88920981092893516392122201 66690735819670137294091651)
            ·
              refine ⟨100036103729505205941137477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66690735819670137294091651 100036103729505205941137477)
              ·
                refine ⟨18756769449282226113963277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100036103729505205941137477 18756769449282226113963277)
                ·
                  refine ⟨7033788543480834792736229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18756769449282226113963277 7033788543480834792736229)
                  ·
                    refine ⟨1318835351902656523638043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033788543480834792736229 1318835351902656523638043)
                    ·
                      rfl

theorem cell22_3852634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_3852634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852634 prefixEnd_3852634 := by exact prefixLift 3852634
  have htrace : WordTrace (prefixWord ++ tailWord_3852634) baseStart_3852634 baseEnd_3852634 := by
    simpa [prefixWord, tailWord_3852634, baseEnd_3852634] using wordTrace_append hprefix tailTrace_3852634
  have hstable : (prefixWord ++ tailWord_3852634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852634).length < 2 ^ (prefixWord ++ tailWord_3852634).sum := by decide
  have hdescent : baseEnd_3852634 < baseStart_3852634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852683 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 4]
def baseStart_3852683 : Nat := 118140960795 + 3852683 * 2 ^ 59
def prefixEnd_3852683 : Nat := 4983230072969 + 3 ^ 40 * 3852683 * 2
def baseEnd_3852683 : Nat := 439617375201345576387631

theorem tailTrace_3852683 : CollatzResearch.WordTrace tailWord_3852683 prefixEnd_3852683 439617375201345576387631 := by
  unfold tailWord_3852683
  simp only [CollatzResearch.WordTrace]
  refine ⟨140518893101394951716578703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93679262067596634477719135 140518893101394951716578703)
  ·
    refine ⟨210778339652092427574868055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140518893101394951716578703 210778339652092427574868055)
    ·
      refine ⟨316167509478138641362302083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210778339652092427574868055 316167509478138641362302083)
      ·
        refine ⟨474251264217207962043453125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316167509478138641362302083 474251264217207962043453125)
        ·
          refine ⟨88922112040726492883147461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 474251264217207962043453125 88922112040726492883147461)
          ·
            refine ⟨16672896007636217415590149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88922112040726492883147461 16672896007636217415590149)
            ·
              refine ⟨3126168001431790765423153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16672896007636217415590149 3126168001431790765423153)
              ·
                refine ⟨2344626001073843074067365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126168001431790765423153 2344626001073843074067365)
                ·
                  refine ⟨439617375201345576387631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344626001073843074067365 439617375201345576387631)
                  ·
                    rfl

theorem cell22_3852683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 4].length) (baseStart_3852683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852683 prefixEnd_3852683 := by exact prefixLift 3852683
  have htrace : WordTrace (prefixWord ++ tailWord_3852683) baseStart_3852683 baseEnd_3852683 := by
    simpa [prefixWord, tailWord_3852683, baseEnd_3852683] using wordTrace_append hprefix tailTrace_3852683
  have hstable : (prefixWord ++ tailWord_3852683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852683).length < 2 ^ (prefixWord ++ tailWord_3852683).sum := by decide
  have hdescent : baseEnd_3852683 < baseStart_3852683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852698 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_3852698 : Nat := 118140960795 + 3852698 * 2 ^ 59
def prefixEnd_3852698 : Nat := 4983230072969 + 3 ^ 40 * 3852698 * 2
def baseEnd_3852698 : Nat := 1318857260410581690037847

theorem tailTrace_3852698 : CollatzResearch.WordTrace tailWord_3852698 prefixEnd_3852698 1318857260410581690037847 := by
  unfold tailWord_3852698
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129860049085152319593687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93679626797560406185583165 35129860049085152319593687)
  ·
    refine ⟨52694790073627728479390531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35129860049085152319593687 52694790073627728479390531)
    ·
      refine ⟨79042185110441592719085797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52694790073627728479390531 79042185110441592719085797)
      ·
        refine ⟨14820409708207798634828587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79042185110441592719085797 14820409708207798634828587)
        ·
          refine ⟨22230614562311697952242881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820409708207798634828587 22230614562311697952242881)
          ·
            refine ⟨16672960921733773464182161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22230614562311697952242881 16672960921733773464182161)
            ·
              refine ⟨12504720691300330098136621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16672960921733773464182161 12504720691300330098136621)
              ·
                refine ⟨4689270259237623786801233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12504720691300330098136621 4689270259237623786801233)
                ·
                  refine ⟨3516952694428217840100925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4689270259237623786801233 3516952694428217840100925)
                  ·
                    refine ⟨1318857260410581690037847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516952694428217840100925 1318857260410581690037847)
                    ·
                      rfl

theorem cell22_3852698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_3852698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852698 prefixEnd_3852698 := by exact prefixLift 3852698
  have htrace : WordTrace (prefixWord ++ tailWord_3852698) baseStart_3852698 baseEnd_3852698 := by
    simpa [prefixWord, tailWord_3852698, baseEnd_3852698] using wordTrace_append hprefix tailTrace_3852698
  have hstable : (prefixWord ++ tailWord_3852698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852698).length < 2 ^ (prefixWord ++ tailWord_3852698).sum := by decide
  have hdescent : baseEnd_3852698 < baseStart_3852698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852743 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 3, 3]
def baseStart_3852743 : Nat := 118140960795 + 3852743 * 2 ^ 59
def prefixEnd_3852743 : Nat := 4983230072969 + 3 ^ 40 * 3852743 * 2
def baseEnd_3852743 : Nat := 1318872664830216572662709

theorem tailTrace_3852743 : CollatzResearch.WordTrace tailWord_3852743 prefixEnd_3852743 1318872664830216572662709 := by
  unfold tailWord_3852743
  simp only [CollatzResearch.WordTrace]
  refine ⟨140521081481177581963762883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93680720987451721309175255 140521081481177581963762883)
  ·
    refine ⟨210781622221766372945644325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140521081481177581963762883 210781622221766372945644325)
    ·
      refine ⟨39521554166581194927308311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210781622221766372945644325 39521554166581194927308311)
      ·
        refine ⟨59282331249871792390962467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39521554166581194927308311 59282331249871792390962467)
        ·
          refine ⟨88923496874807688586443701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59282331249871792390962467 88923496874807688586443701)
          ·
            refine ⟨8336577832013220804979097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88923496874807688586443701 8336577832013220804979097)
            ·
              refine ⟨6252433374009915603734323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8336577832013220804979097 6252433374009915603734323)
              ·
                refine ⟨9378650061014873405601485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252433374009915603734323 9378650061014873405601485)
                ·
                  refine ⟨3516993772880577527100557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9378650061014873405601485 3516993772880577527100557)
                  ·
                    refine ⟨1318872664830216572662709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516993772880577527100557 1318872664830216572662709)
                    ·
                      rfl

theorem cell22_3852743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_3852743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852743 prefixEnd_3852743 := by exact prefixLift 3852743
  have htrace : WordTrace (prefixWord ++ tailWord_3852743) baseStart_3852743 baseEnd_3852743 := by
    simpa [prefixWord, tailWord_3852743, baseEnd_3852743] using wordTrace_append hprefix tailTrace_3852743
  have hstable : (prefixWord ++ tailWord_3852743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852743).length < 2 ^ (prefixWord ++ tailWord_3852743).sum := by decide
  have hdescent : baseEnd_3852743 < baseStart_3852743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852807 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 5]
def baseStart_3852807 : Nat := 118140960795 + 3852807 * 2 ^ 59
def prefixEnd_3852807 : Nat := 4983230072969 + 3 ^ 40 * 3852807 * 2
def baseEnd_3852807 : Nat := 439631524446047246354171

theorem tailTrace_3852807 : CollatzResearch.WordTrace tailWord_3852807 prefixEnd_3852807 439631524446047246354171 := by
  unfold tailWord_3852807
  simp only [CollatzResearch.WordTrace]
  refine ⟨140523415752945720894092675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93682277168630480596061783 140523415752945720894092675)
  ·
    refine ⟨210785123629418581341139013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140523415752945720894092675 210785123629418581341139013)
    ·
      refine ⟨39522210680515984001463565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210785123629418581341139013 39522210680515984001463565)
      ·
        refine ⟨14820829005193494000548837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39522210680515984001463565 14820829005193494000548837)
        ·
          refine ⟨2778905438473780125102907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14820829005193494000548837 2778905438473780125102907)
          ·
            refine ⟨4168358157710670187654361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778905438473780125102907 4168358157710670187654361)
            ·
              refine ⟨3126268618283002640740771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168358157710670187654361 3126268618283002640740771)
              ·
                refine ⟨4689402927424503961111157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126268618283002640740771 4689402927424503961111157)
                ·
                  refine ⟨439631524446047246354171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689402927424503961111157 439631524446047246354171)
                  ·
                    rfl

theorem cell22_3852807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 5].length) (baseStart_3852807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852807 prefixEnd_3852807 := by exact prefixLift 3852807
  have htrace : WordTrace (prefixWord ++ tailWord_3852807) baseStart_3852807 baseEnd_3852807 := by
    simpa [prefixWord, tailWord_3852807, baseEnd_3852807] using wordTrace_append hprefix tailTrace_3852807
  have hstable : (prefixWord ++ tailWord_3852807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852807).length < 2 ^ (prefixWord ++ tailWord_3852807).sum := by decide
  have hdescent : baseEnd_3852807 < baseStart_3852807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852820 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3852820 : Nat := 118140960795 + 3852820 * 2 ^ 59
def prefixEnd_3852820 : Nat := 4983230072969 + 3 ^ 40 * 3852820 * 2
def baseEnd_3852820 : Nat := 1318899023503814038487473

theorem tailTrace_3852820 : CollatzResearch.WordTrace tailWord_3852820 prefixEnd_3852820 1318899023503814038487473 := by
  unfold tailWord_3852820
  simp only [CollatzResearch.WordTrace]
  refine ⟨70261944950949312057157957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93682593267932416076210609 70261944950949312057157957)
  ·
    refine ⟨13174114678302996010717117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70261944950949312057157957 13174114678302996010717117)
    ·
      refine ⟨4940293004363623504018919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13174114678302996010717117 4940293004363623504018919)
      ·
        refine ⟨7410439506545435256028379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940293004363623504018919 7410439506545435256028379)
        ·
          refine ⟨11115659259818152884042569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410439506545435256028379 11115659259818152884042569)
          ·
            refine ⟨8336744444863614663031927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115659259818152884042569 8336744444863614663031927)
            ·
              refine ⟨12505116667295421994547891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336744444863614663031927 12505116667295421994547891)
              ·
                refine ⟨18757675000943132991821837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12505116667295421994547891 18757675000943132991821837)
                ·
                  refine ⟨7034128125353674871933189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18757675000943132991821837 7034128125353674871933189)
                  ·
                    refine ⟨1318899023503814038487473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034128125353674871933189 1318899023503814038487473)
                    ·
                      rfl

theorem cell22_3852820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3852820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852820 prefixEnd_3852820 := by exact prefixLift 3852820
  have htrace : WordTrace (prefixWord ++ tailWord_3852820) baseStart_3852820 baseEnd_3852820 := by
    simpa [prefixWord, tailWord_3852820, baseEnd_3852820] using wordTrace_append hprefix tailTrace_3852820
  have hstable : (prefixWord ++ tailWord_3852820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852820).length < 2 ^ (prefixWord ++ tailWord_3852820).sum := by decide
  have hdescent : baseEnd_3852820 < baseStart_3852820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852845 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3852845 : Nat := 118140960795 + 3852845 * 2 ^ 59
def prefixEnd_3852845 : Nat := 4983230072969 + 3 ^ 40 * 3852845 * 2
def baseEnd_3852845 : Nat := 1318907581514722306612397

theorem tailTrace_3852845 : CollatzResearch.WordTrace tailWord_3852845 prefixEnd_3852845 1318907581514722306612397 := by
  unfold tailWord_3852845
  simp only [CollatzResearch.WordTrace]
  refine ⟨140524801726808053383975989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93683201151205368922650659 140524801726808053383975989)
  ·
    refine ⟨13174200161888255004747749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140524801726808053383975989 13174200161888255004747749)
    ·
      refine ⟨2470162530354047813390203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13174200161888255004747749 2470162530354047813390203)
      ·
        refine ⟨3705243795531071720085305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470162530354047813390203 3705243795531071720085305)
        ·
          refine ⟨2778932846648303790063979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3705243795531071720085305 2778932846648303790063979)
          ·
            refine ⟨4168399269972455685095969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778932846648303790063979 4168399269972455685095969)
            ·
              refine ⟨3126299452479341763821977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168399269972455685095969 3126299452479341763821977)
              ·
                refine ⟨2344724589359506322866483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126299452479341763821977 2344724589359506322866483)
                ·
                  refine ⟨3517086884039259484299725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344724589359506322866483 3517086884039259484299725)
                  ·
                    refine ⟨1318907581514722306612397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517086884039259484299725 1318907581514722306612397)
                    ·
                      rfl

theorem cell22_3852845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3852845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852845 prefixEnd_3852845 := by exact prefixLift 3852845
  have htrace : WordTrace (prefixWord ++ tailWord_3852845) baseStart_3852845 baseEnd_3852845 := by
    simpa [prefixWord, tailWord_3852845, baseEnd_3852845] using wordTrace_append hprefix tailTrace_3852845
  have hstable : (prefixWord ++ tailWord_3852845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852845).length < 2 ^ (prefixWord ++ tailWord_3852845).sum := by decide
  have hdescent : baseEnd_3852845 < baseStart_3852845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852846 : List Nat := [4, 1, 3, 1, 13]
def baseStart_3852846 : Nat := 118140960795 + 3852846 * 2 ^ 59
def prefixEnd_3852846 : Nat := 4983230072969 + 3 ^ 40 * 3852846 * 2
def baseEnd_3852846 : Nat := 5427604624836043775051

theorem tailTrace_3852846 : CollatzResearch.WordTrace tailWord_3852846 prefixEnd_3852846 5427604624836043775051 := by
  unfold tailWord_3852846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565604774975553819345299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93683225466536287036508261 17565604774975553819345299)
  ·
    refine ⟨26348407162463330729017949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17565604774975553819345299 26348407162463330729017949)
    ·
      refine ⟨9880652685923749023381731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26348407162463330729017949 9880652685923749023381731)
      ·
        refine ⟨14820979028885623535072597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880652685923749023381731 14820979028885623535072597)
        ·
          refine ⟨5427604624836043775051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14820979028885623535072597 5427604624836043775051)
          ·
            rfl

theorem cell22_3852846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 13].length) (baseStart_3852846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852846 prefixEnd_3852846 := by exact prefixLift 3852846
  have htrace : WordTrace (prefixWord ++ tailWord_3852846) baseStart_3852846 baseEnd_3852846 := by
    simpa [prefixWord, tailWord_3852846, baseEnd_3852846] using wordTrace_append hprefix tailTrace_3852846
  have hstable : (prefixWord ++ tailWord_3852846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852846).length < 2 ^ (prefixWord ++ tailWord_3852846).sum := by decide
  have hdescent : baseEnd_3852846 < baseStart_3852846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852876 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_3852876 : Nat := 118140960795 + 3852876 * 2 ^ 59
def prefixEnd_3852876 : Nat := 4983230072969 + 3 ^ 40 * 3852876 * 2
def baseEnd_3852876 : Nat := 1318918193448248559087301

theorem tailTrace_3852876 : CollatzResearch.WordTrace tailWord_3852876 prefixEnd_3852876 1318918193448248559087301 := by
  unfold tailWord_3852876
  simp only [CollatzResearch.WordTrace]
  refine ⟨70262966194847872839177241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93683954926463830452236321 70262966194847872839177241)
  ·
    refine ⟨52697224646135904629382931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70262966194847872839177241 52697224646135904629382931)
    ·
      refine ⟨79045836969203856944074397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52697224646135904629382931 79045836969203856944074397)
      ·
        refine ⟨29642188863451446354027899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79045836969203856944074397 29642188863451446354027899)
        ·
          refine ⟨44463283295177169531041849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29642188863451446354027899 44463283295177169531041849)
          ·
            refine ⟨33347462471382877148281387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44463283295177169531041849 33347462471382877148281387)
            ·
              refine ⟨50021193707074315722422081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33347462471382877148281387 50021193707074315722422081)
              ·
                refine ⟨37515895280305736791816561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50021193707074315722422081 37515895280305736791816561)
                ·
                  refine ⟨28136921460229302593862421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37515895280305736791816561 28136921460229302593862421)
                  ·
                    refine ⟨1318918193448248559087301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28136921460229302593862421 1318918193448248559087301)
                    ·
                      rfl

theorem cell22_3852876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_3852876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852876 prefixEnd_3852876 := by exact prefixLift 3852876
  have htrace : WordTrace (prefixWord ++ tailWord_3852876) baseStart_3852876 baseEnd_3852876 := by
    simpa [prefixWord, tailWord_3852876, baseEnd_3852876] using wordTrace_append hprefix tailTrace_3852876
  have hstable : (prefixWord ++ tailWord_3852876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852876).length < 2 ^ (prefixWord ++ tailWord_3852876).sum := by decide
  have hdescent : baseEnd_3852876 < baseStart_3852876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852878 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_3852878 : Nat := 118140960795 + 3852878 * 2 ^ 59
def prefixEnd_3852878 : Nat := 4983230072969 + 3 ^ 40 * 3852878 * 2
def baseEnd_3852878 : Nat := 1318918878089121220537295

theorem tailTrace_3852878 : CollatzResearch.WordTrace tailWord_3852878 prefixEnd_3852878 1318918878089121220537295 := by
  unfold tailWord_3852878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565750666961062502490911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93684003557125666679951525 17565750666961062502490911)
  ·
    refine ⟨26348626000441593753736367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17565750666961062502490911 26348626000441593753736367)
    ·
      refine ⟨39522939000662390630604551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26348626000441593753736367 39522939000662390630604551)
      ·
        refine ⟨59284408500993585945906827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39522939000662390630604551 59284408500993585945906827)
        ·
          refine ⟨88926612751490378918860241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59284408500993585945906827 88926612751490378918860241)
          ·
            refine ⟨66694959563617784189145181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88926612751490378918860241 66694959563617784189145181)
            ·
              refine ⟨25010609836356669070929443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66694959563617784189145181 25010609836356669070929443)
              ·
                refine ⟨37515914754535003606394165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25010609836356669070929443 37515914754535003606394165)
                ·
                  refine ⟨3517117008237656588099453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37515914754535003606394165 3517117008237656588099453)
                  ·
                    refine ⟨1318918878089121220537295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517117008237656588099453 1318918878089121220537295)
                    ·
                      rfl

theorem cell22_3852878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_3852878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852878 prefixEnd_3852878 := by exact prefixLift 3852878
  have htrace : WordTrace (prefixWord ++ tailWord_3852878) baseStart_3852878 baseEnd_3852878 := by
    simpa [prefixWord, tailWord_3852878, baseEnd_3852878] using wordTrace_append hprefix tailTrace_3852878
  have hstable : (prefixWord ++ tailWord_3852878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852878).length < 2 ^ (prefixWord ++ tailWord_3852878).sum := by decide
  have hdescent : baseEnd_3852878 < baseStart_3852878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852908 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_3852908 : Nat := 118140960795 + 3852908 * 2 ^ 59
def prefixEnd_3852908 : Nat := 4983230072969 + 3 ^ 40 * 3852908 * 2
def baseEnd_3852908 : Nat := 439643049234070380762401

theorem tailTrace_3852908 : CollatzResearch.WordTrace tailWord_3852908 prefixEnd_3852908 439643049234070380762401 := by
  unfold tailWord_3852908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70263549762789907571759689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93684733017053210095679585 70263549762789907571759689)
  ·
    refine ⟨52697662322092430678819767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70263549762789907571759689 52697662322092430678819767)
    ·
      refine ⟨79046493483138646018229651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52697662322092430678819767 79046493483138646018229651)
      ·
        refine ⟨118569740224707969027344477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79046493483138646018229651 118569740224707969027344477)
        ·
          refine ⟨44463652584265488385254179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118569740224707969027344477 44463652584265488385254179)
          ·
            refine ⟨66695478876398232577881269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44463652584265488385254179 66695478876398232577881269)
            ·
              refine ⟨6252701144662334304176369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66695478876398232577881269 6252701144662334304176369)
              ·
                refine ⟨4689525858496750728132277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6252701144662334304176369 4689525858496750728132277)
                ·
                  refine ⟨439643049234070380762401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689525858496750728132277 439643049234070380762401)
                  ·
                    rfl

theorem cell22_3852908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_3852908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3852908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3852908 prefixEnd_3852908 := by exact prefixLift 3852908
  have htrace : WordTrace (prefixWord ++ tailWord_3852908) baseStart_3852908 baseEnd_3852908 := by
    simpa [prefixWord, tailWord_3852908, baseEnd_3852908] using wordTrace_append hprefix tailTrace_3852908
  have hstable : (prefixWord ++ tailWord_3852908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852908).length < 2 ^ (prefixWord ++ tailWord_3852908).sum := by decide
  have hdescent : baseEnd_3852908 < baseStart_3852908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853000 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_3853000 : Nat := 118140960795 + 3853000 * 2 ^ 59
def prefixEnd_3853000 : Nat := 4983230072969 + 3 ^ 40 * 3853000 * 2
def baseEnd_3853000 : Nat := 1318960641182353568986921

theorem tailTrace_3853000 : CollatzResearch.WordTrace tailWord_3853000 prefixEnd_3853000 1318960641182353568986921 := by
  unfold tailWord_3853000
  simp only [CollatzResearch.WordTrace]
  refine ⟨70265227520623257427934227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93686970027497676570578969 70265227520623257427934227)
  ·
    refine ⟨105397841280934886141901341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70265227520623257427934227 105397841280934886141901341)
    ·
      refine ⟨39524190480350582303213003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105397841280934886141901341 39524190480350582303213003)
      ·
        refine ⟨59286285720525873454819505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39524190480350582303213003 59286285720525873454819505)
        ·
          refine ⟨44464714290394405091114629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59286285720525873454819505 44464714290394405091114629)
          ·
            refine ⟨8337133929448950954583993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44464714290394405091114629 8337133929448950954583993)
            ·
              refine ⟨6252850447086713215937995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337133929448950954583993 6252850447086713215937995)
              ·
                refine ⟨9379275670630069823906993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252850447086713215937995 9379275670630069823906993)
                ·
                  refine ⟨7034456752972552367930245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9379275670630069823906993 7034456752972552367930245)
                  ·
                    refine ⟨1318960641182353568986921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034456752972552367930245 1318960641182353568986921)
                    ·
                      rfl

theorem cell22_3853000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_3853000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853000 prefixEnd_3853000 := by exact prefixLift 3853000
  have htrace : WordTrace (prefixWord ++ tailWord_3853000) baseStart_3853000 baseEnd_3853000 := by
    simpa [prefixWord, tailWord_3853000, baseEnd_3853000] using wordTrace_append hprefix tailTrace_3853000
  have hstable : (prefixWord ++ tailWord_3853000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853000).length < 2 ^ (prefixWord ++ tailWord_3853000).sum := by decide
  have hdescent : baseEnd_3853000 < baseStart_3853000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853028 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3853028 : Nat := 118140960795 + 3853028 * 2 ^ 59
def prefixEnd_3853028 : Nat := 4983230072969 + 3 ^ 40 * 3853028 * 2
def baseEnd_3853028 : Nat := 1318970226154570829286835

theorem tailTrace_3853028 : CollatzResearch.WordTrace tailWord_3853028 prefixEnd_3853028 1318970226154570829286835 := by
  unfold tailWord_3853028
  simp only [CollatzResearch.WordTrace]
  refine ⟨70265738142572537818943869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93687650856763383758591825 70265738142572537818943869)
  ·
    refine ⟨26349651803464701682103951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70265738142572537818943869 26349651803464701682103951)
    ·
      refine ⟨39524477705197052523155927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26349651803464701682103951 39524477705197052523155927)
      ·
        refine ⟨59286716557795578784733891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39524477705197052523155927 59286716557795578784733891)
        ·
          refine ⟨88930074836693368177100837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59286716557795578784733891 88930074836693368177100837)
          ·
            refine ⟨16674389031880006533206407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88930074836693368177100837 16674389031880006533206407)
            ·
              refine ⟨25011583547820009799809611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16674389031880006533206407 25011583547820009799809611)
              ·
                refine ⟨37517375321730014699714417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25011583547820009799809611 37517375321730014699714417)
                ·
                  refine ⟨28138031491297511024785813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37517375321730014699714417 28138031491297511024785813)
                  ·
                    refine ⟨1318970226154570829286835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28138031491297511024785813 1318970226154570829286835)
                    ·
                      rfl

theorem cell22_3853028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3853028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853028 prefixEnd_3853028 := by exact prefixLift 3853028
  have htrace : WordTrace (prefixWord ++ tailWord_3853028) baseStart_3853028 baseEnd_3853028 := by
    simpa [prefixWord, tailWord_3853028, baseEnd_3853028] using wordTrace_append hprefix tailTrace_3853028
  have hstable : (prefixWord ++ tailWord_3853028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853028).length < 2 ^ (prefixWord ++ tailWord_3853028).sum := by decide
  have hdescent : baseEnd_3853028 < baseStart_3853028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853032 : List Nat := [2, 1, 4, 1, 5, 1, 1, 7]
def baseStart_3853032 : Nat := 118140960795 + 3853032 * 2 ^ 59
def prefixEnd_3853032 : Nat := 4983230072969 + 3 ^ 40 * 3853032 * 2
def baseEnd_3853032 : Nat := 146552399492924016909647

theorem tailTrace_3853032 : CollatzResearch.WordTrace tailWord_3853032 prefixEnd_3853032 146552399492924016909647 := by
  unfold tailWord_3853032
  simp only [CollatzResearch.WordTrace]
  refine ⟨70265811088565292160516675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93687748118087056214022233 70265811088565292160516675)
  ·
    refine ⟨105398716632847938240775013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70265811088565292160516675 105398716632847938240775013)
    ·
      refine ⟨19762259368658988420145315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105398716632847938240775013 19762259368658988420145315)
      ·
        refine ⟨29643389052988482630217973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19762259368658988420145315 29643389052988482630217973)
        ·
          refine ⟨2779067723717670246582935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29643389052988482630217973 2779067723717670246582935)
          ·
            refine ⟨4168601585576505369874403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779067723717670246582935 4168601585576505369874403)
            ·
              refine ⟨6252902378364758054811605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168601585576505369874403 6252902378364758054811605)
              ·
                refine ⟨146552399492924016909647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6252902378364758054811605 146552399492924016909647)
                ·
                  rfl

theorem cell22_3853032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_3853032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853032 prefixEnd_3853032 := by exact prefixLift 3853032
  have htrace : WordTrace (prefixWord ++ tailWord_3853032) baseStart_3853032 baseEnd_3853032 := by
    simpa [prefixWord, tailWord_3853032, baseEnd_3853032] using wordTrace_append hprefix tailTrace_3853032
  have hstable : (prefixWord ++ tailWord_3853032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853032).length < 2 ^ (prefixWord ++ tailWord_3853032).sum := by decide
  have hdescent : baseEnd_3853032 < baseStart_3853032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853064 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 1, 3]
def baseStart_3853064 : Nat := 118140960795 + 3853064 * 2 ^ 59
def prefixEnd_3853064 : Nat := 4983230072969 + 3 ^ 40 * 3853064 * 2
def baseEnd_3853064 : Nat := 1318982549690278735386725

theorem tailTrace_3853064 : CollatzResearch.WordTrace tailWord_3853064 prefixEnd_3853064 1318982549690278735386725 := by
  unfold tailWord_3853064
  simp only [CollatzResearch.WordTrace]
  refine ⟨70266394656507326893099123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93688526208676435857465497 70266394656507326893099123)
  ·
    refine ⟨105399591984760990339648685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70266394656507326893099123 105399591984760990339648685)
    ·
      refine ⟨39524846994285371377368257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105399591984760990339648685 39524846994285371377368257)
      ·
        refine ⟨29643635245714028533026193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39524846994285371377368257 29643635245714028533026193)
        ·
          refine ⟨22232726434285521399769645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29643635245714028533026193 22232726434285521399769645)
          ·
            refine ⟨8337272412857070524913617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22232726434285521399769645 8337272412857070524913617)
            ·
              refine ⟨6252954309642802893685213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337272412857070524913617 6252954309642802893685213)
              ·
                refine ⟨2344857866116051085131955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252954309642802893685213 2344857866116051085131955)
                ·
                  refine ⟨3517286799174076627697933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344857866116051085131955 3517286799174076627697933)
                  ·
                    refine ⟨1318982549690278735386725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517286799174076627697933 1318982549690278735386725)
                    ·
                      rfl

theorem cell22_3853064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_3853064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853064 prefixEnd_3853064 := by exact prefixLift 3853064
  have htrace : WordTrace (prefixWord ++ tailWord_3853064) baseStart_3853064 baseEnd_3853064 := by
    simpa [prefixWord, tailWord_3853064, baseEnd_3853064] using wordTrace_append hprefix tailTrace_3853064
  have hstable : (prefixWord ++ tailWord_3853064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853064).length < 2 ^ (prefixWord ++ tailWord_3853064).sum := by decide
  have hdescent : baseEnd_3853064 < baseStart_3853064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853107 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 1, 4]
def baseStart_3853107 : Nat := 118140960795 + 3853107 * 2 ^ 59
def prefixEnd_3853107 : Nat := 4983230072969 + 3 ^ 40 * 3853107 * 2
def baseEnd_3853107 : Nat := 1318997269469040956561593

theorem tailTrace_3853107 : CollatzResearch.WordTrace tailWord_3853107 prefixEnd_3853107 1318997269469040956561593 := by
  unfold tailWord_3853107
  simp only [CollatzResearch.WordTrace]
  refine ⟨140534357651858872130013575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93689571767905914753342383 140534357651858872130013575)
  ·
    refine ⟨210801536477788308195020363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140534357651858872130013575 210801536477788308195020363)
    ·
      refine ⟨316202304716682462292530545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210801536477788308195020363 316202304716682462292530545)
      ·
        refine ⟨237151728537511846719397909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316202304716682462292530545 237151728537511846719397909)
        ·
          refine ⟨11116487275195867814971777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237151728537511846719397909 11116487275195867814971777)
          ·
            refine ⟨8337365456396900861228833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11116487275195867814971777 8337365456396900861228833)
            ·
              refine ⟨6253024092297675645921625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337365456396900861228833 6253024092297675645921625)
              ·
                refine ⟨4689768069223256734441219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253024092297675645921625 4689768069223256734441219)
                ·
                  refine ⟨7034652103834885101661829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689768069223256734441219 7034652103834885101661829)
                  ·
                    refine ⟨1318997269469040956561593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034652103834885101661829 1318997269469040956561593)
                    ·
                      rfl

theorem cell22_3853107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 4].length) (baseStart_3853107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853107 prefixEnd_3853107 := by exact prefixLift 3853107
  have htrace : WordTrace (prefixWord ++ tailWord_3853107) baseStart_3853107 baseEnd_3853107 := by
    simpa [prefixWord, tailWord_3853107, baseEnd_3853107] using wordTrace_append hprefix tailTrace_3853107
  have hstable : (prefixWord ++ tailWord_3853107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853107).length < 2 ^ (prefixWord ++ tailWord_3853107).sum := by decide
  have hdescent : baseEnd_3853107 < baseStart_3853107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853195 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 5]
def baseStart_3853195 : Nat := 118140960795 + 3853195 * 2 ^ 59
def prefixEnd_3853195 : Nat := 4983230072969 + 3 ^ 40 * 3853195 * 2
def baseEnd_3853195 : Nat := 439675797889146020120441

theorem tailTrace_3853195 : CollatzResearch.WordTrace tailWord_3853195 prefixEnd_3853195 439675797889146020120441 := by
  unfold tailWord_3853195
  simp only [CollatzResearch.WordTrace]
  refine ⟨140537567275540063159217039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93691711517026708772811359 140537567275540063159217039)
  ·
    refine ⟨210806350913310094738825559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140537567275540063159217039 210806350913310094738825559)
    ·
      refine ⟨316209526369965142108238339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210806350913310094738825559 316209526369965142108238339)
      ·
        refine ⟨474314289554947713162357509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316209526369965142108238339 474314289554947713162357509)
        ·
          refine ⟨88933929291552696217942033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 474314289554947713162357509 88933929291552696217942033)
          ·
            refine ⟨66700446968664522163456525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88933929291552696217942033 66700446968664522163456525)
            ·
              refine ⟨25012667613249195811296197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66700446968664522163456525 25012667613249195811296197)
              ·
                refine ⟨4689875177484224214618037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25012667613249195811296197 4689875177484224214618037)
                ·
                  refine ⟨439675797889146020120441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689875177484224214618037 439675797889146020120441)
                  ·
                    rfl

theorem cell22_3853195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 5].length) (baseStart_3853195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853195 prefixEnd_3853195 := by exact prefixLift 3853195
  have htrace : WordTrace (prefixWord ++ tailWord_3853195) baseStart_3853195 baseEnd_3853195 := by
    simpa [prefixWord, tailWord_3853195, baseEnd_3853195] using wordTrace_append hprefix tailTrace_3853195
  have hstable : (prefixWord ++ tailWord_3853195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853195).length < 2 ^ (prefixWord ++ tailWord_3853195).sum := by decide
  have hdescent : baseEnd_3853195 < baseStart_3853195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853225 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_3853225 : Nat := 118140960795 + 3853225 * 2 ^ 59
def prefixEnd_3853225 : Nat := 4983230072969 + 3 ^ 40 * 3853225 * 2
def baseEnd_3853225 : Nat := 1319037663280527982111231

theorem tailTrace_3853225 : CollatzResearch.WordTrace tailWord_3853225 prefixEnd_3853225 1319037663280527982111231 := by
  unfold tailWord_3853225
  simp only [CollatzResearch.WordTrace]
  refine ⟨140538661465431378282809129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93692440976954252188539419 140538661465431378282809129)
  ·
    refine ⟨105403996099073533712106847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140538661465431378282809129 105403996099073533712106847)
    ·
      refine ⟨158105994148610300568160271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105403996099073533712106847 158105994148610300568160271)
      ·
        refine ⟨237158991222915450852240407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158105994148610300568160271 237158991222915450852240407)
        ·
          refine ⟨355738486834373176278360611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237158991222915450852240407 355738486834373176278360611)
          ·
            refine ⟨533607730251559764417540917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355738486834373176278360611 533607730251559764417540917)
            ·
              refine ⟨50025724711083727914144461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533607730251559764417540917 50025724711083727914144461)
              ·
                refine ⟨18759646766656397967804173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50025724711083727914144461 18759646766656397967804173)
                ·
                  refine ⟨7034867537496149237926565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18759646766656397967804173 7034867537496149237926565)
                  ·
                    refine ⟨1319037663280527982111231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034867537496149237926565 1319037663280527982111231)
                    ·
                      rfl

theorem cell22_3853225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_3853225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853225 prefixEnd_3853225 := by exact prefixLift 3853225
  have htrace : WordTrace (prefixWord ++ tailWord_3853225) baseStart_3853225 baseEnd_3853225 := by
    simpa [prefixWord, tailWord_3853225, baseEnd_3853225] using wordTrace_append hprefix tailTrace_3853225
  have hstable : (prefixWord ++ tailWord_3853225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853225).length < 2 ^ (prefixWord ++ tailWord_3853225).sum := by decide
  have hdescent : baseEnd_3853225 < baseStart_3853225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853242 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_3853242 : Nat := 118140960795 + 3853242 * 2 ^ 59
def prefixEnd_3853242 : Nat := 4983230072969 + 3 ^ 40 * 3853242 * 2
def baseEnd_3853242 : Nat := 1319043482727945604436179

theorem tailTrace_3853242 : CollatzResearch.WordTrace tailWord_3853242 prefixEnd_3853242 1319043482727945604436179 := by
  unfold tailWord_3853242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35134820376592447546544495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93692854337579860124118653 35134820376592447546544495)
  ·
    refine ⟨52702230564888671319816743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35134820376592447546544495 52702230564888671319816743)
    ·
      refine ⟨79053345847333006979725115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52702230564888671319816743 79053345847333006979725115)
      ·
        refine ⟨118580018770999510469587673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79053345847333006979725115 118580018770999510469587673)
        ·
          refine ⟨88935014078249632852190755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118580018770999510469587673 88935014078249632852190755)
          ·
            refine ⟨133402521117374449278286133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88935014078249632852190755 133402521117374449278286133)
            ·
              refine ⟨12506486354753854619839325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133402521117374449278286133 12506486354753854619839325)
              ·
                refine ⟨4689932383032695482439747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12506486354753854619839325 4689932383032695482439747)
                ·
                  refine ⟨7034898574549043223659621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689932383032695482439747 7034898574549043223659621)
                  ·
                    refine ⟨1319043482727945604436179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034898574549043223659621 1319043482727945604436179)
                    ·
                      rfl

theorem cell22_3853242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_3853242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853242 prefixEnd_3853242 := by exact prefixLift 3853242
  have htrace : WordTrace (prefixWord ++ tailWord_3853242) baseStart_3853242 baseEnd_3853242 := by
    simpa [prefixWord, tailWord_3853242, baseEnd_3853242] using wordTrace_append hprefix tailTrace_3853242
  have hstable : (prefixWord ++ tailWord_3853242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853242).length < 2 ^ (prefixWord ++ tailWord_3853242).sum := by decide
  have hdescent : baseEnd_3853242 < baseStart_3853242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853255 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3853255 : Nat := 118140960795 + 3853255 * 2 ^ 59
def prefixEnd_3853255 : Nat := 4983230072969 + 3 ^ 40 * 3853255 * 2
def baseEnd_3853255 : Nat := 1319047932893617903861139

theorem tailTrace_3853255 : CollatzResearch.WordTrace tailWord_3853255 prefixEnd_3853255 1319047932893617903861139 := by
  unfold tailWord_3853255
  simp only [CollatzResearch.WordTrace]
  refine ⟨140539755655322693406401219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93693170436881795604267479 140539755655322693406401219)
  ·
    refine ⟨210809633482984040109601829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140539755655322693406401219 210809633482984040109601829)
    ·
      refine ⟨39526806278059507520550343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210809633482984040109601829 39526806278059507520550343)
      ·
        refine ⟨59290209417089261280825515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39526806278059507520550343 59290209417089261280825515)
        ·
          refine ⟨88935314125633891921238273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59290209417089261280825515 88935314125633891921238273)
          ·
            refine ⟨66701485594225418940928705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88935314125633891921238273 66701485594225418940928705)
            ·
              refine ⟨50026114195669064205696529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66701485594225418940928705 50026114195669064205696529)
              ·
                refine ⟨37519585646751798154272397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50026114195669064205696529 37519585646751798154272397)
                ·
                  refine ⟨14069844617531924307852149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37519585646751798154272397 14069844617531924307852149)
                  ·
                    refine ⟨1319047932893617903861139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14069844617531924307852149 1319047932893617903861139)
                    ·
                      rfl

theorem cell22_3853255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3853255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853255 prefixEnd_3853255 := by exact prefixLift 3853255
  have htrace : WordTrace (prefixWord ++ tailWord_3853255) baseStart_3853255 baseEnd_3853255 := by
    simpa [prefixWord, tailWord_3853255, baseEnd_3853255] using wordTrace_append hprefix tailTrace_3853255
  have hstable : (prefixWord ++ tailWord_3853255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853255).length < 2 ^ (prefixWord ++ tailWord_3853255).sum := by decide
  have hdescent : baseEnd_3853255 < baseStart_3853255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853272 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_3853272 : Nat := 118140960795 + 3853272 * 2 ^ 59
def prefixEnd_3853272 : Nat := 4983230072969 + 3 ^ 40 * 3853272 * 2
def baseEnd_3853272 : Nat := 1319053752341035526186087

theorem tailTrace_3853272 : CollatzResearch.WordTrace tailWord_3853272 prefixEnd_3853272 1319053752341035526186087 := by
  unfold tailWord_3853272
  simp only [CollatzResearch.WordTrace]
  refine ⟨70270187848130552654885035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93693583797507403539846713 70270187848130552654885035)
  ·
    refine ⟨105405281772195828982327553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70270187848130552654885035 105405281772195828982327553)
    ·
      refine ⟨79053961329146871736745665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105405281772195828982327553 79053961329146871736745665)
      ·
        refine ⟨59290470996860153802559249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79053961329146871736745665 59290470996860153802559249)
        ·
          refine ⟨44467853247645115351919437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59290470996860153802559249 44467853247645115351919437)
          ·
            refine ⟨16675444967866918256969789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44467853247645115351919437 16675444967866918256969789)
            ·
              refine ⟨6253291862950094346363671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16675444967866918256969789 6253291862950094346363671)
              ·
                refine ⟨9379937794425141519545507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253291862950094346363671 9379937794425141519545507)
                ·
                  refine ⟨14069906691637712279318261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9379937794425141519545507 14069906691637712279318261)
                  ·
                    refine ⟨1319053752341035526186087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14069906691637712279318261 1319053752341035526186087)
                    ·
                      rfl

theorem cell22_3853272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_3853272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853272 prefixEnd_3853272 := by exact prefixLift 3853272
  have htrace : WordTrace (prefixWord ++ tailWord_3853272) baseStart_3853272 baseEnd_3853272 := by
    simpa [prefixWord, tailWord_3853272, baseEnd_3853272] using wordTrace_append hprefix tailTrace_3853272
  have hstable : (prefixWord ++ tailWord_3853272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853272).length < 2 ^ (prefixWord ++ tailWord_3853272).sum := by decide
  have hdescent : baseEnd_3853272 < baseStart_3853272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853287 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3853287 : Nat := 118140960795 + 3853287 * 2 ^ 59
def prefixEnd_3853287 : Nat := 4983230072969 + 3 ^ 40 * 3853287 * 2
def baseEnd_3853287 : Nat := 1319058887147580487061041

theorem tailTrace_3853287 : CollatzResearch.WordTrace tailWord_3853287 prefixEnd_3853287 1319058887147580487061041 := by
  unfold tailWord_3853287
  simp only [CollatzResearch.WordTrace]
  refine ⟨140540922791206762871566115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93693948527471175247710743 140540922791206762871566115)
  ·
    refine ⟨210811384186810144307349173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140540922791206762871566115 210811384186810144307349173)
    ·
      refine ⟨19763567267513451028813985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210811384186810144307349173 19763567267513451028813985)
      ·
        refine ⟨14822675450635088271610489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19763567267513451028813985 14822675450635088271610489)
        ·
          refine ⟨11117006587976316203707867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14822675450635088271610489 11117006587976316203707867)
          ·
            refine ⟨16675509881964474305561801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117006587976316203707867 16675509881964474305561801)
            ·
              refine ⟨12506632411473355729171351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16675509881964474305561801 12506632411473355729171351)
              ·
                refine ⟨18759948617210033593757027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506632411473355729171351 18759948617210033593757027)
                ·
                  refine ⟨28139922925815050390635541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18759948617210033593757027 28139922925815050390635541)
                  ·
                    refine ⟨1319058887147580487061041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28139922925815050390635541 1319058887147580487061041)
                    ·
                      rfl

theorem cell22_3853287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3853287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853287 prefixEnd_3853287 := by exact prefixLift 3853287
  have htrace : WordTrace (prefixWord ++ tailWord_3853287) baseStart_3853287 baseEnd_3853287 := by
    simpa [prefixWord, tailWord_3853287, baseEnd_3853287] using wordTrace_append hprefix tailTrace_3853287
  have hstable : (prefixWord ++ tailWord_3853287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853287).length < 2 ^ (prefixWord ++ tailWord_3853287).sum := by decide
  have hdescent : baseEnd_3853287 < baseStart_3853287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853302 : List Nat := [5, 1, 1, 1, 3, 1, 10]
def baseStart_3853302 : Nat := 118140960795 + 3853302 * 2 ^ 59
def prefixEnd_3853302 : Nat := 4983230072969 + 3 ^ 40 * 3853302 * 2
def baseEnd_3853302 : Nat := 48854223035337979553185

theorem tailTrace_3853302 : CollatzResearch.WordTrace tailWord_3853302 prefixEnd_3853302 48854223035337979553185 := by
  unfold tailWord_3853302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783841867884526277085135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93694313257434946955574773 8783841867884526277085135)
  ·
    refine ⟨13175762801826789415627703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783841867884526277085135 13175762801826789415627703)
    ·
      refine ⟨19763644202740184123441555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175762801826789415627703 19763644202740184123441555)
      ·
        refine ⟨29645466304110276185162333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19763644202740184123441555 29645466304110276185162333)
        ·
          refine ⟨11117049864041353569435875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29645466304110276185162333 11117049864041353569435875)
          ·
            refine ⟨16675574796062030354153813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117049864041353569435875 16675574796062030354153813)
            ·
              refine ⟨48854223035337979553185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16675574796062030354153813 48854223035337979553185)
              ·
                rfl

theorem cell22_3853302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 10].length) (baseStart_3853302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853302 prefixEnd_3853302 := by exact prefixLift 3853302
  have htrace : WordTrace (prefixWord ++ tailWord_3853302) baseStart_3853302 baseEnd_3853302 := by
    simpa [prefixWord, tailWord_3853302, baseEnd_3853302] using wordTrace_append hprefix tailTrace_3853302
  have hstable : (prefixWord ++ tailWord_3853302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853302).length < 2 ^ (prefixWord ++ tailWord_3853302).sum := by decide
  have hdescent : baseEnd_3853302 < baseStart_3853302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853362 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_3853362 : Nat := 118140960795 + 3853362 * 2 ^ 59
def prefixEnd_3853362 : Nat := 4983230072969 + 3 ^ 40 * 3853362 * 2
def baseEnd_3853362 : Nat := 1319084561180305291435811

theorem tailTrace_3853362 : CollatzResearch.WordTrace tailWord_3853362 prefixEnd_3853362 1319084561180305291435811 := by
  unfold tailWord_3853362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35135914566483762670136585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93695772177290033787030893 35135914566483762670136585)
  ·
    refine ⟨26351935924862822002602439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35135914566483762670136585 26351935924862822002602439)
    ·
      refine ⟨39527903887294233003903659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26351935924862822002602439 39527903887294233003903659)
      ·
        refine ⟨59291855830941349505855489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39527903887294233003903659 59291855830941349505855489)
        ·
          refine ⟨44468891873206012129391617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59291855830941349505855489 44468891873206012129391617)
          ·
            refine ⟨33351668904904509097043713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44468891873206012129391617 33351668904904509097043713)
            ·
              refine ⟨25013751678678381822782785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33351668904904509097043713 25013751678678381822782785)
              ·
                refine ⟨18760313759008786367087089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25013751678678381822782785 18760313759008786367087089)
                ·
                  refine ⟨14070235319256589775315317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18760313759008786367087089 14070235319256589775315317)
                  ·
                    refine ⟨1319084561180305291435811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14070235319256589775315317 1319084561180305291435811)
                    ·
                      rfl

theorem cell22_3853362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_3853362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853362 prefixEnd_3853362 := by exact prefixLift 3853362
  have htrace : WordTrace (prefixWord ++ tailWord_3853362) baseStart_3853362 baseEnd_3853362 := by
    simpa [prefixWord, tailWord_3853362, baseEnd_3853362] using wordTrace_append hprefix tailTrace_3853362
  have hstable : (prefixWord ++ tailWord_3853362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853362).length < 2 ^ (prefixWord ++ tailWord_3853362).sum := by decide
  have hdescent : baseEnd_3853362 < baseStart_3853362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853368 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 1, 3]
def baseStart_3853368 : Nat := 118140960795 + 3853368 * 2 ^ 59
def prefixEnd_3853368 : Nat := 4983230072969 + 3 ^ 40 * 3853368 * 2
def baseEnd_3853368 : Nat := 1319086615102923275785793

theorem tailTrace_3853368 : CollatzResearch.WordTrace tailWord_3853368 prefixEnd_3853368 1319086615102923275785793 := by
  unfold tailWord_3853368
  simp only [CollatzResearch.WordTrace]
  refine ⟨70271938551956656852632379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93695918069275542470176505 70271938551956656852632379)
  ·
    refine ⟨105407907827934985278948569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70271938551956656852632379 105407907827934985278948569)
    ·
      refine ⟨79055930870951238959211427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105407907827934985278948569 79055930870951238959211427)
      ·
        refine ⟨118583896306426858438817141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79055930870951238959211427 118583896306426858438817141)
        ·
          refine ⟨11117240278727517978639107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118583896306426858438817141 11117240278727517978639107)
          ·
            refine ⟨16675860418091276967958661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117240278727517978639107 16675860418091276967958661)
            ·
              refine ⟨3126723828392114431492249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16675860418091276967958661 3126723828392114431492249)
              ·
                refine ⟨2345042871294085823619187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126723828392114431492249 2345042871294085823619187)
                ·
                  refine ⟨3517564306941128735428781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345042871294085823619187 3517564306941128735428781)
                  ·
                    refine ⟨1319086615102923275785793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517564306941128735428781 1319086615102923275785793)
                    ·
                      rfl

theorem cell22_3853368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_3853368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853368 prefixEnd_3853368 := by exact prefixLift 3853368
  have htrace : WordTrace (prefixWord ++ tailWord_3853368) baseStart_3853368 baseEnd_3853368 := by
    simpa [prefixWord, tailWord_3853368, baseEnd_3853368] using wordTrace_append hprefix tailTrace_3853368
  have hstable : (prefixWord ++ tailWord_3853368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853368).length < 2 ^ (prefixWord ++ tailWord_3853368).sum := by decide
  have hdescent : baseEnd_3853368 < baseStart_3853368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853394 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3853394 : Nat := 118140960795 + 3853394 * 2 ^ 59
def prefixEnd_3853394 : Nat := 4983230072969 + 3 ^ 40 * 3853394 * 2
def baseEnd_3853394 : Nat := 1319095515434267874635713

theorem tailTrace_3853394 : CollatzResearch.WordTrace tailWord_3853394 prefixEnd_3853394 1319095515434267874635713 := by
  unfold tailWord_3853394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35136206350454780036427809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93696550267879413430474157 35136206350454780036427809)
  ·
    refine ⟨26352154762841085027320857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35136206350454780036427809 26352154762841085027320857)
    ·
      refine ⟨19764116072130813770490643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26352154762841085027320857 19764116072130813770490643)
      ·
        refine ⟨29646174108196220655735965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19764116072130813770490643 29646174108196220655735965)
        ·
          refine ⟨11117315290573582745900987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29646174108196220655735965 11117315290573582745900987)
          ·
            refine ⟨16675972935860374118851481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117315290573582745900987 16675972935860374118851481)
            ·
              refine ⟨12506979701895280589138611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16675972935860374118851481 12506979701895280589138611)
              ·
                refine ⟨18760469552842920883707917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506979701895280589138611 18760469552842920883707917)
                ·
                  refine ⟨7035176082316095331390469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18760469552842920883707917 7035176082316095331390469)
                  ·
                    refine ⟨1319095515434267874635713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7035176082316095331390469 1319095515434267874635713)
                    ·
                      rfl

theorem cell22_3853394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3853394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853394 prefixEnd_3853394 := by exact prefixLift 3853394
  have htrace : WordTrace (prefixWord ++ tailWord_3853394) baseStart_3853394 baseEnd_3853394 := by
    simpa [prefixWord, tailWord_3853394, baseEnd_3853394] using wordTrace_append hprefix tailTrace_3853394
  have hstable : (prefixWord ++ tailWord_3853394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853394).length < 2 ^ (prefixWord ++ tailWord_3853394).sum := by decide
  have hdescent : baseEnd_3853394 < baseStart_3853394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853407 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 1, 5]
def baseStart_3853407 : Nat := 118140960795 + 3853407 * 2 ^ 59
def prefixEnd_3853407 : Nat := 4983230072969 + 3 ^ 40 * 3853407 * 2
def baseEnd_3853407 : Nat := 1319099965599940174060673

theorem tailTrace_3853407 : CollatzResearch.WordTrace tailWord_3853407 prefixEnd_3853407 1319099965599940174060673 := by
  unfold tailWord_3853407
  simp only [CollatzResearch.WordTrace]
  refine ⟨140545299550772023365934475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93696866367181348910622983 140545299550772023365934475)
  ·
    refine ⟨210817949326158035048901713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140545299550772023365934475 210817949326158035048901713)
    ·
      refine ⟨158113461994618526286676285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210817949326158035048901713 158113461994618526286676285)
      ·
        refine ⟨59292548247981947357503607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158113461994618526286676285 59292548247981947357503607)
        ·
          refine ⟨88938822371972921036255411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59292548247981947357503607 88938822371972921036255411)
          ·
            refine ⟨133408233557959381554383117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88938822371972921036255411 133408233557959381554383117)
            ·
              refine ⟨50028087584234768082893669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133408233557959381554383117 50028087584234768082893669)
              ·
                refine ⟨9380266422044019015542563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50028087584234768082893669 9380266422044019015542563)
                ·
                  refine ⟨14070399633066028523313845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380266422044019015542563 14070399633066028523313845)
                  ·
                    refine ⟨1319099965599940174060673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14070399633066028523313845 1319099965599940174060673)
                    ·
                      rfl

theorem cell22_3853407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_3853407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853407 prefixEnd_3853407 := by exact prefixLift 3853407
  have htrace : WordTrace (prefixWord ++ tailWord_3853407) baseStart_3853407 baseEnd_3853407 := by
    simpa [prefixWord, tailWord_3853407, baseEnd_3853407] using wordTrace_append hprefix tailTrace_3853407
  have hstable : (prefixWord ++ tailWord_3853407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853407).length < 2 ^ (prefixWord ++ tailWord_3853407).sum := by decide
  have hdescent : baseEnd_3853407 < baseStart_3853407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853409 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 4]
def baseStart_3853409 : Nat := 118140960795 + 3853409 * 2 ^ 59
def prefixEnd_3853409 : Nat := 4983230072969 + 3 ^ 40 * 3853409 * 2
def baseEnd_3853409 : Nat := 439700216746937611836889

theorem tailTrace_3853409 : CollatzResearch.WordTrace tailWord_3853409 prefixEnd_3853409 439700216746937611836889 := by
  unfold tailWord_3853409
  simp only [CollatzResearch.WordTrace]
  refine ⟨140545372496764777707507281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93696914997843185138338187 140545372496764777707507281)
  ·
    refine ⟨105409029372573583280630461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140545372496764777707507281 105409029372573583280630461)
    ·
      refine ⟨39528386014715093730236423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105409029372573583280630461 39528386014715093730236423)
      ·
        refine ⟨59292579022072640595354635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39528386014715093730236423 59292579022072640595354635)
        ·
          refine ⟨88938868533108960893031953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59292579022072640595354635 88938868533108960893031953)
          ·
            refine ⟨66704151399831720669773965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88938868533108960893031953 66704151399831720669773965)
            ·
              refine ⟨25014056774936895251165237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66704151399831720669773965 25014056774936895251165237)
              ·
                refine ⟨2345067822650333929796741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25014056774936895251165237 2345067822650333929796741)
                ·
                  refine ⟨439700216746937611836889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345067822650333929796741 439700216746937611836889)
                  ·
                    rfl

theorem cell22_3853409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_3853409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853409 prefixEnd_3853409 := by exact prefixLift 3853409
  have htrace : WordTrace (prefixWord ++ tailWord_3853409) baseStart_3853409 baseEnd_3853409 := by
    simpa [prefixWord, tailWord_3853409, baseEnd_3853409] using wordTrace_append hprefix tailTrace_3853409
  have hstable : (prefixWord ++ tailWord_3853409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853409).length < 2 ^ (prefixWord ++ tailWord_3853409).sum := by decide
  have hdescent : baseEnd_3853409 < baseStart_3853409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853424 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_3853424 : Nat := 118140960795 + 3853424 * 2 ^ 59
def prefixEnd_3853424 : Nat := 4983230072969 + 3 ^ 40 * 3853424 * 2
def baseEnd_3853424 : Nat := 1319105785047357796385621

theorem tailTrace_3853424 : CollatzResearch.WordTrace tailWord_3853424 prefixEnd_3853424 1319105785047357796385621 := by
  unfold tailWord_3853424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70272959795855217634651663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93697279727806956846202217 70272959795855217634651663)
  ·
    refine ⟨105409439693782826451977495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70272959795855217634651663 105409439693782826451977495)
    ·
      refine ⟨158114159540674239677966243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105409439693782826451977495 158114159540674239677966243)
      ·
        refine ⟨237171239311011359516949365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158114159540674239677966243 237171239311011359516949365)
        ·
          refine ⟨22234803685407314954714003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237171239311011359516949365 22234803685407314954714003)
          ·
            refine ⟨33352205528110972432071005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22234803685407314954714003 33352205528110972432071005)
            ·
              refine ⟨12507077073041614662026627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33352205528110972432071005 12507077073041614662026627)
              ·
                refine ⟨18760615609562421993039941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507077073041614662026627 18760615609562421993039941)
                ·
                  refine ⟨3517615426792954123694989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18760615609562421993039941 3517615426792954123694989)
                  ·
                    refine ⟨1319105785047357796385621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517615426792954123694989 1319105785047357796385621)
                    ·
                      rfl

theorem cell22_3853424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_3853424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853424 prefixEnd_3853424 := by exact prefixLift 3853424
  have htrace : WordTrace (prefixWord ++ tailWord_3853424) baseStart_3853424 baseEnd_3853424 := by
    simpa [prefixWord, tailWord_3853424, baseEnd_3853424] using wordTrace_append hprefix tailTrace_3853424
  have hstable : (prefixWord ++ tailWord_3853424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853424).length < 2 ^ (prefixWord ++ tailWord_3853424).sum := by decide
  have hdescent : baseEnd_3853424 < baseStart_3853424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853437 : List Nat := [1, 4, 1, 1, 3, 1, 2, 9]
def baseStart_3853437 : Nat := 118140960795 + 3853437 * 2 ^ 59
def prefixEnd_3853437 : Nat := 4983230072969 + 3 ^ 40 * 3853437 * 2
def baseEnd_3853437 : Nat := 146567803912558899534509

theorem tailTrace_3853437 : CollatzResearch.WordTrace tailWord_3853437 prefixEnd_3853437 146567803912558899534509 := by
  unfold tailWord_3853437
  simp only [CollatzResearch.WordTrace]
  refine ⟨140546393740663338489526565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93697595827108892326351043 140546393740663338489526565)
  ·
    refine ⟨26352448826374375966786231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140546393740663338489526565 26352448826374375966786231)
    ·
      refine ⟨39528673239561563950179347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26352448826374375966786231 39528673239561563950179347)
      ·
        refine ⟨59293009859342345925269021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39528673239561563950179347 59293009859342345925269021)
        ·
          refine ⟨22234878697253379721975883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59293009859342345925269021 22234878697253379721975883)
          ·
            refine ⟨33352318045880069582963825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22234878697253379721975883 33352318045880069582963825)
            ·
              refine ⟨25014238534410052187222869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33352318045880069582963825 25014238534410052187222869)
              ·
                refine ⟨146567803912558899534509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25014238534410052187222869 146567803912558899534509)
                ·
                  rfl

theorem cell22_3853437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 9].length) (baseStart_3853437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853437 prefixEnd_3853437 := by exact prefixLift 3853437
  have htrace : WordTrace (prefixWord ++ tailWord_3853437) baseStart_3853437 baseEnd_3853437 := by
    simpa [prefixWord, tailWord_3853437, baseEnd_3853437] using wordTrace_append hprefix tailTrace_3853437
  have hstable : (prefixWord ++ tailWord_3853437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853437).length < 2 ^ (prefixWord ++ tailWord_3853437).sum := by decide
  have hdescent : baseEnd_3853437 < baseStart_3853437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853441 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3853441 : Nat := 118140960795 + 3853441 * 2 ^ 59
def prefixEnd_3853441 : Nat := 4983230072969 + 3 ^ 40 * 3853441 * 2
def baseEnd_3853441 : Nat := 1319111604494775418710569

theorem tailTrace_3853441 : CollatzResearch.WordTrace tailWord_3853441 prefixEnd_3853441 1319111604494775418710569 := by
  unfold tailWord_3853441
  simp only [CollatzResearch.WordTrace]
  refine ⟨140546539632648847172672177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93697693088432564781781451 140546539632648847172672177)
  ·
    refine ⟨105409904724486635379504133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140546539632648847172672177 105409904724486635379504133)
    ·
      refine ⟨19764357135841244133657025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105409904724486635379504133 19764357135841244133657025)
      ·
        refine ⟨14823267851880933100242769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764357135841244133657025 14823267851880933100242769)
        ·
          refine ⟨11117450888910699825182077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14823267851880933100242769 11117450888910699825182077)
          ·
            refine ⟨4169044083341512434443279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11117450888910699825182077 4169044083341512434443279)
            ·
              refine ⟨6253566125012268651664919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169044083341512434443279 6253566125012268651664919)
              ·
                refine ⟨9380349187518402977497379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253566125012268651664919 9380349187518402977497379)
                ·
                  refine ⟨14070523781277604466246069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380349187518402977497379 14070523781277604466246069)
                  ·
                    refine ⟨1319111604494775418710569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14070523781277604466246069 1319111604494775418710569)
                    ·
                      rfl

theorem cell22_3853441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3853441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853441 prefixEnd_3853441 := by exact prefixLift 3853441
  have htrace : WordTrace (prefixWord ++ tailWord_3853441) baseStart_3853441 baseEnd_3853441 := by
    simpa [prefixWord, tailWord_3853441, baseEnd_3853441] using wordTrace_append hprefix tailTrace_3853441
  have hstable : (prefixWord ++ tailWord_3853441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853441).length < 2 ^ (prefixWord ++ tailWord_3853441).sum := by decide
  have hdescent : baseEnd_3853441 < baseStart_3853441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853454 : List Nat := [4, 1, 1, 3, 2, 2, 1, 8]
def baseStart_3853454 : Nat := 118140960795 + 3853454 * 2 ^ 59
def prefixEnd_3853454 : Nat := 4983230072969 + 3 ^ 40 * 3853454 * 2
def baseEnd_3853454 : Nat := 146568450517827524237281

theorem tailTrace_3853454 : CollatzResearch.WordTrace tailWord_3853454 prefixEnd_3853454 146568450517827524237281 := by
  unfold tailWord_3853454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568376722700218799111927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93698009187734500261930277 17568376722700218799111927)
  ·
    refine ⟨26352565084050328198667891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17568376722700218799111927 26352565084050328198667891)
    ·
      refine ⟨39528847626075492298001837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26352565084050328198667891 39528847626075492298001837)
      ·
        refine ⟨14823317859778309611750689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39528847626075492298001837 14823317859778309611750689)
        ·
          refine ⟨11117488394833732208813017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14823317859778309611750689 11117488394833732208813017)
          ·
            refine ⟨8338116296125299156609763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117488394833732208813017 8338116296125299156609763)
            ·
              refine ⟨12507174444187948734914645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338116296125299156609763 12507174444187948734914645)
              ·
                refine ⟨146568450517827524237281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12507174444187948734914645 146568450517827524237281)
                ·
                  rfl

theorem cell22_3853454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_3853454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853454 prefixEnd_3853454 := by exact prefixLift 3853454
  have htrace : WordTrace (prefixWord ++ tailWord_3853454) baseStart_3853454 baseEnd_3853454 := by
    simpa [prefixWord, tailWord_3853454, baseEnd_3853454] using wordTrace_append hprefix tailTrace_3853454
  have hstable : (prefixWord ++ tailWord_3853454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853454).length < 2 ^ (prefixWord ++ tailWord_3853454).sum := by decide
  have hdescent : baseEnd_3853454 < baseStart_3853454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853471 : List Nat := [1, 1, 2, 6, 3, 1, 8]
def baseStart_3853471 : Nat := 118140960795 + 3853471 * 2 ^ 59
def prefixEnd_3853471 : Nat := 4983230072969 + 3 ^ 40 * 3853471 * 2
def baseEnd_3853471 : Nat := 48856365707698716313351

theorem tailTrace_3853471 : CollatzResearch.WordTrace tailWord_3853471 prefixEnd_3853471 48856365707698716313351 := by
  unfold tailWord_3853471
  simp only [CollatzResearch.WordTrace]
  refine ⟨140547633822540162296264267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93698422548360108197509511 140547633822540162296264267)
  ·
    refine ⟨210821450733810243444396401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140547633822540162296264267 210821450733810243444396401)
    ·
      refine ⟨158116088050357682583297301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210821450733810243444396401 158116088050357682583297301)
      ·
        refine ⟨7411691627360516371092061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158116088050357682583297301 7411691627360516371092061)
        ·
          refine ⟨2779384360260193639159523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7411691627360516371092061 2779384360260193639159523)
          ·
            refine ⟨4169076540390290458739285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779384360260193639159523 4169076540390290458739285)
            ·
              refine ⟨48856365707698716313351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4169076540390290458739285 48856365707698716313351)
              ·
                rfl

theorem cell22_3853471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 8].length) (baseStart_3853471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853471 prefixEnd_3853471 := by exact prefixLift 3853471
  have htrace : WordTrace (prefixWord ++ tailWord_3853471) baseStart_3853471 baseEnd_3853471 := by
    simpa [prefixWord, tailWord_3853471, baseEnd_3853471] using wordTrace_append hprefix tailTrace_3853471
  have hstable : (prefixWord ++ tailWord_3853471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853471).length < 2 ^ (prefixWord ++ tailWord_3853471).sum := by decide
  have hdescent : baseEnd_3853471 < baseStart_3853471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853533 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3853533 : Nat := 118140960795 + 3853533 * 2 ^ 59
def prefixEnd_3853533 : Nat := 4983230072969 + 3 ^ 40 * 3853533 * 2
def baseEnd_3853533 : Nat := 439714365991639281803429

theorem tailTrace_3853533 : CollatzResearch.WordTrace tailWord_3853533 prefixEnd_3853533 439714365991639281803429 := by
  unfold tailWord_3853533
  simp only [CollatzResearch.WordTrace]
  refine ⟨140549895148315546885021253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93699930098877031256680835 140549895148315546885021253)
  ·
    refine ⟨26353105340309165040941485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140549895148315546885021253 26353105340309165040941485)
    ·
      refine ⟨9882414502615936890353057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26353105340309165040941485 9882414502615936890353057)
      ·
        refine ⟨7411810876961952667764793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9882414502615936890353057 7411810876961952667764793)
        ·
          refine ⟨5558858157721464500823595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7411810876961952667764793 5558858157721464500823595)
          ·
            refine ⟨8338287236582196751235393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558858157721464500823595 8338287236582196751235393)
            ·
              refine ⟨6253715427436647563426545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8338287236582196751235393 6253715427436647563426545)
              ·
                refine ⟨4690286570577485672569909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253715427436647563426545 4690286570577485672569909)
                ·
                  refine ⟨439714365991639281803429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690286570577485672569909 439714365991639281803429)
                  ·
                    rfl

theorem cell22_3853533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3853533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853533 prefixEnd_3853533 := by exact prefixLift 3853533
  have htrace : WordTrace (prefixWord ++ tailWord_3853533) baseStart_3853533 baseEnd_3853533 := by
    simpa [prefixWord, tailWord_3853533, baseEnd_3853533] using wordTrace_append hprefix tailTrace_3853533
  have hstable : (prefixWord ++ tailWord_3853533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853533).length < 2 ^ (prefixWord ++ tailWord_3853533).sum := by decide
  have hdescent : baseEnd_3853533 < baseStart_3853533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853544 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_3853544 : Nat := 118140960795 + 3853544 * 2 ^ 59
def prefixEnd_3853544 : Nat := 4983230072969 + 3 ^ 40 * 3853544 * 2
def baseEnd_3853544 : Nat := 439715621166572494461751

theorem tailTrace_3853544 : CollatzResearch.WordTrace tailWord_3853544 prefixEnd_3853544 439715621166572494461751 := by
  unfold tailWord_3853544
  simp only [CollatzResearch.WordTrace]
  refine ⟨70275148175637847881835843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93700197567517130509114457 70275148175637847881835843)
  ·
    refine ⟨105412722263456771822753765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70275148175637847881835843 105412722263456771822753765)
    ·
      refine ⟨19764885424398144716766331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105412722263456771822753765 19764885424398144716766331)
      ·
        refine ⟨29647328136597217075149497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19764885424398144716766331 29647328136597217075149497)
        ·
          refine ⟨22235496102447912806362123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29647328136597217075149497 22235496102447912806362123)
          ·
            refine ⟨33353244153671869209543185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22235496102447912806362123 33353244153671869209543185)
            ·
              refine ⟨25014933115253901907157389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33353244153671869209543185 25014933115253901907157389)
              ·
                refine ⟨9380599918220213215184021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25014933115253901907157389 9380599918220213215184021)
                ·
                  refine ⟨439715621166572494461751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9380599918220213215184021 439715621166572494461751)
                  ·
                    rfl

theorem cell22_3853544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_3853544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853544 prefixEnd_3853544 := by exact prefixLift 3853544
  have htrace : WordTrace (prefixWord ++ tailWord_3853544) baseStart_3853544 baseEnd_3853544 := by
    simpa [prefixWord, tailWord_3853544, baseEnd_3853544] using wordTrace_append hprefix tailTrace_3853544
  have hstable : (prefixWord ++ tailWord_3853544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853544).length < 2 ^ (prefixWord ++ tailWord_3853544).sum := by decide
  have hdescent : baseEnd_3853544 < baseStart_3853544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853661 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3853661 : Nat := 118140960795 + 3853661 * 2 ^ 59
def prefixEnd_3853661 : Nat := 4983230072969 + 3 ^ 40 * 3853661 * 2
def baseEnd_3853661 : Nat := 1319186914990768178209895

theorem tailTrace_3853661 : CollatzResearch.WordTrace tailWord_3853661 prefixEnd_3853661 1319186914990768178209895 := by
  unfold tailWord_3853661
  simp only [CollatzResearch.WordTrace]
  refine ⟨140554563691851824745680837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93703042461234549830453891 140554563691851824745680837)
  ·
    refine ⟨26353980692222217139815157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140554563691851824745680837 26353980692222217139815157)
    ·
      refine ⟨2470685689895832856857671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26353980692222217139815157 2470685689895832856857671)
      ·
        refine ⟨3706028534843749285286507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470685689895832856857671 3706028534843749285286507)
        ·
          refine ⟨5559042802265623927929761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706028534843749285286507 5559042802265623927929761)
          ·
            refine ⟨4169282101699217945947321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559042802265623927929761 4169282101699217945947321)
            ·
              refine ⟨3126961576274413459460491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169282101699217945947321 3126961576274413459460491)
              ·
                refine ⟨4690442364411620189190737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126961576274413459460491 4690442364411620189190737)
                ·
                  refine ⟨3517831773308715141893053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690442364411620189190737 3517831773308715141893053)
                  ·
                    refine ⟨1319186914990768178209895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517831773308715141893053 1319186914990768178209895)
                    ·
                      rfl

theorem cell22_3853661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3853661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853661 prefixEnd_3853661 := by exact prefixLift 3853661
  have htrace : WordTrace (prefixWord ++ tailWord_3853661) baseStart_3853661 baseEnd_3853661 := by
    simpa [prefixWord, tailWord_3853661, baseEnd_3853661] using wordTrace_append hprefix tailTrace_3853661
  have hstable : (prefixWord ++ tailWord_3853661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853661).length < 2 ^ (prefixWord ++ tailWord_3853661).sum := by decide
  have hdescent : baseEnd_3853661 < baseStart_3853661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853666 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3853666 : Nat := 118140960795 + 3853666 * 2 ^ 59
def prefixEnd_3853666 : Nat := 4983230072969 + 3 ^ 40 * 3853666 * 2
def baseEnd_3853666 : Nat := 1319188626592949831834879

theorem tailTrace_3853666 : CollatzResearch.WordTrace tailWord_3853666 prefixEnd_3853666 1319188626592949831834879 := by
  unfold tailWord_3853666
  simp only [CollatzResearch.WordTrace]
  refine ⟨35138686514208427649903213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93703164037889140399741901 35138686514208427649903213)
  ·
    refine ⟨13177007442828160368713705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35138686514208427649903213 13177007442828160368713705)
    ·
      refine ⟨9882755582121120276535279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13177007442828160368713705 9882755582121120276535279)
      ·
        refine ⟨14824133373181680414802919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9882755582121120276535279 14824133373181680414802919)
        ·
          refine ⟨22236200059772520622204379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14824133373181680414802919 22236200059772520622204379)
          ·
            refine ⟨33354300089658780933306569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22236200059772520622204379 33354300089658780933306569)
            ·
              refine ⟨25015725067244085699979927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33354300089658780933306569 25015725067244085699979927)
              ·
                refine ⟨37523587600866128549969891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25015725067244085699979927 37523587600866128549969891)
                ·
                  refine ⟨56285381401299192824954837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37523587600866128549969891 56285381401299192824954837)
                  ·
                    refine ⟨1319188626592949831834879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56285381401299192824954837 1319188626592949831834879)
                    ·
                      rfl

theorem cell22_3853666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3853666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853666 prefixEnd_3853666 := by exact prefixLift 3853666
  have htrace : WordTrace (prefixWord ++ tailWord_3853666) baseStart_3853666 baseEnd_3853666 := by
    simpa [prefixWord, tailWord_3853666, baseEnd_3853666] using wordTrace_append hprefix tailTrace_3853666
  have hstable : (prefixWord ++ tailWord_3853666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853666).length < 2 ^ (prefixWord ++ tailWord_3853666).sum := by decide
  have hdescent : baseEnd_3853666 < baseStart_3853666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853668 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 5]
def baseStart_3853668 : Nat := 118140960795 + 3853668 * 2 ^ 59
def prefixEnd_3853668 : Nat := 4983230072969 + 3 ^ 40 * 3853668 * 2
def baseEnd_3853668 : Nat := 439729770411274164428291

theorem tailTrace_3853668 : CollatzResearch.WordTrace tailWord_3853668 prefixEnd_3853668 439729770411274164428291 := by
  unfold tailWord_3853668
  simp only [CollatzResearch.WordTrace]
  refine ⟨70277409501413232470592829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93703212668550976627457105 70277409501413232470592829)
  ·
    refine ⟨26354028563029962176472311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70277409501413232470592829 26354028563029962176472311)
    ·
      refine ⟨39531042844544943264708467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26354028563029962176472311 39531042844544943264708467)
      ·
        refine ⟨59296564266817414897062701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39531042844544943264708467 59296564266817414897062701)
        ·
          refine ⟨22236211600056530586398513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59296564266817414897062701 22236211600056530586398513)
          ·
            refine ⟨16677158700042397939798885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22236211600056530586398513 16677158700042397939798885)
            ·
              refine ⟨3126967256257949613712291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16677158700042397939798885 3126967256257949613712291)
              ·
                refine ⟨4690450884386924420568437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126967256257949613712291 4690450884386924420568437)
                ·
                  refine ⟨439729770411274164428291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690450884386924420568437 439729770411274164428291)
                  ·
                    rfl

theorem cell22_3853668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_3853668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853668 prefixEnd_3853668 := by exact prefixLift 3853668
  have htrace : WordTrace (prefixWord ++ tailWord_3853668) baseStart_3853668 baseEnd_3853668 := by
    simpa [prefixWord, tailWord_3853668, baseEnd_3853668] using wordTrace_append hprefix tailTrace_3853668
  have hstable : (prefixWord ++ tailWord_3853668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853668).length < 2 ^ (prefixWord ++ tailWord_3853668).sum := by decide
  have hdescent : baseEnd_3853668 < baseStart_3853668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853679 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 8]
def baseStart_3853679 : Nat := 118140960795 + 3853679 * 2 ^ 59
def prefixEnd_3853679 : Nat := 4983230072969 + 3 ^ 40 * 3853679 * 2
def baseEnd_3853679 : Nat := 439731025586207377086613

theorem tailTrace_3853679 : CollatzResearch.WordTrace tailWord_3853679 prefixEnd_3853679 439731025586207377086613 := by
  unfold tailWord_3853679
  simp only [CollatzResearch.WordTrace]
  refine ⟨140555220205786613819836091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93703480137191075879890727 140555220205786613819836091)
  ·
    refine ⟨210832830308679920729754137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140555220205786613819836091 210832830308679920729754137)
    ·
      refine ⟨158124622731509940547315603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210832830308679920729754137 158124622731509940547315603)
      ·
        refine ⟨237186934097264910820973405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158124622731509940547315603 237186934097264910820973405)
        ·
          refine ⟨88945100286474341557865027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237186934097264910820973405 88945100286474341557865027)
          ·
            refine ⟨133417650429711512336797541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88945100286474341557865027 133417650429711512336797541)
            ·
              refine ⟨25015809455570908563149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133417650429711512336797541 25015809455570908563149539)
              ·
                refine ⟨37523714183356362844724309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25015809455570908563149539 37523714183356362844724309)
                ·
                  refine ⟨439731025586207377086613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37523714183356362844724309 439731025586207377086613)
                  ·
                    rfl

theorem cell22_3853679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_3853679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853679 prefixEnd_3853679 := by exact prefixLift 3853679
  have htrace : WordTrace (prefixWord ++ tailWord_3853679) baseStart_3853679 baseEnd_3853679 := by
    simpa [prefixWord, tailWord_3853679, baseEnd_3853679] using wordTrace_append hprefix tailTrace_3853679
  have hstable : (prefixWord ++ tailWord_3853679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853679).length < 2 ^ (prefixWord ++ tailWord_3853679).sum := by decide
  have hdescent : baseEnd_3853679 < baseStart_3853679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853728 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_3853728 : Nat := 118140960795 + 3853728 * 2 ^ 59
def prefixEnd_3853728 : Nat := 4983230072969 + 3 ^ 40 * 3853728 * 2
def baseEnd_3853728 : Nat := 1319209850460002336784689

theorem tailTrace_3853728 : CollatzResearch.WordTrace tailWord_3853728 prefixEnd_3853728 1319209850460002336784689 := by
  unfold tailWord_3853728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70278503691304547594184919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93704671588406063458913225 70278503691304547594184919)
  ·
    refine ⟨105417755536956821391277379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70278503691304547594184919 105417755536956821391277379)
    ·
      refine ⟨158126633305435232086916069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105417755536956821391277379 158126633305435232086916069)
      ·
        refine ⟨29648743744769106016296763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158126633305435232086916069 29648743744769106016296763)
        ·
          refine ⟨44473115617153659024445145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29648743744769106016296763 44473115617153659024445145)
          ·
            refine ⟨33354836712865244268333859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44473115617153659024445145 33354836712865244268333859)
            ·
              refine ⟨50032255069297866402500789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33354836712865244268333859 50032255069297866402500789)
              ·
                refine ⟨4690523912746674975234449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50032255069297866402500789 4690523912746674975234449)
                ·
                  refine ⟨3517892934560006231425837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690523912746674975234449 3517892934560006231425837)
                  ·
                    refine ⟨1319209850460002336784689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517892934560006231425837 1319209850460002336784689)
                    ·
                      rfl

theorem cell22_3853728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_3853728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853728 prefixEnd_3853728 := by exact prefixLift 3853728
  have htrace : WordTrace (prefixWord ++ tailWord_3853728) baseStart_3853728 baseEnd_3853728 := by
    simpa [prefixWord, tailWord_3853728, baseEnd_3853728] using wordTrace_append hprefix tailTrace_3853728
  have hstable : (prefixWord ++ tailWord_3853728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853728).length < 2 ^ (prefixWord ++ tailWord_3853728).sum := by decide
  have hdescent : baseEnd_3853728 < baseStart_3853728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853830 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3853830 : Nat := 118140960795 + 3853830 * 2 ^ 59
def prefixEnd_3853830 : Nat := 4983230072969 + 3 ^ 40 * 3853830 * 2
def baseEnd_3853830 : Nat := 1319244767144508070734377

theorem tailTrace_3853830 : CollatzResearch.WordTrace tailWord_3853830 prefixEnd_3853830 1319244767144508070734377 := by
  unfold tailWord_3853830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4392522738382486456518217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93707151752159711072388629 4392522738382486456518217)
  ·
    refine ⟨3294392053786864842388663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4392522738382486456518217 3294392053786864842388663)
    ·
      refine ⟨4941588080680297263582995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294392053786864842388663 4941588080680297263582995)
      ·
        refine ⟨7412382121020445895374493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941588080680297263582995 7412382121020445895374493)
        ·
          refine ⟨2779643295382667210765435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7412382121020445895374493 2779643295382667210765435)
          ·
            refine ⟨4169464943074000816148153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779643295382667210765435 4169464943074000816148153)
            ·
              refine ⟨3127098707305500612111115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169464943074000816148153 3127098707305500612111115)
              ·
                refine ⟨4690648060958250918166673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127098707305500612111115 4690648060958250918166673)
                ·
                  refine ⟨3517986045718688188625005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690648060958250918166673 3517986045718688188625005)
                  ·
                    refine ⟨1319244767144508070734377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517986045718688188625005 1319244767144508070734377)
                    ·
                      rfl

theorem cell22_3853830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3853830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853830 prefixEnd_3853830 := by exact prefixLift 3853830
  have htrace : WordTrace (prefixWord ++ tailWord_3853830) baseStart_3853830 baseEnd_3853830 := by
    simpa [prefixWord, tailWord_3853830, baseEnd_3853830] using wordTrace_append hprefix tailTrace_3853830
  have hstable : (prefixWord ++ tailWord_3853830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853830).length < 2 ^ (prefixWord ++ tailWord_3853830).sum := by decide
  have hdescent : baseEnd_3853830 < baseStart_3853830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853880 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_3853880 : Nat := 118140960795 + 3853880 * 2 ^ 59
def prefixEnd_3853880 : Nat := 4983230072969 + 3 ^ 40 * 3853880 * 2
def baseEnd_3853880 : Nat := 1319261883166324606984223

theorem tailTrace_3853880 : CollatzResearch.WordTrace tailWord_3853880 prefixEnd_3853880 1319261883166324606984223 := by
  unfold tailWord_3853880
  simp only [CollatzResearch.WordTrace]
  refine ⟨70281275639029212573951547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93708367518705616765268729 70281275639029212573951547)
  ·
    refine ⟨105421913458543818860927321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70281275639029212573951547 105421913458543818860927321)
    ·
      refine ⟨79066435093907864145695491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105421913458543818860927321 79066435093907864145695491)
      ·
        refine ⟨118599652640861796218543237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79066435093907864145695491 118599652640861796218543237)
        ·
          refine ⟨22237434870161586790976857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118599652640861796218543237 22237434870161586790976857)
          ·
            refine ⟨16678076152621190093232643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22237434870161586790976857 16678076152621190093232643)
            ·
              refine ⟨25017114228931785139848965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678076152621190093232643 25017114228931785139848965)
              ·
                refine ⟨4690708917924709713721681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25017114228931785139848965 4690708917924709713721681)
                ·
                  refine ⟨3518031688443532285291261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690708917924709713721681 3518031688443532285291261)
                  ·
                    refine ⟨1319261883166324606984223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518031688443532285291261 1319261883166324606984223)
                    ·
                      rfl

theorem cell22_3853880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_3853880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853880 prefixEnd_3853880 := by exact prefixLift 3853880
  have htrace : WordTrace (prefixWord ++ tailWord_3853880) baseStart_3853880 baseEnd_3853880 := by
    simpa [prefixWord, tailWord_3853880, baseEnd_3853880] using wordTrace_append hprefix tailTrace_3853880
  have hstable : (prefixWord ++ tailWord_3853880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853880).length < 2 ^ (prefixWord ++ tailWord_3853880).sum := by decide
  have hdescent : baseEnd_3853880 < baseStart_3853880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853891 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_3853891 : Nat := 118140960795 + 3853891 * 2 ^ 59
def prefixEnd_3853891 : Nat := 4983230072969 + 3 ^ 40 * 3853891 * 2
def baseEnd_3853891 : Nat := 1319265648691124244959189

theorem tailTrace_3853891 : CollatzResearch.WordTrace tailWord_3853891 prefixEnd_3853891 1319265648691124244959189 := by
  unfold tailWord_3853891
  simp only [CollatzResearch.WordTrace]
  refine ⟨140562952481018574026553527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93708634987345716017702351 140562952481018574026553527)
  ·
    refine ⟨210844428721527861039830291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140562952481018574026553527 210844428721527861039830291)
    ·
      refine ⟨316266643082291791559745437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210844428721527861039830291 316266643082291791559745437)
      ·
        refine ⟨118599991155859421834904539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316266643082291791559745437 118599991155859421834904539)
        ·
          refine ⟨177899986733789132752356809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118599991155859421834904539 177899986733789132752356809)
          ·
            refine ⟨133424990050341849564267607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177899986733789132752356809 133424990050341849564267607)
            ·
              refine ⟨200137485075512774346401411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133424990050341849564267607 200137485075512774346401411)
              ·
                refine ⟨300206227613269161519602117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200137485075512774346401411 300206227613269161519602117)
                ·
                  refine ⟨56288667677487967784925397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300206227613269161519602117 56288667677487967784925397)
                  ·
                    refine ⟨1319265648691124244959189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56288667677487967784925397 1319265648691124244959189)
                    ·
                      rfl

theorem cell22_3853891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_3853891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853891 prefixEnd_3853891 := by exact prefixLift 3853891
  have htrace : WordTrace (prefixWord ++ tailWord_3853891) baseStart_3853891 baseEnd_3853891 := by
    simpa [prefixWord, tailWord_3853891, baseEnd_3853891] using wordTrace_append hprefix tailTrace_3853891
  have hstable : (prefixWord ++ tailWord_3853891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853891).length < 2 ^ (prefixWord ++ tailWord_3853891).sum := by decide
  have hdescent : baseEnd_3853891 < baseStart_3853891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853942 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_3853942 : Nat := 118140960795 + 3853942 * 2 ^ 59
def prefixEnd_3853942 : Nat := 4983230072969 + 3 ^ 40 * 3853942 * 2
def baseEnd_3853942 : Nat := 1319283107033377111934033

theorem tailTrace_3853942 : CollatzResearch.WordTrace tailWord_3853942 prefixEnd_3853942 1319283107033377111934033 := by
  unfold tailWord_3853942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785300787739613108541255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93709875069222539824440053 8785300787739613108541255)
  ·
    refine ⟨13177951181609419662811883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785300787739613108541255 13177951181609419662811883)
    ·
      refine ⟨19766926772414129494217825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13177951181609419662811883 19766926772414129494217825)
      ·
        refine ⟨14825195079310597120663369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19766926772414129494217825 14825195079310597120663369)
        ·
          refine ⟨11118896309482947840497527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14825195079310597120663369 11118896309482947840497527)
          ·
            refine ⟨16678344464224421760746291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11118896309482947840497527 16678344464224421760746291)
            ·
              refine ⟨25017516696336632641119437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678344464224421760746291 25017516696336632641119437)
              ·
                refine ⟨9381568761126237240419789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25017516696336632641119437 9381568761126237240419789)
                ·
                  refine ⟨3518088285422338965157421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9381568761126237240419789 3518088285422338965157421)
                  ·
                    refine ⟨1319283107033377111934033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518088285422338965157421 1319283107033377111934033)
                    ·
                      rfl

theorem cell22_3853942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_3853942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853942 prefixEnd_3853942 := by exact prefixLift 3853942
  have htrace : WordTrace (prefixWord ++ tailWord_3853942) baseStart_3853942 baseEnd_3853942 := by
    simpa [prefixWord, tailWord_3853942, baseEnd_3853942] using wordTrace_append hprefix tailTrace_3853942
  have hstable : (prefixWord ++ tailWord_3853942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853942).length < 2 ^ (prefixWord ++ tailWord_3853942).sum := by decide
  have hdescent : baseEnd_3853942 < baseStart_3853942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853968 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_3853968 : Nat := 118140960795 + 3853968 * 2 ^ 59
def prefixEnd_3853968 : Nat := 4983230072969 + 3 ^ 40 * 3853968 * 2
def baseEnd_3853968 : Nat := 1319292007364721710783953

theorem tailTrace_3853968 : CollatzResearch.WordTrace tailWord_3853968 prefixEnd_3853968 1319292007364721710783953 := by
  unfold tailWord_3853968
  simp only [CollatzResearch.WordTrace]
  refine ⟨70282880450869808088553279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93710507267826410784737705 70282880450869808088553279)
  ·
    refine ⟨105424320676304712132829919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70282880450869808088553279 105424320676304712132829919)
    ·
      refine ⟨158136481014457068199244879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105424320676304712132829919 158136481014457068199244879)
      ·
        refine ⟨237204721521685602298867319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158136481014457068199244879 237204721521685602298867319)
        ·
          refine ⟨355807082282528403448300979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237204721521685602298867319 355807082282528403448300979)
          ·
            refine ⟨533710623423792605172451469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355807082282528403448300979 533710623423792605172451469)
            ·
              refine ⟨200141483783922226939669301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533710623423792605172451469 200141483783922226939669301)
              ·
                refine ⟨18763264104742708775593997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200141483783922226939669301 18763264104742708775593997)
                ·
                  refine ⟨7036224039278515790847749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18763264104742708775593997 7036224039278515790847749)
                  ·
                    refine ⟨1319292007364721710783953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7036224039278515790847749 1319292007364721710783953)
                    ·
                      rfl

theorem cell22_3853968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_3853968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3853968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3853968 prefixEnd_3853968 := by exact prefixLift 3853968
  have htrace : WordTrace (prefixWord ++ tailWord_3853968) baseStart_3853968 baseEnd_3853968 := by
    simpa [prefixWord, tailWord_3853968, baseEnd_3853968] using wordTrace_append hprefix tailTrace_3853968
  have hstable : (prefixWord ++ tailWord_3853968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853968).length < 2 ^ (prefixWord ++ tailWord_3853968).sum := by decide
  have hdescent : baseEnd_3853968 < baseStart_3853968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854000 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 4]
def baseStart_3854000 : Nat := 118140960795 + 3854000 * 2 ^ 59
def prefixEnd_3854000 : Nat := 4983230072969 + 3 ^ 40 * 3854000 * 2
def baseEnd_3854000 : Nat := 439767653872894764661285

theorem tailTrace_3854000 : CollatzResearch.WordTrace tailWord_3854000 prefixEnd_3854000 439767653872894764661285 := by
  unfold tailWord_3854000
  simp only [CollatzResearch.WordTrace]
  refine ⟨70283464018811842821135727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93711285358415790428180969 70283464018811842821135727)
  ·
    refine ⟨105425196028217764231703591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70283464018811842821135727 105425196028217764231703591)
    ·
      refine ⟨158137794042326646347555387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105425196028217764231703591 158137794042326646347555387)
      ·
        refine ⟨237206691063489969521333081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158137794042326646347555387 237206691063489969521333081)
        ·
          refine ⟨177905018297617477140999811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237206691063489969521333081 177905018297617477140999811)
          ·
            refine ⟨266857527446426215711499717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177905018297617477140999811 266857527446426215711499717)
            ·
              refine ⟨50035786396204915445906197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266857527446426215711499717 50035786396204915445906197)
              ·
                refine ⟨2345427487322105411526853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50035786396204915445906197 2345427487322105411526853)
                ·
                  refine ⟨439767653872894764661285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345427487322105411526853 439767653872894764661285)
                  ·
                    rfl

theorem cell22_3854000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_3854000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854000 prefixEnd_3854000 := by exact prefixLift 3854000
  have htrace : WordTrace (prefixWord ++ tailWord_3854000) baseStart_3854000 baseEnd_3854000 := by
    simpa [prefixWord, tailWord_3854000, baseEnd_3854000] using wordTrace_append hprefix tailTrace_3854000
  have hstable : (prefixWord ++ tailWord_3854000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854000).length < 2 ^ (prefixWord ++ tailWord_3854000).sum := by decide
  have hdescent : baseEnd_3854000 < baseStart_3854000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854006 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_3854006 : Nat := 118140960795 + 3854006 * 2 ^ 59
def prefixEnd_3854006 : Nat := 4983230072969 + 3 ^ 40 * 3854006 * 2
def baseEnd_3854006 : Nat := 439768338513767426111279

theorem tailTrace_3854006 : CollatzResearch.WordTrace tailWord_3854006 prefixEnd_3854006 439768338513767426111279 := by
  unfold tailWord_3854006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785446679725121791686867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93711431250401299111326581 8785446679725121791686867)
  ·
    refine ⟨13178170019587682687530301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785446679725121791686867 13178170019587682687530301)
    ·
      refine ⟨4941813757345381007823863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13178170019587682687530301 4941813757345381007823863)
      ·
        refine ⟨7412720636018071511735795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941813757345381007823863 7412720636018071511735795)
        ·
          refine ⟨11119080954027107267603693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412720636018071511735795 11119080954027107267603693)
          ·
            refine ⟨4169655357760165225351385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11119080954027107267603693 4169655357760165225351385)
            ·
              refine ⟨3127241518320123919013539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169655357760165225351385 3127241518320123919013539)
              ·
                refine ⟨4690862277480185878520309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127241518320123919013539 4690862277480185878520309)
                ·
                  refine ⟨439768338513767426111279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690862277480185878520309 439768338513767426111279)
                  ·
                    rfl

theorem cell22_3854006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_3854006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854006 prefixEnd_3854006 := by exact prefixLift 3854006
  have htrace : WordTrace (prefixWord ++ tailWord_3854006) baseStart_3854006 baseEnd_3854006 := by
    simpa [prefixWord, tailWord_3854006, baseEnd_3854006] using wordTrace_append hprefix tailTrace_3854006
  have hstable : (prefixWord ++ tailWord_3854006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854006).length < 2 ^ (prefixWord ++ tailWord_3854006).sum := by decide
  have hdescent : baseEnd_3854006 < baseStart_3854006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854045 : List Nat := [1, 4, 3, 3, 11]
def baseStart_3854045 : Nat := 118140960795 + 3854045 * 2 ^ 59
def prefixEnd_3854045 : Nat := 4983230072969 + 3 ^ 40 * 3854045 * 2
def baseEnd_3854045 : Nat := 5429293687400490438719

theorem tailTrace_3854045 : CollatzResearch.WordTrace tailWord_3854045 prefixEnd_3854045 5429293687400490438719 := by
  unfold tailWord_3854045
  simp only [CollatzResearch.WordTrace]
  refine ⟨140568569322460658327659589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93712379548307105551773059 140568569322460658327659589)
  ·
    refine ⟨26356606747961373436436173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140568569322460658327659589 26356606747961373436436173)
    ·
      refine ⟨9883727530485515038663565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26356606747961373436436173 9883727530485515038663565)
      ·
        refine ⟨3706397823932068139498837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9883727530485515038663565 3706397823932068139498837)
        ·
          refine ⟨5429293687400490438719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3706397823932068139498837 5429293687400490438719)
          ·
            rfl

theorem cell22_3854045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 11].length) (baseStart_3854045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854045 prefixEnd_3854045 := by exact prefixLift 3854045
  have htrace : WordTrace (prefixWord ++ tailWord_3854045) baseStart_3854045 baseEnd_3854045 := by
    simpa [prefixWord, tailWord_3854045, baseEnd_3854045] using wordTrace_append hprefix tailTrace_3854045
  have hstable : (prefixWord ++ tailWord_3854045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854045).length < 2 ^ (prefixWord ++ tailWord_3854045).sum := by decide
  have hdescent : baseEnd_3854045 < baseStart_3854045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854049 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3854049 : Nat := 118140960795 + 3854049 * 2 ^ 59
def prefixEnd_3854049 : Nat := 4983230072969 + 3 ^ 40 * 3854049 * 2
def baseEnd_3854049 : Nat := 1319319735320064499508705

theorem tailTrace_3854049 : CollatzResearch.WordTrace tailWord_3854049 prefixEnd_3854049 1319319735320064499508705 := by
  unfold tailWord_3854049
  simp only [CollatzResearch.WordTrace]
  refine ⟨140568715214446167010805201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93712476809630778007203467 140568715214446167010805201)
  ·
    refine ⟨105426536410834625258103901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140568715214446167010805201 105426536410834625258103901)
    ·
      refine ⟨39534951154062984471788963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105426536410834625258103901 39534951154062984471788963)
      ·
        refine ⟨59302426731094476707683445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39534951154062984471788963 59302426731094476707683445)
        ·
          refine ⟨5559602506040107191345323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59302426731094476707683445 5559602506040107191345323)
          ·
            refine ⟨8339403759060160787017985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559602506040107191345323 8339403759060160787017985)
            ·
              refine ⟨6254552819295120590263489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339403759060160787017985 6254552819295120590263489)
              ·
                refine ⟨4690914614471340442697617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6254552819295120590263489 4690914614471340442697617)
                ·
                  refine ⟨3518185960853505332023213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690914614471340442697617 3518185960853505332023213)
                  ·
                    refine ⟨1319319735320064499508705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518185960853505332023213 1319319735320064499508705)
                    ·
                      rfl

theorem cell22_3854049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3854049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854049 prefixEnd_3854049 := by exact prefixLift 3854049
  have htrace : WordTrace (prefixWord ++ tailWord_3854049) baseStart_3854049 baseEnd_3854049 := by
    simpa [prefixWord, tailWord_3854049, baseEnd_3854049] using wordTrace_append hprefix tailTrace_3854049
  have hstable : (prefixWord ++ tailWord_3854049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854049).length < 2 ^ (prefixWord ++ tailWord_3854049).sum := by decide
  have hdescent : baseEnd_3854049 < baseStart_3854049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854051 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 4]
def baseStart_3854051 : Nat := 118140960795 + 3854051 * 2 ^ 59
def prefixEnd_3854051 : Nat := 4983230072969 + 3 ^ 40 * 3854051 * 2
def baseEnd_3854051 : Nat := 439773473320312386986233

theorem tailTrace_3854051 : CollatzResearch.WordTrace tailWord_3854051 prefixEnd_3854051 439773473320312386986233 := by
  unfold tailWord_3854051
  simp only [CollatzResearch.WordTrace]
  refine ⟨140568788160438921352378007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93712525440292614234918671 140568788160438921352378007)
  ·
    refine ⟨210853182240658382028567011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140568788160438921352378007 210853182240658382028567011)
    ·
      refine ⟨316279773360987573042850517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210853182240658382028567011 316279773360987573042850517)
      ·
        refine ⟨7412807188148146243191809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 316279773360987573042850517 7412807188148146243191809)
        ·
          refine ⟨5559605391111109682393857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7412807188148146243191809 5559605391111109682393857)
          ·
            refine ⟨4169704043333332261795393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559605391111109682393857 4169704043333332261795393)
            ·
              refine ⟨3127278032499999196346545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169704043333332261795393 3127278032499999196346545)
              ·
                refine ⟨2345458524374999397259909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127278032499999196346545 2345458524374999397259909)
                ·
                  refine ⟨439773473320312386986233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345458524374999397259909 439773473320312386986233)
                  ·
                    rfl

theorem cell22_3854051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 4].length) (baseStart_3854051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854051 prefixEnd_3854051 := by exact prefixLift 3854051
  have htrace : WordTrace (prefixWord ++ tailWord_3854051) baseStart_3854051 baseEnd_3854051 := by
    simpa [prefixWord, tailWord_3854051, baseEnd_3854051] using wordTrace_append hprefix tailTrace_3854051
  have hstable : (prefixWord ++ tailWord_3854051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854051).length < 2 ^ (prefixWord ++ tailWord_3854051).sum := by decide
  have hdescent : baseEnd_3854051 < baseStart_3854051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854073 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 11]
def baseStart_3854073 : Nat := 118140960795 + 3854073 * 2 ^ 59
def prefixEnd_3854073 : Nat := 4983230072969 + 3 ^ 40 * 3854073 * 2
def baseEnd_3854073 : Nat := 439775983670178812302877

theorem tailTrace_3854073 : CollatzResearch.WordTrace tailWord_3854073 prefixEnd_3854073 439775983670178812302877 := by
  unfold tailWord_3854073
  simp only [CollatzResearch.WordTrace]
  refine ⟨140569590566359219109678873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93713060377572812739785915 140569590566359219109678873)
  ·
    refine ⟨105427192924769414332259155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140569590566359219109678873 105427192924769414332259155)
    ·
      refine ⟨158140789387154121498388733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105427192924769414332259155 158140789387154121498388733)
      ·
        refine ⟨59302796020182795561895775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158140789387154121498388733 59302796020182795561895775)
        ·
          refine ⟨88954194030274193342843663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59302796020182795561895775 88954194030274193342843663)
          ·
            refine ⟨133431291045411290014265495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88954194030274193342843663 133431291045411290014265495)
            ·
              refine ⟨200146936568116935021398243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133431291045411290014265495 200146936568116935021398243)
              ·
                refine ⟨300220404852175402532097365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200146936568116935021398243 300220404852175402532097365)
                ·
                  refine ⟨439775983670178812302877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 300220404852175402532097365 439775983670178812302877)
                  ·
                    rfl

theorem cell22_3854073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_3854073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854073 prefixEnd_3854073 := by exact prefixLift 3854073
  have htrace : WordTrace (prefixWord ++ tailWord_3854073) baseStart_3854073 baseEnd_3854073 := by
    simpa [prefixWord, tailWord_3854073, baseEnd_3854073] using wordTrace_append hprefix tailTrace_3854073
  have hstable : (prefixWord ++ tailWord_3854073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854073).length < 2 ^ (prefixWord ++ tailWord_3854073).sum := by decide
  have hdescent : baseEnd_3854073 < baseStart_3854073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854094 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_3854094 : Nat := 118140960795 + 3854094 * 2 ^ 59
def prefixEnd_3854094 : Nat := 4983230072969 + 3 ^ 40 * 3854094 * 2
def baseEnd_3854094 : Nat := 1319335139739699382133567

theorem tailTrace_3854094 : CollatzResearch.WordTrace tailWord_3854094 prefixEnd_3854094 1319335139739699382133567 := by
  unfold tailWord_3854094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17571294562410392462024167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93713570999522093130795557 17571294562410392462024167)
  ·
    refine ⟨26356941843615588693036251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17571294562410392462024167 26356941843615588693036251)
    ·
      refine ⟨39535412765423383039554377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26356941843615588693036251 39535412765423383039554377)
      ·
        refine ⟨29651559574067537279665783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39535412765423383039554377 29651559574067537279665783)
        ·
          refine ⟨44477339361101305919498675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29651559574067537279665783 44477339361101305919498675)
          ·
            refine ⟨66716009041651958879248013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44477339361101305919498675 66716009041651958879248013)
            ·
              refine ⟨25018503390619484579718005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66716009041651958879248013 25018503390619484579718005)
              ·
                refine ⟨2345484692870576679348563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25018503390619484579718005 2345484692870576679348563)
                ·
                  refine ⟨3518227039305865019022845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345484692870576679348563 3518227039305865019022845)
                  ·
                    refine ⟨1319335139739699382133567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518227039305865019022845 1319335139739699382133567)
                    ·
                      rfl

theorem cell22_3854094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_3854094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854094 prefixEnd_3854094 := by exact prefixLift 3854094
  have htrace : WordTrace (prefixWord ++ tailWord_3854094) baseStart_3854094 baseEnd_3854094 := by
    simpa [prefixWord, tailWord_3854094, baseEnd_3854094] using wordTrace_append hprefix tailTrace_3854094
  have hstable : (prefixWord ++ tailWord_3854094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854094).length < 2 ^ (prefixWord ++ tailWord_3854094).sum := by decide
  have hdescent : baseEnd_3854094 < baseStart_3854094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854100 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3854100 : Nat := 118140960795 + 3854100 * 2 ^ 59
def prefixEnd_3854100 : Nat := 4983230072969 + 3 ^ 40 * 3854100 * 2
def baseEnd_3854100 : Nat := 1319337193662317366483549

theorem tailTrace_3854100 : CollatzResearch.WordTrace tailWord_3854100 prefixEnd_3854100 1319337193662317366483549 := by
  unfold tailWord_3854100
  simp only [CollatzResearch.WordTrace]
  refine ⟨70285287668630701360455877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93713716891507601813941169 70285287668630701360455877)
  ·
    refine ⟨13178491437868256505085477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70285287668630701360455877 13178491437868256505085477)
    ·
      refine ⟨2470967144600298094703527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13178491437868256505085477 2470967144600298094703527)
      ·
        refine ⟨3706450716900447142055291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470967144600298094703527 3706450716900447142055291)
        ·
          refine ⟨5559676075350670713082937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706450716900447142055291 5559676075350670713082937)
          ·
            refine ⟨4169757056513003034812203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559676075350670713082937 4169757056513003034812203)
            ·
              refine ⟨6254635584769504552218305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169757056513003034812203 6254635584769504552218305)
              ·
                refine ⟨4690976688577128414163729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6254635584769504552218305 4690976688577128414163729)
                ·
                  refine ⟨3518232516432846310622797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690976688577128414163729 3518232516432846310622797)
                  ·
                    refine ⟨1319337193662317366483549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518232516432846310622797 1319337193662317366483549)
                    ·
                      rfl

theorem cell22_3854100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3854100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854100 prefixEnd_3854100 := by exact prefixLift 3854100
  have htrace : WordTrace (prefixWord ++ tailWord_3854100) baseStart_3854100 baseEnd_3854100 := by
    simpa [prefixWord, tailWord_3854100, baseEnd_3854100] using wordTrace_append hprefix tailTrace_3854100
  have hstable : (prefixWord ++ tailWord_3854100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854100).length < 2 ^ (prefixWord ++ tailWord_3854100).sum := by decide
  have hdescent : baseEnd_3854100 < baseStart_3854100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854169 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 4]
def baseStart_3854169 : Nat := 118140960795 + 3854169 * 2 ^ 59
def prefixEnd_3854169 : Nat := 4983230072969 + 3 ^ 40 * 3854169 * 2
def baseEnd_3854169 : Nat := 439786937924141395502779

theorem tailTrace_3854169 : CollatzResearch.WordTrace tailWord_3854169 prefixEnd_3854169 439786937924141395502779 := by
  unfold tailWord_3854169
  simp only [CollatzResearch.WordTrace]
  refine ⟨140573091974011427505173561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93715394649340951670115707 140573091974011427505173561)
  ·
    refine ⟨105429818980508570628880171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140573091974011427505173561 105429818980508570628880171)
    ·
      refine ⟨158144728470762855943320257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105429818980508570628880171 158144728470762855943320257)
      ·
        refine ⟨118608546353072141957490193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158144728470762855943320257 118608546353072141957490193)
        ·
          refine ⟨88956409764804106468117645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118608546353072141957490193 88956409764804106468117645)
          ·
            refine ⟨33358653661801539925544117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88956409764804106468117645 33358653661801539925544117)
            ·
              refine ⟨3127373780793894368019761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33358653661801539925544117 3127373780793894368019761)
              ·
                refine ⟨2345530335595420776014821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127373780793894368019761 2345530335595420776014821)
                ·
                  refine ⟨439786937924141395502779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345530335595420776014821 439786937924141395502779)
                  ·
                    rfl

theorem cell22_3854169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_3854169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854169 prefixEnd_3854169 := by exact prefixLift 3854169
  have htrace : WordTrace (prefixWord ++ tailWord_3854169) baseStart_3854169 baseEnd_3854169 := by
    simpa [prefixWord, tailWord_3854169, baseEnd_3854169] using wordTrace_append hprefix tailTrace_3854169
  have hstable : (prefixWord ++ tailWord_3854169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854169).length < 2 ^ (prefixWord ++ tailWord_3854169).sum := by decide
  have hdescent : baseEnd_3854169 < baseStart_3854169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854184 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_3854184 : Nat := 118140960795 + 3854184 * 2 ^ 59
def prefixEnd_3854184 : Nat := 4983230072969 + 3 ^ 40 * 3854184 * 2
def baseEnd_3854184 : Nat := 1319365948578969147383291

theorem tailTrace_3854184 : CollatzResearch.WordTrace tailWord_3854184 prefixEnd_3854184 1319365948578969147383291 := by
  unfold tailWord_3854184
  simp only [CollatzResearch.WordTrace]
  refine ⟨70286819534478542533484803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93715759379304723377979737 70286819534478542533484803)
  ·
    refine ⟨105430229301717813800227205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70286819534478542533484803 105430229301717813800227205)
    ·
      refine ⟨19768167994072090087542601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105430229301717813800227205 19768167994072090087542601)
      ·
        refine ⟨14826125995554067565656951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19768167994072090087542601 14826125995554067565656951)
        ·
          refine ⟨22239188993331101348485427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14826125995554067565656951 22239188993331101348485427)
          ·
            refine ⟨33358783489996652022728141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22239188993331101348485427 33358783489996652022728141)
            ·
              refine ⟨12509543808748744508523053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33358783489996652022728141 12509543808748744508523053)
              ·
                refine ⟨4691078928280779190696145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12509543808748744508523053 4691078928280779190696145)
                ·
                  refine ⟨3518309196210584393022109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4691078928280779190696145 3518309196210584393022109)
                  ·
                    refine ⟨1319365948578969147383291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518309196210584393022109 1319365948578969147383291)
                    ·
                      rfl

theorem cell22_3854184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_3854184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854184 prefixEnd_3854184 := by exact prefixLift 3854184
  have htrace : WordTrace (prefixWord ++ tailWord_3854184) baseStart_3854184 baseEnd_3854184 := by
    simpa [prefixWord, tailWord_3854184, baseEnd_3854184] using wordTrace_append hprefix tailTrace_3854184
  have hstable : (prefixWord ++ tailWord_3854184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854184).length < 2 ^ (prefixWord ++ tailWord_3854184).sum := by decide
  have hdescent : baseEnd_3854184 < baseStart_3854184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854225 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 7]
def baseStart_3854225 : Nat := 118140960795 + 3854225 * 2 ^ 59
def prefixEnd_3854225 : Nat := 4983230072969 + 3 ^ 40 * 3854225 * 2
def baseEnd_3854225 : Nat := 439793327905619569036055

theorem tailTrace_3854225 : CollatzResearch.WordTrace tailWord_3854225 prefixEnd_3854225 439793327905619569036055 := by
  unfold tailWord_3854225
  simp only [CollatzResearch.WordTrace]
  refine ⟨140575134461808549069212129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93716756307872366046141419 140575134461808549069212129)
  ·
    refine ⟨105431350846356411801909097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140575134461808549069212129 105431350846356411801909097)
    ·
      refine ⟨79073513134767308851431823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105431350846356411801909097 79073513134767308851431823)
      ·
        refine ⟨118610269702150963277147735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79073513134767308851431823 118610269702150963277147735)
        ·
          refine ⟨177915404553226444915721603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118610269702150963277147735 177915404553226444915721603)
          ·
            refine ⟨266873106829839667373582405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177915404553226444915721603 266873106829839667373582405)
            ·
              refine ⟨50038707530594937632546701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266873106829839667373582405 50038707530594937632546701)
              ·
                refine ⟨18764515323973101612205013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50038707530594937632546701 18764515323973101612205013)
                ·
                  refine ⟨439793327905619569036055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18764515323973101612205013 439793327905619569036055)
                  ·
                    rfl

theorem cell22_3854225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_3854225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854225 prefixEnd_3854225 := by exact prefixLift 3854225
  have htrace : WordTrace (prefixWord ++ tailWord_3854225) baseStart_3854225 baseEnd_3854225 := by
    simpa [prefixWord, tailWord_3854225, baseEnd_3854225] using wordTrace_append hprefix tailTrace_3854225
  have hstable : (prefixWord ++ tailWord_3854225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854225).length < 2 ^ (prefixWord ++ tailWord_3854225).sum := by decide
  have hdescent : baseEnd_3854225 < baseStart_3854225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854287 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 6]
def baseStart_3854287 : Nat := 118140960795 + 3854287 * 2 ^ 59
def prefixEnd_3854287 : Nat := 4983230072969 + 3 ^ 40 * 3854287 * 2
def baseEnd_3854287 : Nat := 439800402527970404019325

theorem tailTrace_3854287 : CollatzResearch.WordTrace tailWord_3854287 prefixEnd_3854287 439800402527970404019325 := by
  unfold tailWord_3854287
  simp only [CollatzResearch.WordTrace]
  refine ⟨140577395787583933657969115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93718263858389289105312743 140577395787583933657969115)
  ·
    refine ⟨210866093681375900486953673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140577395787583933657969115 210866093681375900486953673)
    ·
      refine ⟨158149570261031925365215255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210866093681375900486953673 158149570261031925365215255)
      ·
        refine ⟨237224355391547888047822883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158149570261031925365215255 237224355391547888047822883)
        ·
          refine ⟨355836533087321832071734325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237224355391547888047822883 355836533087321832071734325)
          ·
            refine ⟨33359674976936421756725093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355836533087321832071734325 33359674976936421756725093)
            ·
              refine ⟨6254939058175579079385955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33359674976936421756725093 6254939058175579079385955)
              ·
                refine ⟨9382408587263368619078933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254939058175579079385955 9382408587263368619078933)
                ·
                  refine ⟨439800402527970404019325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9382408587263368619078933 439800402527970404019325)
                  ·
                    rfl

theorem cell22_3854287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 6].length) (baseStart_3854287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854287 prefixEnd_3854287 := by exact prefixLift 3854287
  have htrace : WordTrace (prefixWord ++ tailWord_3854287) baseStart_3854287 baseEnd_3854287 := by
    simpa [prefixWord, tailWord_3854287, baseEnd_3854287] using wordTrace_append hprefix tailTrace_3854287
  have hstable : (prefixWord ++ tailWord_3854287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854287).length < 2 ^ (prefixWord ++ tailWord_3854287).sum := by decide
  have hdescent : baseEnd_3854287 < baseStart_3854287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854424 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_3854424 : Nat := 118140960795 + 3854424 * 2 ^ 59
def prefixEnd_3854424 : Nat := 4983230072969 + 3 ^ 40 * 3854424 * 2
def baseEnd_3854424 : Nat := 1319448105483688521382555

theorem tailTrace_3854424 : CollatzResearch.WordTrace tailWord_3854424 prefixEnd_3854424 1319448105483688521382555 := by
  unfold tailWord_3854424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70291196294043803027853163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93721595058725070703804217 70291196294043803027853163)
  ·
    refine ⟨105436794441065704541779745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70291196294043803027853163 105436794441065704541779745)
    ·
      refine ⟨79077595830799278406334809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105436794441065704541779745 79077595830799278406334809)
      ·
        refine ⟨59308196873099458804751107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79077595830799278406334809 59308196873099458804751107)
        ·
          refine ⟨88962295309649188207126661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59308196873099458804751107 88962295309649188207126661)
          ·
            refine ⟨16680430370559222788836249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88962295309649188207126661 16680430370559222788836249)
            ·
              refine ⟨12510322777919417091627187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16680430370559222788836249 12510322777919417091627187)
              ·
                refine ⟨18765484166879125637440781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12510322777919417091627187 18765484166879125637440781)
                ·
                  refine ⟨7037056562579672114040293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18765484166879125637440781 7037056562579672114040293)
                  ·
                    refine ⟨1319448105483688521382555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7037056562579672114040293 1319448105483688521382555)
                    ·
                      rfl

theorem cell22_3854424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_3854424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854424 prefixEnd_3854424 := by exact prefixLift 3854424
  have htrace : WordTrace (prefixWord ++ tailWord_3854424) baseStart_3854424 baseEnd_3854424 := by
    simpa [prefixWord, tailWord_3854424, baseEnd_3854424] using wordTrace_append hprefix tailTrace_3854424
  have hstable : (prefixWord ++ tailWord_3854424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854424).length < 2 ^ (prefixWord ++ tailWord_3854424).sum := by decide
  have hdescent : baseEnd_3854424 < baseStart_3854424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854469 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3854469 : Nat := 118140960795 + 3854469 * 2 ^ 59
def prefixEnd_3854469 : Nat := 4983230072969 + 3 ^ 40 * 3854469 * 2
def baseEnd_3854469 : Nat := 1319463509903323404007417

theorem tailTrace_3854469 : CollatzResearch.WordTrace tailWord_3854469 prefixEnd_3854469 1319463509903323404007417 := by
  unfold tailWord_3854469
  simp only [CollatzResearch.WordTrace]
  refine ⟨140584033872924578741094461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93722689248616385827396307 140584033872924578741094461)
  ·
    refine ⟨52719012702346717027910423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140584033872924578741094461 52719012702346717027910423)
    ·
      refine ⟨79078519053520075541865635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52719012702346717027910423 79078519053520075541865635)
      ·
        refine ⟨118617778580280113312798453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79078519053520075541865635 118617778580280113312798453)
        ·
          refine ⟨11120416741901260623074855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118617778580280113312798453 11120416741901260623074855)
          ·
            refine ⟨16680625112851890934612283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11120416741901260623074855 16680625112851890934612283)
            ·
              refine ⟨25020937669277836401918425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16680625112851890934612283 25020937669277836401918425)
              ·
                refine ⟨18765703251958377301438819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25020937669277836401918425 18765703251958377301438819)
                ·
                  refine ⟨28148554877937565952158229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18765703251958377301438819 28148554877937565952158229)
                  ·
                    refine ⟨1319463509903323404007417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28148554877937565952158229 1319463509903323404007417)
                    ·
                      rfl

theorem cell22_3854469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3854469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854469 prefixEnd_3854469 := by exact prefixLift 3854469
  have htrace : WordTrace (prefixWord ++ tailWord_3854469) baseStart_3854469 baseEnd_3854469 := by
    simpa [prefixWord, tailWord_3854469, baseEnd_3854469] using wordTrace_append hprefix tailTrace_3854469
  have hstable : (prefixWord ++ tailWord_3854469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854469).length < 2 ^ (prefixWord ++ tailWord_3854469).sum := by decide
  have hdescent : baseEnd_3854469 < baseStart_3854469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854471 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 2, 3]
def baseStart_3854471 : Nat := 118140960795 + 3854471 * 2 ^ 59
def prefixEnd_3854471 : Nat := 4983230072969 + 3 ^ 40 * 3854471 * 2
def baseEnd_3854471 : Nat := 1319464194544196065457411

theorem tailTrace_3854471 : CollatzResearch.WordTrace tailWord_3854471 prefixEnd_3854471 1319464194544196065457411 := by
  unfold tailWord_3854471
  simp only [CollatzResearch.WordTrace]
  refine ⟨140584106818917333082667267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93722737879278222055111511 140584106818917333082667267)
  ·
    refine ⟨210876160228375999624000901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140584106818917333082667267 210876160228375999624000901)
    ·
      refine ⟨39539280042820499929500169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210876160228375999624000901 39539280042820499929500169)
      ·
        refine ⟨29654460032115374947125127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39539280042820499929500169 29654460032115374947125127)
        ·
          refine ⟨44481690048173062420687691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29654460032115374947125127 44481690048173062420687691)
          ·
            refine ⟨66722535072259593631031537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44481690048173062420687691 66722535072259593631031537)
            ·
              refine ⟨50041901304194695223273653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66722535072259593631031537 50041901304194695223273653)
              ·
                refine ⟨4691428247268252677181905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50041901304194695223273653 4691428247268252677181905)
                ·
                  refine ⟨3518571185451189507886429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4691428247268252677181905 3518571185451189507886429)
                  ·
                    refine ⟨1319464194544196065457411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518571185451189507886429 1319464194544196065457411)
                    ·
                      rfl

theorem cell22_3854471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_3854471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854471 prefixEnd_3854471 := by exact prefixLift 3854471
  have htrace : WordTrace (prefixWord ++ tailWord_3854471) baseStart_3854471 baseEnd_3854471 := by
    simpa [prefixWord, tailWord_3854471, baseEnd_3854471] using wordTrace_append hprefix tailTrace_3854471
  have hstable : (prefixWord ++ tailWord_3854471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854471).length < 2 ^ (prefixWord ++ tailWord_3854471).sum := by decide
  have hdescent : baseEnd_3854471 < baseStart_3854471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854490 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_3854490 : Nat := 118140960795 + 3854490 * 2 ^ 59
def prefixEnd_3854490 : Nat := 4983230072969 + 3 ^ 40 * 3854490 * 2
def baseEnd_3854490 : Nat := 439823566210828783077451

theorem tailTrace_3854490 : CollatzResearch.WordTrace tailWord_3854490 prefixEnd_3854490 439823566210828783077451 := by
  unfold tailWord_3854490
  simp only [CollatzResearch.WordTrace]
  refine ⟨35146199951462124831902231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93723199870565666218405949 35146199951462124831902231)
  ·
    refine ⟨52719299927193187247853347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35146199951462124831902231 52719299927193187247853347)
    ·
      refine ⟨79078949890789780871780021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52719299927193187247853347 79078949890789780871780021)
      ·
        refine ⟨7413651552261541956729377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79078949890789780871780021 7413651552261541956729377)
        ·
          refine ⟨5560238664196156467547033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7413651552261541956729377 5560238664196156467547033)
          ·
            refine ⟨4170178998147117350660275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5560238664196156467547033 4170178998147117350660275)
            ·
              refine ⟨6255268497220676025990413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170178998147117350660275 6255268497220676025990413)
              ·
                refine ⟨2345725686457753509746405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6255268497220676025990413 2345725686457753509746405)
                ·
                  refine ⟨439823566210828783077451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345725686457753509746405 439823566210828783077451)
                  ·
                    rfl

theorem cell22_3854490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_3854490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854490 prefixEnd_3854490 := by exact prefixLift 3854490
  have htrace : WordTrace (prefixWord ++ tailWord_3854490) baseStart_3854490 baseEnd_3854490 := by
    simpa [prefixWord, tailWord_3854490, baseEnd_3854490] using wordTrace_append hprefix tailTrace_3854490
  have hstable : (prefixWord ++ tailWord_3854490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854490).length < 2 ^ (prefixWord ++ tailWord_3854490).sum := by decide
  have hdescent : baseEnd_3854490 < baseStart_3854490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854503 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3854503 : Nat := 118140960795 + 3854503 * 2 ^ 59
def prefixEnd_3854503 : Nat := 4983230072969 + 3 ^ 40 * 3854503 * 2
def baseEnd_3854503 : Nat := 1319475148798158648657313

theorem tailTrace_3854503 : CollatzResearch.WordTrace tailWord_3854503 prefixEnd_3854503 1319475148798158648657313 := by
  unfold tailWord_3854503
  simp only [CollatzResearch.WordTrace]
  refine ⟨140585273954801402547832163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93723515969867601698554775 140585273954801402547832163)
  ·
    refine ⟨210877910932202103821748245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140585273954801402547832163 210877910932202103821748245)
    ·
      refine ⟨9884902074946973616644449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210877910932202103821748245 9884902074946973616644449)
      ·
        refine ⟨7413676556210230212483337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9884902074946973616644449 7413676556210230212483337)
        ·
          refine ⟨5560257417157672659362503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7413676556210230212483337 5560257417157672659362503)
          ·
            refine ⟨8340386125736508989043755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560257417157672659362503 8340386125736508989043755)
            ·
              refine ⟨12510579188604763483565633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340386125736508989043755 12510579188604763483565633)
              ·
                refine ⟨9382934391453572612674225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12510579188604763483565633 9382934391453572612674225)
                ·
                  refine ⟨7037200793590179459505669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9382934391453572612674225 7037200793590179459505669)
                  ·
                    refine ⟨1319475148798158648657313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7037200793590179459505669 1319475148798158648657313)
                    ·
                      rfl

theorem cell22_3854503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3854503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854503 prefixEnd_3854503 := by exact prefixLift 3854503
  have htrace : WordTrace (prefixWord ++ tailWord_3854503) baseStart_3854503 baseEnd_3854503 := by
    simpa [prefixWord, tailWord_3854503, baseEnd_3854503] using wordTrace_append hprefix tailTrace_3854503
  have hstable : (prefixWord ++ tailWord_3854503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854503).length < 2 ^ (prefixWord ++ tailWord_3854503).sum := by decide
  have hdescent : baseEnd_3854503 < baseStart_3854503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854514 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_3854514 : Nat := 118140960795 + 3854514 * 2 ^ 59
def prefixEnd_3854514 : Nat := 4983230072969 + 3 ^ 40 * 3854514 * 2
def baseEnd_3854514 : Nat := 1319478914322958286632279

theorem tailTrace_3854514 : CollatzResearch.WordTrace tailWord_3854514 prefixEnd_3854514 1319478914322958286632279 := by
  unfold tailWord_3854514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35146418789440387856620649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93723783438507700950988397 35146418789440387856620649)
  ·
    refine ⟨26359814092080290892465487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35146418789440387856620649 26359814092080290892465487)
    ·
      refine ⟨39539721138120436338698231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26359814092080290892465487 39539721138120436338698231)
      ·
        refine ⟨59309581707180654508047347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39539721138120436338698231 59309581707180654508047347)
        ·
          refine ⟨88964372560770981762071021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59309581707180654508047347 88964372560770981762071021)
          ·
            refine ⟨33361639710289118160776633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88964372560770981762071021 33361639710289118160776633)
            ·
              refine ⟨25021229782716838620582475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33361639710289118160776633 25021229782716838620582475)
              ·
                refine ⟨37531844674075257930873713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25021229782716838620582475 37531844674075257930873713)
                ·
                  refine ⟨28148883505556443448155285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37531844674075257930873713 28148883505556443448155285)
                  ·
                    refine ⟨1319478914322958286632279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28148883505556443448155285 1319478914322958286632279)
                    ·
                      rfl

theorem cell22_3854514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_3854514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854514 prefixEnd_3854514 := by exact prefixLift 3854514
  have htrace : WordTrace (prefixWord ++ tailWord_3854514) baseStart_3854514 baseEnd_3854514 := by
    simpa [prefixWord, tailWord_3854514, baseEnd_3854514] using wordTrace_append hprefix tailTrace_3854514
  have hstable : (prefixWord ++ tailWord_3854514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854514).length < 2 ^ (prefixWord ++ tailWord_3854514).sum := by decide
  have hdescent : baseEnd_3854514 < baseStart_3854514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854567 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3854567 : Nat := 118140960795 + 3854567 * 2 ^ 59
def prefixEnd_3854567 : Nat := 4983230072969 + 3 ^ 40 * 3854567 * 2
def baseEnd_3854567 : Nat := 1319497057306083815057117

theorem tailTrace_3854567 : CollatzResearch.WordTrace tailWord_3854567 prefixEnd_3854567 1319497057306083815057117 := by
  unfold tailWord_3854567
  simp only [CollatzResearch.WordTrace]
  refine ⟨140587608226569541478161955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93725072151046360985441303 140587608226569541478161955)
  ·
    refine ⟨210881412339854312217242933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140587608226569541478161955 210881412339854312217242933)
    ·
      refine ⟨19770132406861341770366525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210881412339854312217242933 19770132406861341770366525)
      ·
        refine ⟨7413799652573003163887447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19770132406861341770366525 7413799652573003163887447)
        ·
          refine ⟨11120699478859504745831171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413799652573003163887447 11120699478859504745831171)
          ·
            refine ⟨16681049218289257118746757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11120699478859504745831171 16681049218289257118746757)
            ·
              refine ⟨3127696728429235709765017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16681049218289257118746757 3127696728429235709765017)
              ·
                refine ⟨2345772546321926782323763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127696728429235709765017 2345772546321926782323763)
                ·
                  refine ⟨3518658819482890173485645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345772546321926782323763 3518658819482890173485645)
                  ·
                    refine ⟨1319497057306083815057117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518658819482890173485645 1319497057306083815057117)
                    ·
                      rfl

theorem cell22_3854567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3854567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854567 prefixEnd_3854567 := by exact prefixLift 3854567
  have htrace : WordTrace (prefixWord ++ tailWord_3854567) baseStart_3854567 baseEnd_3854567 := by
    simpa [prefixWord, tailWord_3854567, baseEnd_3854567] using wordTrace_append hprefix tailTrace_3854567
  have hstable : (prefixWord ++ tailWord_3854567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854567).length < 2 ^ (prefixWord ++ tailWord_3854567).sum := by decide
  have hdescent : baseEnd_3854567 < baseStart_3854567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854606 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_3854606 : Nat := 118140960795 + 3854606 * 2 ^ 59
def prefixEnd_3854606 : Nat := 4983230072969 + 3 ^ 40 * 3854606 * 2
def baseEnd_3854606 : Nat := 1319510407803100713331997

theorem tailTrace_3854606 : CollatzResearch.WordTrace tailWord_3854606 prefixEnd_3854606 1319510407803100713331997 := by
  unfold tailWord_3854606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17573628834178531392353959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93726020448952167425887781 17573628834178531392353959)
  ·
    refine ⟨26360443251267797088530939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17573628834178531392353959 26360443251267797088530939)
    ·
      refine ⟨39540664876901695632796409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26360443251267797088530939 39540664876901695632796409)
      ·
        refine ⟨29655498657676271724597307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39540664876901695632796409 29655498657676271724597307)
        ·
          refine ⟨44483247986514407586895961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29655498657676271724597307 44483247986514407586895961)
          ·
            refine ⟨33362435989885805690171971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44483247986514407586895961 33362435989885805690171971)
            ·
              refine ⟨50043653984828708535257957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33362435989885805690171971 50043653984828708535257957)
              ·
                refine ⟨9383185122155382850360867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50043653984828708535257957 9383185122155382850360867)
                ·
                  refine ⟨14074777683233074275541301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9383185122155382850360867 14074777683233074275541301)
                  ·
                    refine ⟨1319510407803100713331997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14074777683233074275541301 1319510407803100713331997)
                    ·
                      rfl

theorem cell22_3854606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_3854606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854606 prefixEnd_3854606 := by exact prefixLift 3854606
  have htrace : WordTrace (prefixWord ++ tailWord_3854606) baseStart_3854606 baseEnd_3854606 := by
    simpa [prefixWord, tailWord_3854606, baseEnd_3854606] using wordTrace_append hprefix tailTrace_3854606
  have hstable : (prefixWord ++ tailWord_3854606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854606).length < 2 ^ (prefixWord ++ tailWord_3854606).sum := by decide
  have hdescent : baseEnd_3854606 < baseStart_3854606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854623 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 4, 3]
def baseStart_3854623 : Nat := 118140960795 + 3854623 * 2 ^ 59
def prefixEnd_3854623 : Nat := 4983230072969 + 3 ^ 40 * 3854623 * 2
def baseEnd_3854623 : Nat := 1319516227250518335656945

theorem tailTrace_3854623 : CollatzResearch.WordTrace tailWord_3854623 prefixEnd_3854623 1319516227250518335656945 := by
  unfold tailWord_3854623
  simp only [CollatzResearch.WordTrace]
  refine ⟨140589650714366663042200523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93726433809577775361467015 140589650714366663042200523)
  ·
    refine ⟨210884476071549994563300785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140589650714366663042200523 210884476071549994563300785)
    ·
      refine ⟨158163357053662495922475589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210884476071549994563300785 158163357053662495922475589)
      ·
        refine ⟨29655629447561717985464173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158163357053662495922475589 29655629447561717985464173)
        ·
          refine ⟨11120861042835644244549065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29655629447561717985464173 11120861042835644244549065)
          ·
            refine ⟨8340645782126733183411799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11120861042835644244549065 8340645782126733183411799)
            ·
              refine ⟨12510968673190099775117699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340645782126733183411799 12510968673190099775117699)
              ·
                refine ⟨18766453009785149662676549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12510968673190099775117699 18766453009785149662676549)
                ·
                  refine ⟨3518709939334715561751853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18766453009785149662676549 3518709939334715561751853)
                  ·
                    refine ⟨1319516227250518335656945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518709939334715561751853 1319516227250518335656945)
                    ·
                      rfl

theorem cell22_3854623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_3854623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854623 prefixEnd_3854623 := by exact prefixLift 3854623
  have htrace : WordTrace (prefixWord ++ tailWord_3854623) baseStart_3854623 baseEnd_3854623 := by
    simpa [prefixWord, tailWord_3854623, baseEnd_3854623] using wordTrace_append hprefix tailTrace_3854623
  have hstable : (prefixWord ++ tailWord_3854623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854623).length < 2 ^ (prefixWord ++ tailWord_3854623).sum := by decide
  have hdescent : baseEnd_3854623 < baseStart_3854623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854681 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 5]
def baseStart_3854681 : Nat := 118140960795 + 3854681 * 2 ^ 59
def prefixEnd_3854681 : Nat := 4983230072969 + 3 ^ 40 * 3854681 * 2
def baseEnd_3854681 : Nat := 439845360611941839235589

theorem tailTrace_3854681 : CollatzResearch.WordTrace tailWord_3854681 prefixEnd_3854681 439845360611941839235589 := by
  unfold tailWord_3854681
  simp only [CollatzResearch.WordTrace]
  refine ⟨140591766148156538947811897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93727844098771025965207931 140591766148156538947811897)
  ·
    refine ⟨105443824611117404210858923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140591766148156538947811897 105443824611117404210858923)
    ·
      refine ⟨158165736916676106316288385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105443824611117404210858923 158165736916676106316288385)
      ·
        refine ⟨118624302687507079737216289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158165736916676106316288385 118624302687507079737216289)
        ·
          refine ⟨88968227015630309802912217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118624302687507079737216289 88968227015630309802912217)
          ·
            refine ⟨66726170261722732352184163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88968227015630309802912217 66726170261722732352184163)
            ·
              refine ⟨100089255392584098528276245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66726170261722732352184163 100089255392584098528276245)
              ·
                refine ⟨4691683846527379618512949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100089255392584098528276245 4691683846527379618512949)
                ·
                  refine ⟨439845360611941839235589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4691683846527379618512949 439845360611941839235589)
                  ·
                    rfl

theorem cell22_3854681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_3854681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854681 prefixEnd_3854681 := by exact prefixLift 3854681
  have htrace : WordTrace (prefixWord ++ tailWord_3854681) baseStart_3854681 baseEnd_3854681 := by
    simpa [prefixWord, tailWord_3854681, baseEnd_3854681] using wordTrace_append hprefix tailTrace_3854681
  have hstable : (prefixWord ++ tailWord_3854681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854681).length < 2 ^ (prefixWord ++ tailWord_3854681).sum := by decide
  have hdescent : baseEnd_3854681 < baseStart_3854681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854741 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3854741 : Nat := 118140960795 + 3854741 * 2 ^ 59
def prefixEnd_3854741 : Nat := 4983230072969 + 3 ^ 40 * 3854741 * 2
def baseEnd_3854741 : Nat := 1319556621062005361206583

theorem tailTrace_3854741 : CollatzResearch.WordTrace tailWord_3854741 prefixEnd_3854741 1319556621062005361206583 := by
  unfold tailWord_3854741
  simp only [CollatzResearch.WordTrace]
  refine ⟨140593954527939169194996077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93729303018626112796664051 140593954527939169194996077)
  ·
    refine ⟨52722732947977188448123529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140593954527939169194996077 52722732947977188448123529)
    ·
      refine ⟨39542049710982891336092647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52722732947977188448123529 39542049710982891336092647)
      ·
        refine ⟨59313074566474337004138971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39542049710982891336092647 59313074566474337004138971)
        ·
          refine ⟨88969611849711505506208457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59313074566474337004138971 88969611849711505506208457)
          ·
            refine ⟨66727208887283629129656343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88969611849711505506208457 66727208887283629129656343)
            ·
              refine ⟨100090813330925443694484515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66727208887283629129656343 100090813330925443694484515)
              ·
                refine ⟨150136219996388165541726773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100090813330925443694484515 150136219996388165541726773)
                ·
                  refine ⟨14075270624661390519536885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150136219996388165541726773 14075270624661390519536885)
                  ·
                    refine ⟨1319556621062005361206583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14075270624661390519536885 1319556621062005361206583)
                    ·
                      rfl

theorem cell22_3854741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3854741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854741 prefixEnd_3854741 := by exact prefixLift 3854741
  have htrace : WordTrace (prefixWord ++ tailWord_3854741) baseStart_3854741 baseEnd_3854741 := by
    simpa [prefixWord, tailWord_3854741, baseEnd_3854741] using wordTrace_append hprefix tailTrace_3854741
  have hstable : (prefixWord ++ tailWord_3854741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854741).length < 2 ^ (prefixWord ++ tailWord_3854741).sum := by decide
  have hdescent : baseEnd_3854741 < baseStart_3854741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854760 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_3854760 : Nat := 118140960795 + 3854760 * 2 ^ 59
def prefixEnd_3854760 : Nat := 4983230072969 + 3 ^ 40 * 3854760 * 2
def baseEnd_3854760 : Nat := 439854375050098548327175

theorem tailTrace_3854760 : CollatzResearch.WordTrace tailWord_3854760 prefixEnd_3854760 439854375050098548327175 := by
  unfold tailWord_3854760
  simp only [CollatzResearch.WordTrace]
  refine ⟨70297323757435167719968867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93729765009913556959958489 70297323757435167719968867)
  ·
    refine ⟨105445985636152751579953301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70297323757435167719968867 105445985636152751579953301)
    ·
      refine ⟨4942780576694660230310311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105445985636152751579953301 4942780576694660230310311)
      ·
        refine ⟨7414170865041990345465467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942780576694660230310311 7414170865041990345465467)
        ·
          refine ⟨11121256297562985518198201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7414170865041990345465467 11121256297562985518198201)
          ·
            refine ⟨8340942223172239138648651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11121256297562985518198201 8340942223172239138648651)
            ·
              refine ⟨12511413334758358707972977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340942223172239138648651 12511413334758358707972977)
              ·
                refine ⟨9383560001068769030979733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12511413334758358707972977 9383560001068769030979733)
                ·
                  refine ⟨439854375050098548327175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9383560001068769030979733 439854375050098548327175)
                  ·
                    rfl

theorem cell22_3854760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_3854760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854760 prefixEnd_3854760 := by exact prefixLift 3854760
  have htrace : WordTrace (prefixWord ++ tailWord_3854760) baseStart_3854760 baseEnd_3854760 := by
    simpa [prefixWord, tailWord_3854760, baseEnd_3854760] using wordTrace_append hprefix tailTrace_3854760
  have hstable : (prefixWord ++ tailWord_3854760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854760).length < 2 ^ (prefixWord ++ tailWord_3854760).sum := by decide
  have hdescent : baseEnd_3854760 < baseStart_3854760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854792 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_3854792 : Nat := 118140960795 + 3854792 * 2 ^ 59
def prefixEnd_3854792 : Nat := 4983230072969 + 3 ^ 40 * 3854792 * 2
def baseEnd_3854792 : Nat := 1319574079404258228181427

theorem tailTrace_3854792 : CollatzResearch.WordTrace tailWord_3854792 prefixEnd_3854792 1319574079404258228181427 := by
  unfold tailWord_3854792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70297907325377202452551315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93730543100502936603401753 70297907325377202452551315)
  ·
    refine ⟨105446860988065803678826973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70297907325377202452551315 105446860988065803678826973)
    ·
      refine ⟨39542572870524676379560115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105446860988065803678826973 39542572870524676379560115)
      ·
        refine ⟨59313859305787014569340173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39542572870524676379560115 59313859305787014569340173)
        ·
          refine ⟨22242697239670130463502565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59313859305787014569340173 22242697239670130463502565)
          ·
            refine ⟨4170505732438149461906731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22242697239670130463502565 4170505732438149461906731)
            ·
              refine ⟨6255758598657224192860097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170505732438149461906731 6255758598657224192860097)
              ·
                refine ⟨4691818948992918144645073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6255758598657224192860097 4691818948992918144645073)
                ·
                  refine ⟨3518864211744688608483805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4691818948992918144645073 3518864211744688608483805)
                  ·
                    refine ⟨1319574079404258228181427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3518864211744688608483805 1319574079404258228181427)
                    ·
                      rfl

theorem cell22_3854792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_3854792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854792 prefixEnd_3854792 := by exact prefixLift 3854792
  have htrace : WordTrace (prefixWord ++ tailWord_3854792) baseStart_3854792 baseEnd_3854792 := by
    simpa [prefixWord, tailWord_3854792, baseEnd_3854792] using wordTrace_append hprefix tailTrace_3854792
  have hstable : (prefixWord ++ tailWord_3854792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854792).length < 2 ^ (prefixWord ++ tailWord_3854792).sum := by decide
  have hdescent : baseEnd_3854792 < baseStart_3854792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854801 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_3854801 : Nat := 118140960795 + 3854801 * 2 ^ 59
def prefixEnd_3854801 : Nat := 4983230072969 + 3 ^ 40 * 3854801 * 2
def baseEnd_3854801 : Nat := 1319577160288185204706399

theorem tailTrace_3854801 : CollatzResearch.WordTrace tailWord_3854801 prefixEnd_3854801 1319577160288185204706399 := by
  unfold tailWord_3854801
  simp only [CollatzResearch.WordTrace]
  refine ⟨140596142907721799442180257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93730761938481199628120171 140596142907721799442180257)
  ·
    refine ⟨105447107180791349581635193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140596142907721799442180257 105447107180791349581635193)
    ·
      refine ⟨79085330385593512186226395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105447107180791349581635193 79085330385593512186226395)
      ·
        refine ⟨118627995578390268279339593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79085330385593512186226395 118627995578390268279339593)
        ·
          refine ⟨88970996683792701209504695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118627995578390268279339593 88970996683792701209504695)
          ·
            refine ⟨133456495025689051814257043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88970996683792701209504695 133456495025689051814257043)
            ·
              refine ⟨200184742538533577721385565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133456495025689051814257043 200184742538533577721385565)
              ·
                refine ⟨75069278451950091645519587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200184742538533577721385565 75069278451950091645519587)
                ·
                  refine ⟨112603917677925137468279381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75069278451950091645519587 112603917677925137468279381)
                  ·
                    refine ⟨1319577160288185204706399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112603917677925137468279381 1319577160288185204706399)
                    ·
                      rfl

theorem cell22_3854801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_3854801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854801 prefixEnd_3854801 := by exact prefixLift 3854801
  have htrace : WordTrace (prefixWord ++ tailWord_3854801) baseStart_3854801 baseEnd_3854801 := by
    simpa [prefixWord, tailWord_3854801, baseEnd_3854801] using wordTrace_append hprefix tailTrace_3854801
  have hstable : (prefixWord ++ tailWord_3854801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854801).length < 2 ^ (prefixWord ++ tailWord_3854801).sum := by decide
  have hdescent : baseEnd_3854801 < baseStart_3854801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854912 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 4]
def baseStart_3854912 : Nat := 118140960795 + 3854912 * 2 ^ 59
def prefixEnd_3854912 : Nat := 4983230072969 + 3 ^ 40 * 3854912 * 2
def baseEnd_3854912 : Nat := 439871719285539305060353

theorem tailTrace_3854912 : CollatzResearch.WordTrace tailWord_3854912 prefixEnd_3854912 439871719285539305060353 := by
  unfold tailWord_3854912
  simp only [CollatzResearch.WordTrace]
  refine ⟨70300095705159832699735495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93733460940213110266313993 70300095705159832699735495)
  ·
    refine ⟨105450143557739749049603243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70300095705159832699735495 105450143557739749049603243)
    ·
      refine ⟨158175215336609623574404865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105450143557739749049603243 158175215336609623574404865)
      ·
        refine ⟨118631411502457217680803649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158175215336609623574404865 118631411502457217680803649)
        ·
          refine ⟨88973558626842913260602737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118631411502457217680803649 88973558626842913260602737)
          ·
            refine ⟨66730168970132184945452053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88973558626842913260602737 66730168970132184945452053)
            ·
              refine ⟨3127976670474946169318065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66730168970132184945452053 3127976670474946169318065)
              ·
                refine ⟨2345982502856209626988549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127976670474946169318065 2345982502856209626988549)
                ·
                  refine ⟨439871719285539305060353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345982502856209626988549 439871719285539305060353)
                  ·
                    rfl

theorem cell22_3854912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_3854912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854912 prefixEnd_3854912 := by exact prefixLift 3854912
  have htrace : WordTrace (prefixWord ++ tailWord_3854912) baseStart_3854912 baseEnd_3854912 := by
    simpa [prefixWord, tailWord_3854912, baseEnd_3854912] using wordTrace_append hprefix tailTrace_3854912
  have hstable : (prefixWord ++ tailWord_3854912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854912).length < 2 ^ (prefixWord ++ tailWord_3854912).sum := by decide
  have hdescent : baseEnd_3854912 < baseStart_3854912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854923 : List Nat := [1, 1, 1, 1, 3, 1, 7, 7]
def baseStart_3854923 : Nat := 118140960795 + 3854923 * 2 ^ 59
def prefixEnd_3854923 : Nat := 4983230072969 + 3 ^ 40 * 3854923 * 2
def baseEnd_3854923 : Nat := 146624324820157505906225

theorem tailTrace_3854923 : CollatzResearch.WordTrace tailWord_3854923 prefixEnd_3854923 146624324820157505906225 := by
  unfold tailWord_3854923
  simp only [CollatzResearch.WordTrace]
  refine ⟨140600592613279814278121423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93733728408853209518747615 140600592613279814278121423)
  ·
    refine ⟨210900888919919721417182135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140600592613279814278121423 210900888919919721417182135)
    ·
      refine ⟨316351333379879582125773203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210900888919919721417182135 316351333379879582125773203)
      ·
        refine ⟨474527000069819373188659805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316351333379879582125773203 474527000069819373188659805)
        ·
          refine ⟨177947625026182264945747427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474527000069819373188659805 177947625026182264945747427)
          ·
            refine ⟨266921437539273397418621141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177947625026182264945747427 266921437539273397418621141)
            ·
              refine ⟨6255971192326720251998933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 266921437539273397418621141 6255971192326720251998933)
              ·
                refine ⟨146624324820157505906225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6255971192326720251998933 146624324820157505906225)
                ·
                  rfl

theorem cell22_3854923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 7].length) (baseStart_3854923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854923 prefixEnd_3854923 := by exact prefixLift 3854923
  have htrace : WordTrace (prefixWord ++ tailWord_3854923) baseStart_3854923 baseEnd_3854923 := by
    simpa [prefixWord, tailWord_3854923, baseEnd_3854923] using wordTrace_append hprefix tailTrace_3854923
  have hstable : (prefixWord ++ tailWord_3854923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854923).length < 2 ^ (prefixWord ++ tailWord_3854923).sum := by decide
  have hdescent : baseEnd_3854923 < baseStart_3854923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854946 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3854946 : Nat := 118140960795 + 3854946 * 2 ^ 59
def prefixEnd_3854946 : Nat := 4983230072969 + 3 ^ 40 * 3854946 * 2
def baseEnd_3854946 : Nat := 439875598917151053276985

theorem tailTrace_3854946 : CollatzResearch.WordTrace tailWord_3854946 prefixEnd_3854946 439875598917151053276985 := by
  unfold tailWord_3854946
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150357873049122301552173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93734287661464326137472461 35150357873049122301552173)
  ·
    refine ⟨13181384202393420863082065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35150357873049122301552173 13181384202393420863082065)
    ·
      refine ⟨9886038151795065647311549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13181384202393420863082065 9886038151795065647311549)
      ·
        refine ⟨3707264306923149617741831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9886038151795065647311549 3707264306923149617741831)
        ·
          refine ⟨5560896460384724426612747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707264306923149617741831 5560896460384724426612747)
          ·
            refine ⟨8341344690577086639919121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560896460384724426612747 8341344690577086639919121)
            ·
              refine ⟨6256008517932814979939341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8341344690577086639919121 6256008517932814979939341)
              ·
                refine ⟨2346003194224805617477253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6256008517932814979939341 2346003194224805617477253)
                ·
                  refine ⟨439875598917151053276985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2346003194224805617477253 439875598917151053276985)
                  ·
                    rfl

theorem cell22_3854946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3854946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854946 prefixEnd_3854946 := by exact prefixLift 3854946
  have htrace : WordTrace (prefixWord ++ tailWord_3854946) baseStart_3854946 baseEnd_3854946 := by
    simpa [prefixWord, tailWord_3854946, baseEnd_3854946] using wordTrace_append hprefix tailTrace_3854946
  have hstable : (prefixWord ++ tailWord_3854946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854946).length < 2 ^ (prefixWord ++ tailWord_3854946).sum := by decide
  have hdescent : baseEnd_3854946 < baseStart_3854946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854968 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_3854968 : Nat := 118140960795 + 3854968 * 2 ^ 59
def prefixEnd_3854968 : Nat := 4983230072969 + 3 ^ 40 * 3854968 * 2
def baseEnd_3854968 : Nat := 439878109267017478593629

theorem tailTrace_3854968 : CollatzResearch.WordTrace tailWord_3854968 prefixEnd_3854968 439878109267017478593629 := by
  unfold tailWord_3854968
  simp only [CollatzResearch.WordTrace]
  refine ⟨70301116949058393481754779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93734822598744524642339705 70301116949058393481754779)
  ·
    refine ⟨105451675423587590222632169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70301116949058393481754779 105451675423587590222632169)
    ·
      refine ⟨79088756567690692666974127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105451675423587590222632169 79088756567690692666974127)
      ·
        refine ⟨118633134851536039000461191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79088756567690692666974127 118633134851536039000461191)
        ·
          refine ⟨177949702277304058500691787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118633134851536039000461191 177949702277304058500691787)
          ·
            refine ⟨266924553415956087751037681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177949702277304058500691787 266924553415956087751037681)
            ·
              refine ⟨200193415061967065813278261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266924553415956087751037681 200193415061967065813278261)
              ·
                refine ⟨18768132662059412419994837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200193415061967065813278261 18768132662059412419994837)
                ·
                  refine ⟨439878109267017478593629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18768132662059412419994837 439878109267017478593629)
                  ·
                    rfl

theorem cell22_3854968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_3854968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854968 prefixEnd_3854968 := by exact prefixLift 3854968
  have htrace : WordTrace (prefixWord ++ tailWord_3854968) baseStart_3854968 baseEnd_3854968 := by
    simpa [prefixWord, tailWord_3854968, baseEnd_3854968] using wordTrace_append hprefix tailTrace_3854968
  have hstable : (prefixWord ++ tailWord_3854968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854968).length < 2 ^ (prefixWord ++ tailWord_3854968).sum := by decide
  have hdescent : baseEnd_3854968 < baseStart_3854968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854978 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3854978 : Nat := 118140960795 + 3854978 * 2 ^ 59
def prefixEnd_3854978 : Nat := 4983230072969 + 3 ^ 40 * 3854978 * 2
def baseEnd_3854978 : Nat := 1319637751005415743030857

theorem tailTrace_3854978 : CollatzResearch.WordTrace tailWord_3854978 prefixEnd_3854978 1319637751005415743030857 := by
  unfold tailWord_3854978
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150649657020139667843397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93735065752053705780915725 35150649657020139667843397)
  ·
    refine ⟨6590746810691276187720637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35150649657020139667843397 6590746810691276187720637)
    ·
      refine ⟨2471530054009228570395239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6590746810691276187720637 2471530054009228570395239)
      ·
        refine ⟨3707295081013842855592859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471530054009228570395239 3707295081013842855592859)
        ·
          refine ⟨5560942621520764283389289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707295081013842855592859 5560942621520764283389289)
          ·
            refine ⟨4170706966140573212541967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5560942621520764283389289 4170706966140573212541967)
            ·
              refine ⟨6256060449210859818812951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170706966140573212541967 6256060449210859818812951)
              ·
                refine ⟨9384090673816289728219427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256060449210859818812951 9384090673816289728219427)
                ·
                  refine ⟨14076136010724434592329141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9384090673816289728219427 14076136010724434592329141)
                  ·
                    refine ⟨1319637751005415743030857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14076136010724434592329141 1319637751005415743030857)
                    ·
                      rfl

theorem cell22_3854978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3854978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3854978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3854978 prefixEnd_3854978 := by exact prefixLift 3854978
  have htrace : WordTrace (prefixWord ++ tailWord_3854978) baseStart_3854978 baseEnd_3854978 := by
    simpa [prefixWord, tailWord_3854978, baseEnd_3854978] using wordTrace_append hprefix tailTrace_3854978
  have hstable : (prefixWord ++ tailWord_3854978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854978).length < 2 ^ (prefixWord ++ tailWord_3854978).sum := by decide
  have hdescent : baseEnd_3854978 < baseStart_3854978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855075 : List Nat := [1, 1, 1, 7, 1, 11]
def baseStart_3855075 : Nat := 118140960795 + 3855075 * 2 ^ 59
def prefixEnd_3855075 : Nat := 4983230072969 + 3 ^ 40 * 3855075 * 2
def baseEnd_3855075 : Nat := 16292234025774565720439

theorem tailTrace_3855075 : CollatzResearch.WordTrace tailWord_3855075 prefixEnd_3855075 16292234025774565720439 := by
  unfold tailWord_3855075
  simp only [CollatzResearch.WordTrace]
  refine ⟨140606136508729144237654679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93737424339152762825103119 140606136508729144237654679)
  ·
    refine ⟨210909204763093716356482019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140606136508729144237654679 210909204763093716356482019)
    ·
      refine ⟨316363807144640574534723029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210909204763093716356482019 316363807144640574534723029)
      ·
        refine ⟨7414776729952513465657571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 316363807144640574534723029 7414776729952513465657571)
        ·
          refine ⟨11122165094928770198486357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7414776729952513465657571 11122165094928770198486357)
          ·
            refine ⟨16292234025774565720439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11122165094928770198486357 16292234025774565720439)
            ·
              rfl

theorem cell22_3855075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 11].length) (baseStart_3855075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855075 prefixEnd_3855075 := by exact prefixLift 3855075
  have htrace : WordTrace (prefixWord ++ tailWord_3855075) baseStart_3855075 baseEnd_3855075 := by
    simpa [prefixWord, tailWord_3855075, baseEnd_3855075] using wordTrace_append hprefix tailTrace_3855075
  have hstable : (prefixWord ++ tailWord_3855075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855075).length < 2 ^ (prefixWord ++ tailWord_3855075).sum := by decide
  have hdescent : baseEnd_3855075 < baseStart_3855075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855077 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_3855077 : Nat := 118140960795 + 3855077 * 2 ^ 59
def prefixEnd_3855077 : Nat := 4983230072969 + 3 ^ 40 * 3855077 * 2
def baseEnd_3855077 : Nat := 1319671640728612484805553

theorem tailTrace_3855077 : CollatzResearch.WordTrace tailWord_3855077 prefixEnd_3855077 1319671640728612484805553 := by
  unfold tailWord_3855077
  simp only [CollatzResearch.WordTrace]
  refine ⟨140606209454721898579227485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93737472969814599052818323 140606209454721898579227485)
  ·
    refine ⟨52727328545520711967210307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140606209454721898579227485 52727328545520711967210307)
    ·
      refine ⟨79090992818281067950815461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52727328545520711967210307 79090992818281067950815461)
      ·
        refine ⟨14829561153427700240777899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79090992818281067950815461 14829561153427700240777899)
        ·
          refine ⟨22244341730141550361166849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14829561153427700240777899 22244341730141550361166849)
          ·
            refine ⟨16683256297606162770875137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22244341730141550361166849 16683256297606162770875137)
            ·
              refine ⟨12512442223204622078156353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16683256297606162770875137 12512442223204622078156353)
              ·
                refine ⟨9384331667403466558617265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12512442223204622078156353 9384331667403466558617265)
                ·
                  refine ⟨7038248750552599918962949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9384331667403466558617265 7038248750552599918962949)
                  ·
                    refine ⟨1319671640728612484805553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038248750552599918962949 1319671640728612484805553)
                    ·
                      rfl

theorem cell22_3855077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_3855077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855077 prefixEnd_3855077 := by exact prefixLift 3855077
  have htrace : WordTrace (prefixWord ++ tailWord_3855077) baseStart_3855077 baseEnd_3855077 := by
    simpa [prefixWord, tailWord_3855077, baseEnd_3855077] using wordTrace_append hprefix tailTrace_3855077
  have hstable : (prefixWord ++ tailWord_3855077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855077).length < 2 ^ (prefixWord ++ tailWord_3855077).sum := by decide
  have hdescent : baseEnd_3855077 < baseStart_3855077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855105 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3855105 : Nat := 118140960795 + 3855105 * 2 ^ 59
def prefixEnd_3855105 : Nat := 4983230072969 + 3 ^ 40 * 3855105 * 2
def baseEnd_3855105 : Nat := 1319681225700829745105467

theorem tailTrace_3855105 : CollatzResearch.WordTrace tailWord_3855105 prefixEnd_3855105 1319681225700829745105467 := by
  unfold tailWord_3855105
  simp only [CollatzResearch.WordTrace]
  refine ⟨140607230698620459361246769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93738153799080306240831179 140607230698620459361246769)
  ·
    refine ⟨105455423023965344520935077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140607230698620459361246769 105455423023965344520935077)
    ·
      refine ⟨19772891816993502097675327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105455423023965344520935077 19772891816993502097675327)
      ·
        refine ⟨29659337725490253146512991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19772891816993502097675327 29659337725490253146512991)
        ·
          refine ⟨44489006588235379719769487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29659337725490253146512991 44489006588235379719769487)
          ·
            refine ⟨66733509882353069579654231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44489006588235379719769487 66733509882353069579654231)
            ·
              refine ⟨100100264823529604369481347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66733509882353069579654231 100100264823529604369481347)
              ·
                refine ⟨150150397235294406554222021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100100264823529604369481347 150150397235294406554222021)
                ·
                  refine ⟨28153199481617701228916629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150150397235294406554222021 28153199481617701228916629)
                  ·
                    refine ⟨1319681225700829745105467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28153199481617701228916629 1319681225700829745105467)
                    ·
                      rfl

theorem cell22_3855105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3855105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855105 prefixEnd_3855105 := by exact prefixLift 3855105
  have htrace : WordTrace (prefixWord ++ tailWord_3855105) baseStart_3855105 baseEnd_3855105 := by
    simpa [prefixWord, tailWord_3855105, baseEnd_3855105] using wordTrace_append hprefix tailTrace_3855105
  have hstable : (prefixWord ++ tailWord_3855105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855105).length < 2 ^ (prefixWord ++ tailWord_3855105).sum := by decide
  have hdescent : baseEnd_3855105 < baseStart_3855105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855154 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_3855154 : Nat := 118140960795 + 3855154 * 2 ^ 59
def prefixEnd_3855154 : Nat := 4983230072969 + 3 ^ 40 * 3855154 * 2
def baseEnd_3855154 : Nat := 439899333134069983543439

theorem tailTrace_3855154 : CollatzResearch.WordTrace tailWord_3855154 prefixEnd_3855154 439899333134069983543439 := by
  unfold tailWord_3855154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35152254468860735182445129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93739345250295293819853677 35152254468860735182445129)
  ·
    refine ⟨26364190851645551386833847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35152254468860735182445129 26364190851645551386833847)
    ·
      refine ⟨39546286277468327080250771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26364190851645551386833847 39546286277468327080250771)
      ·
        refine ⟨59319429416202490620376157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39546286277468327080250771 59319429416202490620376157)
        ·
          refine ⟨22244786031075933982641059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59319429416202490620376157 22244786031075933982641059)
          ·
            refine ⟨33367179046613900973961589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22244786031075933982641059 33367179046613900973961589)
            ·
              refine ⟨3128173035620053216308899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33367179046613900973961589 3128173035620053216308899)
              ·
                refine ⟨4692259553430079824463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128173035620053216308899 4692259553430079824463349)
                ·
                  refine ⟨439899333134069983543439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4692259553430079824463349 439899333134069983543439)
                  ·
                    rfl

theorem cell22_3855154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_3855154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855154 prefixEnd_3855154 := by exact prefixLift 3855154
  have htrace : WordTrace (prefixWord ++ tailWord_3855154) baseStart_3855154 baseEnd_3855154 := by
    simpa [prefixWord, tailWord_3855154, baseEnd_3855154] using wordTrace_append hprefix tailTrace_3855154
  have hstable : (prefixWord ++ tailWord_3855154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855154).length < 2 ^ (prefixWord ++ tailWord_3855154).sum := by decide
  have hdescent : baseEnd_3855154 < baseStart_3855154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855212 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_3855212 : Nat := 118140960795 + 3855212 * 2 ^ 59
def prefixEnd_3855212 : Nat := 4983230072969 + 3 ^ 40 * 3855212 * 2
def baseEnd_3855212 : Nat := 1319717853987517132680139

theorem tailTrace_3855212 : CollatzResearch.WordTrace tailWord_3855212 prefixEnd_3855212 1319717853987517132680139 := by
  unfold tailWord_3855212
  simp only [CollatzResearch.WordTrace]
  refine ⟨70305566654616408317695945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93740755539488544423594593 70305566654616408317695945)
  ·
    refine ⟨52729174990962306238271959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70305566654616408317695945 52729174990962306238271959)
    ·
      refine ⟨79093762486443459357407939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52729174990962306238271959 79093762486443459357407939)
      ·
        refine ⟨118640643729665189036111909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79093762486443459357407939 118640643729665189036111909)
        ·
          refine ⟨22245120699312222944270983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118640643729665189036111909 22245120699312222944270983)
          ·
            refine ⟨33367681048968334416406475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22245120699312222944270983 33367681048968334416406475)
            ·
              refine ⟨50051521573452501624609713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33367681048968334416406475 50051521573452501624609713)
              ·
                refine ⟨37538641180089376218457285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50051521573452501624609713 37538641180089376218457285)
                ·
                  refine ⟨7038495221266758040960741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37538641180089376218457285 7038495221266758040960741)
                  ·
                    refine ⟨1319717853987517132680139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038495221266758040960741 1319717853987517132680139)
                    ·
                      rfl

theorem cell22_3855212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_3855212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855212 prefixEnd_3855212 := by exact prefixLift 3855212
  have htrace : WordTrace (prefixWord ++ tailWord_3855212) baseStart_3855212 baseEnd_3855212 := by
    simpa [prefixWord, tailWord_3855212, baseEnd_3855212] using wordTrace_append hprefix tailTrace_3855212
  have hstable : (prefixWord ++ tailWord_3855212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855212).length < 2 ^ (prefixWord ++ tailWord_3855212).sum := by decide
  have hdescent : baseEnd_3855212 < baseStart_3855212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855250 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3855250 : Nat := 118140960795 + 3855250 * 2 ^ 59
def prefixEnd_3855250 : Nat := 4983230072969 + 3 ^ 40 * 3855250 * 2
def baseEnd_3855250 : Nat := 439910287388032566743341

theorem tailTrace_3855250 : CollatzResearch.WordTrace tailWord_3855250 prefixEnd_3855250 439910287388032566743341 := by
  unfold tailWord_3855250
  simp only [CollatzResearch.WordTrace]
  refine ⟨35153129820773787281318801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93741679522063432750183469 35153129820773787281318801)
  ·
    refine ⟨26364847365580340460989101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35153129820773787281318801 26364847365580340460989101)
    ·
      refine ⟨9886817762092627672870913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26364847365580340460989101 9886817762092627672870913)
      ·
        refine ⟨7415113321569470754653185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9886817762092627672870913 7415113321569470754653185)
        ·
          refine ⟨5561334991177103065989889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7415113321569470754653185 5561334991177103065989889)
          ·
            refine ⟨4171001243382827299492417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5561334991177103065989889 4171001243382827299492417)
            ·
              refine ⟨3128250932537120474619313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4171001243382827299492417 3128250932537120474619313)
              ·
                refine ⟨2346188199402840355964485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128250932537120474619313 2346188199402840355964485)
                ·
                  refine ⟨439910287388032566743341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2346188199402840355964485 439910287388032566743341)
                  ·
                    rfl

theorem cell22_3855250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3855250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855250 prefixEnd_3855250 := by exact prefixLift 3855250
  have htrace : WordTrace (prefixWord ++ tailWord_3855250) baseStart_3855250 baseEnd_3855250 := by
    simpa [prefixWord, tailWord_3855250, baseEnd_3855250] using wordTrace_append hprefix tailTrace_3855250
  have hstable : (prefixWord ++ tailWord_3855250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855250).length < 2 ^ (prefixWord ++ tailWord_3855250).sum := by decide
  have hdescent : baseEnd_3855250 < baseStart_3855250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855368 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 4]
def baseStart_3855368 : Nat := 118140960795 + 3855368 * 2 ^ 59
def prefixEnd_3855368 : Nat := 4983230072969 + 3 ^ 40 * 3855368 * 2
def baseEnd_3855368 : Nat := 439923751991861575259887

theorem tailTrace_3855368 : CollatzResearch.WordTrace tailWord_3855368 prefixEnd_3855368 439923751991861575259887 := by
  unfold tailWord_3855368
  simp only [CollatzResearch.WordTrace]
  refine ⟨70308411548333827639035379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93744548731111770185380505 70308411548333827639035379)
  ·
    refine ⟨105462617322500741458553069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70308411548333827639035379 105462617322500741458553069)
    ·
      refine ⟨39548481495937778046957401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105462617322500741458553069 39548481495937778046957401)
      ·
        refine ⟨29661361121953333535218051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39548481495937778046957401 29661361121953333535218051)
        ·
          refine ⟨44492041682930000302827077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29661361121953333535218051 44492041682930000302827077)
          ·
            refine ⟨8342257815549375056780077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44492041682930000302827077 8342257815549375056780077)
            ·
              refine ⟨3128346680831015646292529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8342257815549375056780077 3128346680831015646292529)
              ·
                refine ⟨2346260010623261734719397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128346680831015646292529 2346260010623261734719397)
                ·
                  refine ⟨439923751991861575259887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2346260010623261734719397 439923751991861575259887)
                  ·
                    rfl

theorem cell22_3855368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_3855368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855368 prefixEnd_3855368 := by exact prefixLift 3855368
  have htrace : WordTrace (prefixWord ++ tailWord_3855368) baseStart_3855368 baseEnd_3855368 := by
    simpa [prefixWord, tailWord_3855368, baseEnd_3855368] using wordTrace_append hprefix tailTrace_3855368
  have hstable : (prefixWord ++ tailWord_3855368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855368).length < 2 ^ (prefixWord ++ tailWord_3855368).sum := by decide
  have hdescent : baseEnd_3855368 < baseStart_3855368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855383 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 2, 3]
def baseStart_3855383 : Nat := 118140960795 + 3855383 * 2 ^ 59
def prefixEnd_3855383 : Nat := 4983230072969 + 3 ^ 40 * 3855383 * 2
def baseEnd_3855383 : Nat := 1319776390782129686654615

theorem tailTrace_3855383 : CollatzResearch.WordTrace tailWord_3855383 prefixEnd_3855383 1319776390782129686654615 := by
  unfold tailWord_3855383
  simp only [CollatzResearch.WordTrace]
  refine ⟨140617370191613312839866803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93744913461075541893244535 140617370191613312839866803)
  ·
    refine ⟨210926055287419969259800205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140617370191613312839866803 210926055287419969259800205)
    ·
      refine ⟨79097270732782488472425077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210926055287419969259800205 79097270732782488472425077)
      ·
        refine ⟨7415369131198358294289851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79097270732782488472425077 7415369131198358294289851)
        ·
          refine ⟨11123053696797537441434777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415369131198358294289851 11123053696797537441434777)
          ·
            refine ⟨8342290272598153081076083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11123053696797537441434777 8342290272598153081076083)
            ·
              refine ⟨12513435408897229621614125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342290272598153081076083 12513435408897229621614125)
              ·
                refine ⟨4692538278336461108105297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12513435408897229621614125 4692538278336461108105297)
                ·
                  refine ⟨3519403708752345831078973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4692538278336461108105297 3519403708752345831078973)
                  ·
                    refine ⟨1319776390782129686654615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519403708752345831078973 1319776390782129686654615)
                    ·
                      rfl

theorem cell22_3855383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_3855383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855383 prefixEnd_3855383 := by exact prefixLift 3855383
  have htrace : WordTrace (prefixWord ++ tailWord_3855383) baseStart_3855383 baseEnd_3855383 := by
    simpa [prefixWord, tailWord_3855383, baseEnd_3855383] using wordTrace_append hprefix tailTrace_3855383
  have hstable : (prefixWord ++ tailWord_3855383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855383).length < 2 ^ (prefixWord ++ tailWord_3855383).sum := by decide
  have hdescent : baseEnd_3855383 < baseStart_3855383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855471 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 1, 4]
def baseStart_3855471 : Nat := 118140960795 + 3855471 * 2 ^ 59
def prefixEnd_3855471 : Nat := 4983230072969 + 3 ^ 40 * 3855471 * 2
def baseEnd_3855471 : Nat := 1319806514980526790454345

theorem tailTrace_3855471 : CollatzResearch.WordTrace tailWord_3855471 prefixEnd_3855471 1319806514980526790454345 := by
  unfold tailWord_3855471
  simp only [CollatzResearch.WordTrace]
  refine ⟨140620579815294503869070267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93747053210196335912713511 140620579815294503869070267)
  ·
    refine ⟨210930869722941755803605401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140620579815294503869070267 210930869722941755803605401)
    ·
      refine ⟨158198152292206316852704051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210930869722941755803605401 158198152292206316852704051)
      ·
        refine ⟨237297228438309475279056077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158198152292206316852704051 237297228438309475279056077)
        ·
          refine ⟨88986460664366053229646029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237297228438309475279056077 88986460664366053229646029)
          ·
            refine ⟨33369922749137269961117261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88986460664366053229646029 33369922749137269961117261)
            ·
              refine ⟨12513721030926476235418973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33369922749137269961117261 12513721030926476235418973)
              ·
                refine ⟨4692645386597428588282115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12513721030926476235418973 4692645386597428588282115)
                ·
                  refine ⟨7038968079896142882423173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692645386597428588282115 7038968079896142882423173)
                  ·
                    refine ⟨1319806514980526790454345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038968079896142882423173 1319806514980526790454345)
                    ·
                      rfl

theorem cell22_3855471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_3855471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855471 prefixEnd_3855471 := by exact prefixLift 3855471
  have htrace : WordTrace (prefixWord ++ tailWord_3855471) baseStart_3855471 baseEnd_3855471 := by
    simpa [prefixWord, tailWord_3855471, baseEnd_3855471] using wordTrace_append hprefix tailTrace_3855471
  have hstable : (prefixWord ++ tailWord_3855471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855471).length < 2 ^ (prefixWord ++ tailWord_3855471).sum := by decide
  have hdescent : baseEnd_3855471 < baseStart_3855471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855516 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3855516 : Nat := 118140960795 + 3855516 * 2 ^ 59
def prefixEnd_3855516 : Nat := 4983230072969 + 3 ^ 40 * 3855516 * 2
def baseEnd_3855516 : Nat := 1319821919400161673079207

theorem tailTrace_3855516 : CollatzResearch.WordTrace tailWord_3855516 prefixEnd_3855516 1319821919400161673079207 := by
  unfold tailWord_3855516
  simp only [CollatzResearch.WordTrace]
  refine ⟨70311110550065738277229201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93748147400087651036305601 70311110550065738277229201)
  ·
    refine ⟨52733332912549303707921901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70311110550065738277229201 52733332912549303707921901)
    ·
      refine ⟨19774999842205988890470713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52733332912549303707921901 19774999842205988890470713)
      ·
        refine ⟨14831249881654491667853035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19774999842205988890470713 14831249881654491667853035)
        ·
          refine ⟨22246874822481737501779553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831249881654491667853035 22246874822481737501779553)
          ·
            refine ⟨16685156116861303126334665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22246874822481737501779553 16685156116861303126334665)
            ·
              refine ⟨12513867087645977344750999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16685156116861303126334665 12513867087645977344750999)
              ·
                refine ⟨18770800631468966017126499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513867087645977344750999 18770800631468966017126499)
                ·
                  refine ⟨28156200947203449025689749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18770800631468966017126499 28156200947203449025689749)
                  ·
                    refine ⟨1319821919400161673079207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28156200947203449025689749 1319821919400161673079207)
                    ·
                      rfl

theorem cell22_3855516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3855516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855516 prefixEnd_3855516 := by exact prefixLift 3855516
  have htrace : WordTrace (prefixWord ++ tailWord_3855516) baseStart_3855516 baseEnd_3855516 := by
    simpa [prefixWord, tailWord_3855516, baseEnd_3855516] using wordTrace_append hprefix tailTrace_3855516
  have hstable : (prefixWord ++ tailWord_3855516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855516).length < 2 ^ (prefixWord ++ tailWord_3855516).sum := by decide
  have hdescent : baseEnd_3855516 < baseStart_3855516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855552 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 2, 3]
def baseStart_3855552 : Nat := 118140960795 + 3855552 * 2 ^ 59
def prefixEnd_3855552 : Nat := 4983230072969 + 3 ^ 40 * 3855552 * 2
def baseEnd_3855552 : Nat := 1319834242935869579179097

theorem tailTrace_3855552 : CollatzResearch.WordTrace tailWord_3855552 prefixEnd_3855552 1319834242935869579179097 := by
  unfold tailWord_3855552
  simp only [CollatzResearch.WordTrace]
  refine ⟨70311767064000527351384455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93749022752000703135179273 70311767064000527351384455)
  ·
    refine ⟨105467650596000791027076683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70311767064000527351384455 105467650596000791027076683)
    ·
      refine ⟨158201475894001186540615025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105467650596000791027076683 158201475894001186540615025)
      ·
        refine ⟨118651106920500889905461269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158201475894001186540615025 118651106920500889905461269)
        ·
          refine ⟨5561770636898479214318497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118651106920500889905461269 5561770636898479214318497)
          ·
            refine ⟨4171327977673859410738873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5561770636898479214318497 4171327977673859410738873)
            ·
              refine ⟨3128495983255394558054155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4171327977673859410738873 3128495983255394558054155)
              ·
                refine ⟨4692743974883091837081233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128495983255394558054155 4692743974883091837081233)
                ·
                  refine ⟨3519557981162318877810925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4692743974883091837081233 3519557981162318877810925)
                  ·
                    refine ⟨1319834242935869579179097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519557981162318877810925 1319834242935869579179097)
                    ·
                      rfl

theorem cell22_3855552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_3855552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855552 prefixEnd_3855552 := by exact prefixLift 3855552
  have htrace : WordTrace (prefixWord ++ tailWord_3855552) baseStart_3855552 baseEnd_3855552 := by
    simpa [prefixWord, tailWord_3855552, baseEnd_3855552] using wordTrace_append hprefix tailTrace_3855552
  have hstable : (prefixWord ++ tailWord_3855552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855552).length < 2 ^ (prefixWord ++ tailWord_3855552).sum := by decide
  have hdescent : baseEnd_3855552 < baseStart_3855552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855597 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_3855597 : Nat := 118140960795 + 3855597 * 2 ^ 59
def prefixEnd_3855597 : Nat := 4983230072969 + 3 ^ 40 * 3855597 * 2
def baseEnd_3855597 : Nat := 1319849647355504461803959

theorem tailTrace_3855597 : CollatzResearch.WordTrace tailWord_3855597 prefixEnd_3855597 1319849647355504461803959 := by
  unfold tailWord_3855597
  simp only [CollatzResearch.WordTrace]
  refine ⟨140625175412838027388157045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93750116941892018258771363 140625175412838027388157045)
  ·
    refine ⟨13183610194953565067639723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140625175412838027388157045 13183610194953565067639723)
    ·
      refine ⟨19775415292430347601459585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13183610194953565067639723 19775415292430347601459585)
      ·
        refine ⟨14831561469322760701094689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19775415292430347601459585 14831561469322760701094689)
        ·
          refine ⟨11123671101992070525821017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14831561469322760701094689 11123671101992070525821017)
          ·
            refine ⟨8342753326494052894365763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11123671101992070525821017 8342753326494052894365763)
            ·
              refine ⟨12514129989741079341548645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342753326494052894365763 12514129989741079341548645)
              ·
                refine ⟨2346399373076452376540371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12514129989741079341548645 2346399373076452376540371)
                ·
                  refine ⟨3519599059614678564810557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346399373076452376540371 3519599059614678564810557)
                  ·
                    refine ⟨1319849647355504461803959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519599059614678564810557 1319849647355504461803959)
                    ·
                      rfl

theorem cell22_3855597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_3855597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855597 prefixEnd_3855597 := by exact prefixLift 3855597
  have htrace : WordTrace (prefixWord ++ tailWord_3855597) baseStart_3855597 baseEnd_3855597 := by
    simpa [prefixWord, tailWord_3855597, baseEnd_3855597] using wordTrace_append hprefix tailTrace_3855597
  have hstable : (prefixWord ++ tailWord_3855597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855597).length < 2 ^ (prefixWord ++ tailWord_3855597).sum := by decide
  have hdescent : baseEnd_3855597 < baseStart_3855597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855621 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 6]
def baseStart_3855621 : Nat := 118140960795 + 3855621 * 2 ^ 59
def prefixEnd_3855621 : Nat := 4983230072969 + 3 ^ 40 * 3855621 * 2
def baseEnd_3855621 : Nat := 439952621015325466401295

theorem tailTrace_3855621 : CollatzResearch.WordTrace tailWord_3855621 prefixEnd_3855621 439952621015325466401295 := by
  unfold tailWord_3855621
  simp only [CollatzResearch.WordTrace]
  refine ⟨140626050764751079487030717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93750700509834052991353811 140626050764751079487030717)
  ·
    refine ⟨52734769036781654807636519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140626050764751079487030717 52734769036781654807636519)
    ·
      refine ⟨79102153555172482211454779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52734769036781654807636519 79102153555172482211454779)
      ·
        refine ⟨118653230332758723317182169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79102153555172482211454779 118653230332758723317182169)
        ·
          refine ⟨88989922749569042487886627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118653230332758723317182169 88989922749569042487886627)
          ·
            refine ⟨133484884124353563731829941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88989922749569042487886627 133484884124353563731829941)
            ·
              refine ⟨12514207886658146599859057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133484884124353563731829941 12514207886658146599859057)
              ·
                refine ⟨9385655914993609949894293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12514207886658146599859057 9385655914993609949894293)
                ·
                  refine ⟨439952621015325466401295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9385655914993609949894293 439952621015325466401295)
                  ·
                    rfl

theorem cell22_3855621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_3855621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855621 prefixEnd_3855621 := by exact prefixLift 3855621
  have htrace : WordTrace (prefixWord ++ tailWord_3855621) baseStart_3855621 baseEnd_3855621 := by
    simpa [prefixWord, tailWord_3855621, baseEnd_3855621] using wordTrace_append hprefix tailTrace_3855621
  have hstable : (prefixWord ++ tailWord_3855621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855621).length < 2 ^ (prefixWord ++ tailWord_3855621).sum := by decide
  have hdescent : baseEnd_3855621 < baseStart_3855621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855640 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 1, 4]
def baseStart_3855640 : Nat := 118140960795 + 3855640 * 2 ^ 59
def prefixEnd_3855640 : Nat := 4983230072969 + 3 ^ 40 * 3855640 * 2
def baseEnd_3855640 : Nat := 1319864367134266682978827

theorem tailTrace_3855640 : CollatzResearch.WordTrace tailWord_3855640 prefixEnd_3855640 1319864367134266682978827 := by
  unfold tailWord_3855640
  simp only [CollatzResearch.WordTrace]
  refine ⟨70313371875841122865986187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93751162501121497154648249 70313371875841122865986187)
  ·
    refine ⟨105470057813761684298979281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70313371875841122865986187 105470057813761684298979281)
    ·
      refine ⟨79102543360321263224234461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105470057813761684298979281 79102543360321263224234461)
      ·
        refine ⟨29663453760120473709087923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79102543360321263224234461 29663453760120473709087923)
        ·
          refine ⟨44495180640180710563631885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29663453760120473709087923 44495180640180710563631885)
          ·
            refine ⟨16685692740067766461361957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44495180640180710563631885 16685692740067766461361957)
            ·
              refine ⟨3128567388762706211505367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16685692740067766461361957 3128567388762706211505367)
              ·
                refine ⟨4692851083144059317258051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128567388762706211505367 4692851083144059317258051)
                ·
                  refine ⟨7039276624716088975887077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692851083144059317258051 7039276624716088975887077)
                  ·
                    refine ⟨1319864367134266682978827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039276624716088975887077 1319864367134266682978827)
                    ·
                      rfl

theorem cell22_3855640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_3855640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855640 prefixEnd_3855640 := by exact prefixLift 3855640
  have htrace : WordTrace (prefixWord ++ tailWord_3855640) baseStart_3855640 baseEnd_3855640 := by
    simpa [prefixWord, tailWord_3855640, baseEnd_3855640] using wordTrace_append hprefix tailTrace_3855640
  have hstable : (prefixWord ++ tailWord_3855640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855640).length < 2 ^ (prefixWord ++ tailWord_3855640).sum := by decide
  have hdescent : baseEnd_3855640 < baseStart_3855640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855668 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3855668 : Nat := 118140960795 + 3855668 * 2 ^ 59
def prefixEnd_3855668 : Nat := 4983230072969 + 3 ^ 40 * 3855668 * 2
def baseEnd_3855668 : Nat := 1319873952106483943278741

theorem tailTrace_3855668 : CollatzResearch.WordTrace tailWord_3855668 prefixEnd_3855668 1319873952106483943278741 := by
  unfold tailWord_3855668
  simp only [CollatzResearch.WordTrace]
  refine ⟨70313882497790403256995829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93751843330387204342661105 70313882497790403256995829)
  ·
    refine ⟨6591926484167850305343359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70313882497790403256995829 6591926484167850305343359)
    ·
      refine ⟨9887889726251775458015039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591926484167850305343359 9887889726251775458015039)
      ·
        refine ⟨14831834589377663187022559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887889726251775458015039 14831834589377663187022559)
        ·
          refine ⟨22247751884066494780533839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831834589377663187022559 22247751884066494780533839)
          ·
            refine ⟨33371627826099742170800759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22247751884066494780533839 33371627826099742170800759)
            ·
              refine ⟨50057441739149613256201139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33371627826099742170800759 50057441739149613256201139)
              ·
                refine ⟨75086162608724419884301709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50057441739149613256201139 75086162608724419884301709)
                ·
                  refine ⟨28157310978271657456613141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75086162608724419884301709 28157310978271657456613141)
                  ·
                    refine ⟨1319873952106483943278741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28157310978271657456613141 1319873952106483943278741)
                    ·
                      rfl

theorem cell22_3855668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3855668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855668 prefixEnd_3855668 := by exact prefixLift 3855668
  have htrace : WordTrace (prefixWord ++ tailWord_3855668) baseStart_3855668 baseEnd_3855668 := by
    simpa [prefixWord, tailWord_3855668, baseEnd_3855668] using wordTrace_append hprefix tailTrace_3855668
  have hstable : (prefixWord ++ tailWord_3855668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855668).length < 2 ^ (prefixWord ++ tailWord_3855668).sum := by decide
  have hdescent : baseEnd_3855668 < baseStart_3855668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855715 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 3, 3]
def baseStart_3855715 : Nat := 118140960795 + 3855715 * 2 ^ 59
def prefixEnd_3855715 : Nat := 4983230072969 + 3 ^ 40 * 3855715 * 2
def baseEnd_3855715 : Nat := 1319890041166991487353597

theorem tailTrace_3855715 : CollatzResearch.WordTrace tailWord_3855715 prefixEnd_3855715 1319890041166991487353597 := by
  unfold tailWord_3855715
  simp only [CollatzResearch.WordTrace]
  refine ⟨140629479226410533540952599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93752986150940355693968399 140629479226410533540952599)
  ·
    refine ⟨210944218839615800311428899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140629479226410533540952599 210944218839615800311428899)
    ·
      refine ⟨316416328259423700467143349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210944218839615800311428899 316416328259423700467143349)
      ·
        refine ⟨29664030774320971918794689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316416328259423700467143349 29664030774320971918794689)
        ·
          refine ⟨22248023080740728939096017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29664030774320971918794689 22248023080740728939096017)
          ·
            refine ⟨16686017310555546704322013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22248023080740728939096017 16686017310555546704322013)
            ·
              refine ⟨6257256491458330014120755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16686017310555546704322013 6257256491458330014120755)
              ·
                refine ⟨9385884737187495021181133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257256491458330014120755 9385884737187495021181133)
                ·
                  refine ⟨3519706776445310632942925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9385884737187495021181133 3519706776445310632942925)
                  ·
                    refine ⟨1319890041166991487353597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519706776445310632942925 1319890041166991487353597)
                    ·
                      rfl

theorem cell22_3855715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 3].length) (baseStart_3855715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855715 prefixEnd_3855715 := by exact prefixLift 3855715
  have htrace : WordTrace (prefixWord ++ tailWord_3855715) baseStart_3855715 baseEnd_3855715 := by
    simpa [prefixWord, tailWord_3855715, baseEnd_3855715] using wordTrace_append hprefix tailTrace_3855715
  have hstable : (prefixWord ++ tailWord_3855715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855715).length < 2 ^ (prefixWord ++ tailWord_3855715).sum := by decide
  have hdescent : baseEnd_3855715 < baseStart_3855715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855728 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_3855728 : Nat := 118140960795 + 3855728 * 2 ^ 59
def prefixEnd_3855728 : Nat := 4983230072969 + 3 ^ 40 * 3855728 * 2
def baseEnd_3855728 : Nat := 439964830444221262259519

theorem tailTrace_3855728 : CollatzResearch.WordTrace tailWord_3855728 prefixEnd_3855728 439964830444221262259519 := by
  unfold tailWord_3855728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70314976687681718380587919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93753302250242291174117225 70314976687681718380587919)
  ·
    refine ⟨105472465031522577570881879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70314976687681718380587919 105472465031522577570881879)
    ·
      refine ⟨158208697547283866356322819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105472465031522577570881879 158208697547283866356322819)
      ·
        refine ⟨237313046320925799534484229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158208697547283866356322819 237313046320925799534484229)
        ·
          refine ⟨44496196185173587412715793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237313046320925799534484229 44496196185173587412715793)
          ·
            refine ⟨33372147138880190559536845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44496196185173587412715793 33372147138880190559536845)
            ·
              refine ⟨12514555177080071459826317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33372147138880190559536845 12514555177080071459826317)
              ·
                refine ⟨4692958191405026797434869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12514555177080071459826317 4692958191405026797434869)
                ·
                  refine ⟨439964830444221262259519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4692958191405026797434869 439964830444221262259519)
                  ·
                    rfl

theorem cell22_3855728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_3855728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855728 prefixEnd_3855728 := by exact prefixLift 3855728
  have htrace : WordTrace (prefixWord ++ tailWord_3855728) baseStart_3855728 baseEnd_3855728 := by
    simpa [prefixWord, tailWord_3855728, baseEnd_3855728] using wordTrace_append hprefix tailTrace_3855728
  have hstable : (prefixWord ++ tailWord_3855728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855728).length < 2 ^ (prefixWord ++ tailWord_3855728).sum := by decide
  have hdescent : baseEnd_3855728 < baseStart_3855728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855788 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_3855788 : Nat := 118140960795 + 3855788 * 2 ^ 59
def prefixEnd_3855788 : Nat := 4983230072969 + 3 ^ 40 * 3855788 * 2
def baseEnd_3855788 : Nat := 1319915030558843630278373

theorem tailTrace_3855788 : CollatzResearch.WordTrace tailWord_3855788 prefixEnd_3855788 1319915030558843630278373 := by
  unfold tailWord_3855788
  simp only [CollatzResearch.WordTrace]
  refine ⟨70316070877573033504180009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93754761170097378005573345 70316070877573033504180009)
  ·
    refine ⟨52737053158179775128135007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70316070877573033504180009 52737053158179775128135007)
    ·
      refine ⟨79105579737269662692202511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52737053158179775128135007 79105579737269662692202511)
      ·
        refine ⟨118658369605904494038303767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79105579737269662692202511 118658369605904494038303767)
        ·
          refine ⟨177987554408856741057455651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118658369605904494038303767 177987554408856741057455651)
          ·
            refine ⟨266981331613285111586183477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177987554408856741057455651 266981331613285111586183477)
            ·
              refine ⟨25029499838745479211204701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266981331613285111586183477 25029499838745479211204701)
              ·
                refine ⟨9386062439529554704201763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25029499838745479211204701 9386062439529554704201763)
                ·
                  refine ⟨14079093659294332056302645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9386062439529554704201763 14079093659294332056302645)
                  ·
                    refine ⟨1319915030558843630278373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14079093659294332056302645 1319915030558843630278373)
                    ·
                      rfl

theorem cell22_3855788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_3855788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855788 prefixEnd_3855788 := by exact prefixLift 3855788
  have htrace : WordTrace (prefixWord ++ tailWord_3855788) baseStart_3855788 baseEnd_3855788 := by
    simpa [prefixWord, tailWord_3855788, baseEnd_3855788] using wordTrace_append hprefix tailTrace_3855788
  have hstable : (prefixWord ++ tailWord_3855788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855788).length < 2 ^ (prefixWord ++ tailWord_3855788).sum := by decide
  have hdescent : baseEnd_3855788 < baseStart_3855788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855805 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_3855805 : Nat := 118140960795 + 3855805 * 2 ^ 59
def prefixEnd_3855805 : Nat := 4983230072969 + 3 ^ 40 * 3855805 * 2
def baseEnd_3855805 : Nat := 1319920850006261252603321

theorem tailTrace_3855805 : CollatzResearch.WordTrace tailWord_3855805 prefixEnd_3855805 1319920850006261252603321 := by
  unfold tailWord_3855805
  simp only [CollatzResearch.WordTrace]
  refine ⟨140632761796084478911728869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93755174530722985941152579 140632761796084478911728869)
  ·
    refine ⟨26368642836765839795949163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140632761796084478911728869 26368642836765839795949163)
    ·
      refine ⟨39552964255148759693923745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26368642836765839795949163 39552964255148759693923745)
      ·
        refine ⟨29664723191361569770442809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39552964255148759693923745 29664723191361569770442809)
        ·
          refine ⟨22248542393521177327832107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29664723191361569770442809 22248542393521177327832107)
          ·
            refine ⟨33372813590281765991748161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22248542393521177327832107 33372813590281765991748161)
            ·
              refine ⟨25029610192711324493811121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33372813590281765991748161 25029610192711324493811121)
              ·
                refine ⟨18772207644533493370358341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25029610192711324493811121 18772207644533493370358341)
                ·
                  refine ⟨3519788933350030006942189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18772207644533493370358341 3519788933350030006942189)
                  ·
                    refine ⟨1319920850006261252603321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519788933350030006942189 1319920850006261252603321)
                    ·
                      rfl

theorem cell22_3855805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_3855805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855805 prefixEnd_3855805 := by exact prefixLift 3855805
  have htrace : WordTrace (prefixWord ++ tailWord_3855805) baseStart_3855805 baseEnd_3855805 := by
    simpa [prefixWord, tailWord_3855805, baseEnd_3855805] using wordTrace_append hprefix tailTrace_3855805
  have hstable : (prefixWord ++ tailWord_3855805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855805).length < 2 ^ (prefixWord ++ tailWord_3855805).sum := by decide
  have hdescent : baseEnd_3855805 < baseStart_3855805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855818 : List Nat := [3, 1, 2, 1, 2, 4, 9]
def baseStart_3855818 : Nat := 118140960795 + 3855818 * 2 ^ 59
def prefixEnd_3855818 : Nat := 4983230072969 + 3 ^ 40 * 3855818 * 2
def baseEnd_3855818 : Nat := 48886122228590131556603

theorem tailTrace_3855818 : CollatzResearch.WordTrace tailWord_3855818 prefixEnd_3855818 48886122228590131556603 := by
  unfold tailWord_3855818
  simp only [CollatzResearch.WordTrace]
  refine ⟨35158308986259345532988027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93755490630024921421301405 35158308986259345532988027)
  ·
    refine ⟨52737463479389018299482041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35158308986259345532988027 52737463479389018299482041)
    ·
      refine ⟨39553097609541763724611531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52737463479389018299482041 39553097609541763724611531)
      ·
        refine ⟨59329646414312645586917297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39553097609541763724611531 59329646414312645586917297)
        ·
          refine ⟨44497234810734484190187973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59329646414312645586917297 44497234810734484190187973)
          ·
            refine ⟨8343231527012715785660245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44497234810734484190187973 8343231527012715785660245)
            ·
              refine ⟨48886122228590131556603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8343231527012715785660245 48886122228590131556603)
              ·
                rfl

theorem cell22_3855818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 9].length) (baseStart_3855818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855818 prefixEnd_3855818 := by exact prefixLift 3855818
  have htrace : WordTrace (prefixWord ++ tailWord_3855818) baseStart_3855818 baseEnd_3855818 := by
    simpa [prefixWord, tailWord_3855818, baseEnd_3855818] using wordTrace_append hprefix tailTrace_3855818
  have hstable : (prefixWord ++ tailWord_3855818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855818).length < 2 ^ (prefixWord ++ tailWord_3855818).sum := by decide
  have hdescent : baseEnd_3855818 < baseStart_3855818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855822 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_3855822 : Nat := 118140960795 + 3855822 * 2 ^ 59
def prefixEnd_3855822 : Nat := 4983230072969 + 3 ^ 40 * 3855822 * 2
def baseEnd_3855822 : Nat := 1319926669453678874928269

theorem tailTrace_3855822 : CollatzResearch.WordTrace tailWord_3855822 prefixEnd_3855822 1319926669453678874928269 := by
  unfold tailWord_3855822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579172729627861351887215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93755587891348593876731813 17579172729627861351887215)
  ·
    refine ⟨26368759094441792027830823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17579172729627861351887215 26368759094441792027830823)
    ·
      refine ⟨39553138641662688041746235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26368759094441792027830823 39553138641662688041746235)
      ·
        refine ⟨59329707962494032062619353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39553138641662688041746235 59329707962494032062619353)
        ·
          refine ⟨44497280971870524046964515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59329707962494032062619353 44497280971870524046964515)
          ·
            refine ⟨66745921457805786070446773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44497280971870524046964515 66745921457805786070446773)
            ·
              refine ⟨6257430136669292444104385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66745921457805786070446773 6257430136669292444104385)
              ·
                refine ⟨4693072602501969333078289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257430136669292444104385 4693072602501969333078289)
                ·
                  refine ⟨3519804451876476999808717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693072602501969333078289 3519804451876476999808717)
                  ·
                    refine ⟨1319926669453678874928269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519804451876476999808717 1319926669453678874928269)
                    ·
                      rfl

theorem cell22_3855822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_3855822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855822 prefixEnd_3855822 := by exact prefixLift 3855822
  have htrace : WordTrace (prefixWord ++ tailWord_3855822) baseStart_3855822 baseEnd_3855822 := by
    simpa [prefixWord, tailWord_3855822, baseEnd_3855822] using wordTrace_append hprefix tailTrace_3855822
  have hstable : (prefixWord ++ tailWord_3855822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855822).length < 2 ^ (prefixWord ++ tailWord_3855822).sum := by decide
  have hdescent : baseEnd_3855822 < baseStart_3855822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855884 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_3855884 : Nat := 118140960795 + 3855884 * 2 ^ 59
def prefixEnd_3855884 : Nat := 4983230072969 + 3 ^ 40 * 3855884 * 2
def baseEnd_3855884 : Nat := 1319947893320731379878079

theorem tailTrace_3855884 : CollatzResearch.WordTrace tailWord_3855884 prefixEnd_3855884 1319947893320731379878079 := by
  unfold tailWord_3855884
  simp only [CollatzResearch.WordTrace]
  refine ⟨70317821581399137701927353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93757095441865516935903137 70317821581399137701927353)
  ·
    refine ⟨52738366186049353276445515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70317821581399137701927353 52738366186049353276445515)
    ·
      refine ⟨79107549279074029914668273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52738366186049353276445515 79107549279074029914668273)
      ·
        refine ⟨59330661959305522436001205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79107549279074029914668273 59330661959305522436001205)
        ·
          refine ⟨5562249558684892728375113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59330661959305522436001205 5562249558684892728375113)
          ·
            refine ⟨4171687169013669546281335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5562249558684892728375113 4171687169013669546281335)
            ·
              refine ⟨6257530753520504319422003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171687169013669546281335 6257530753520504319422003)
              ·
                refine ⟨9386296130280756479133005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257530753520504319422003 9386296130280756479133005)
                ·
                  refine ⟨3519861048855283679674877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9386296130280756479133005 3519861048855283679674877)
                  ·
                    refine ⟨1319947893320731379878079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519861048855283679674877 1319947893320731379878079)
                    ·
                      rfl

theorem cell22_3855884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_3855884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855884 prefixEnd_3855884 := by exact prefixLift 3855884
  have htrace : WordTrace (prefixWord ++ tailWord_3855884) baseStart_3855884 baseEnd_3855884 := by
    simpa [prefixWord, tailWord_3855884, baseEnd_3855884] using wordTrace_append hprefix tailTrace_3855884
  have hstable : (prefixWord ++ tailWord_3855884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855884).length < 2 ^ (prefixWord ++ tailWord_3855884).sum := by decide
  have hdescent : baseEnd_3855884 < baseStart_3855884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855972 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3855972 : Nat := 118140960795 + 3855972 * 2 ^ 59
def prefixEnd_3855972 : Nat := 4983230072969 + 3 ^ 40 * 3855972 * 2
def baseEnd_3855972 : Nat := 1319978017519128483677809

theorem tailTrace_3855972 : CollatzResearch.WordTrace tailWord_3855972 prefixEnd_3855972 1319978017519128483677809 := by
  unfold tailWord_3855972
  simp only [CollatzResearch.WordTrace]
  refine ⟨70319426393239733216529085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93759235190986310955372113 70319426393239733216529085)
  ·
    refine ⟨26369784897464899956198407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70319426393239733216529085 26369784897464899956198407)
    ·
      refine ⟨39554677346197349934297611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26369784897464899956198407 39554677346197349934297611)
      ·
        refine ⟨59332016019296024901446417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39554677346197349934297611 59332016019296024901446417)
        ·
          refine ⟨44499012014472018676084813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59332016019296024901446417 44499012014472018676084813)
          ·
            refine ⟨16687129505427007003531805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44499012014472018676084813 16687129505427007003531805)
            ·
              refine ⟨6257673564535127626324427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16687129505427007003531805 6257673564535127626324427)
              ·
                refine ⟨9386510346802691439486641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257673564535127626324427 9386510346802691439486641)
                ·
                  refine ⟨7039882760102018579614981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9386510346802691439486641 7039882760102018579614981)
                  ·
                    refine ⟨1319978017519128483677809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039882760102018579614981 1319978017519128483677809)
                    ·
                      rfl

theorem cell22_3855972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3855972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3855972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3855972 prefixEnd_3855972 := by exact prefixLift 3855972
  have htrace : WordTrace (prefixWord ++ tailWord_3855972) baseStart_3855972 baseEnd_3855972 := by
    simpa [prefixWord, tailWord_3855972, baseEnd_3855972] using wordTrace_append hprefix tailTrace_3855972
  have hstable : (prefixWord ++ tailWord_3855972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855972).length < 2 ^ (prefixWord ++ tailWord_3855972).sum := by decide
  have hdescent : baseEnd_3855972 < baseStart_3855972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856008 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 2, 3]
def baseStart_3856008 : Nat := 118140960795 + 3856008 * 2 ^ 59
def prefixEnd_3856008 : Nat := 4983230072969 + 3 ^ 40 * 3856008 * 2
def baseEnd_3856008 : Nat := 1319990341054836389777699

theorem tailTrace_3856008 : CollatzResearch.WordTrace tailWord_3856008 prefixEnd_3856008 1319990341054836389777699 := by
  unfold tailWord_3856008
  simp only [CollatzResearch.WordTrace]
  refine ⟨70320082907174522290684339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93760110542899363054245785 70320082907174522290684339)
  ·
    refine ⟨105480124360761783436026509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70320082907174522290684339 105480124360761783436026509)
    ·
      refine ⟨39555046635285668788509941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105480124360761783436026509 39555046635285668788509941)
      ·
        refine ⟨3708285622058031448922807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39555046635285668788509941 3708285622058031448922807)
        ·
          refine ⟨5562428433087047173384211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708285622058031448922807 5562428433087047173384211)
          ·
            refine ⟨8343642649630570760076317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562428433087047173384211 8343642649630570760076317)
            ·
              refine ⟨3128865993611464035028619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8343642649630570760076317 3128865993611464035028619)
              ·
                refine ⟨4693298990417196052542929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128865993611464035028619 4693298990417196052542929)
                ·
                  refine ⟨3519974242812897039407197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693298990417196052542929 3519974242812897039407197)
                  ·
                    refine ⟨1319990341054836389777699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519974242812897039407197 1319990341054836389777699)
                    ·
                      rfl

theorem cell22_3856008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_3856008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856008 prefixEnd_3856008 := by exact prefixLift 3856008
  have htrace : WordTrace (prefixWord ++ tailWord_3856008) baseStart_3856008 baseEnd_3856008 := by
    simpa [prefixWord, tailWord_3856008, baseEnd_3856008] using wordTrace_append hprefix tailTrace_3856008
  have hstable : (prefixWord ++ tailWord_3856008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856008).length < 2 ^ (prefixWord ++ tailWord_3856008).sum := by decide
  have hdescent : baseEnd_3856008 < baseStart_3856008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856036 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_3856036 : Nat := 118140960795 + 3856036 * 2 ^ 59
def prefixEnd_3856036 : Nat := 4983230072969 + 3 ^ 40 * 3856036 * 2
def baseEnd_3856036 : Nat := 1319999926027053650077613

theorem tailTrace_3856036 : CollatzResearch.WordTrace tailWord_3856036 prefixEnd_3856036 1319999926027053650077613 := by
  unfold tailWord_3856036
  simp only [CollatzResearch.WordTrace]
  refine ⟨70320593529123802681693981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93760791372165070242258641 70320593529123802681693981)
  ·
    refine ⟨26370222573421426005635243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70320593529123802681693981 26370222573421426005635243)
    ·
      refine ⟨39555333860132139008452865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26370222573421426005635243 39555333860132139008452865)
      ·
        refine ⟨29666500395099104256339649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39555333860132139008452865 29666500395099104256339649)
        ·
          refine ⟨22249875296324328192254737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29666500395099104256339649 22249875296324328192254737)
          ·
            refine ⟨16687406472243246144191053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22249875296324328192254737 16687406472243246144191053)
            ·
              refine ⟨6257777427091217304071645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16687406472243246144191053 6257777427091217304071645)
              ·
                refine ⟨2346666535159206489026867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6257777427091217304071645 2346666535159206489026867)
                ·
                  refine ⟨3519999802738809733540301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346666535159206489026867 3519999802738809733540301)
                  ·
                    refine ⟨1319999926027053650077613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519999802738809733540301 1319999926027053650077613)
                    ·
                      rfl

theorem cell22_3856036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_3856036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856036 prefixEnd_3856036 := by exact prefixLift 3856036
  have htrace : WordTrace (prefixWord ++ tailWord_3856036) baseStart_3856036 baseEnd_3856036 := by
    simpa [prefixWord, tailWord_3856036, baseEnd_3856036] using wordTrace_append hprefix tailTrace_3856036
  have hstable : (prefixWord ++ tailWord_3856036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856036).length < 2 ^ (prefixWord ++ tailWord_3856036).sum := by decide
  have hdescent : baseEnd_3856036 < baseStart_3856036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856053 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3856053 : Nat := 118140960795 + 3856053 * 2 ^ 59
def prefixEnd_3856053 : Nat := 4983230072969 + 3 ^ 40 * 3856053 * 2
def baseEnd_3856053 : Nat := 1320005745474471272402561

theorem tailTrace_3856053 : CollatzResearch.WordTrace tailWord_3856053 prefixEnd_3856053 1320005745474471272402561 := by
  unfold tailWord_3856053
  simp only [CollatzResearch.WordTrace]
  refine ⟨140641807099186017266756813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93761204732790678177837875 140641807099186017266756813)
  ·
    refine ⟨52740677662194756475033805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140641807099186017266756813 52740677662194756475033805)
    ·
      refine ⟨19777754123323033678137677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52740677662194756475033805 19777754123323033678137677)
      ·
        refine ⟨7416657796246137629301629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19777754123323033678137677 7416657796246137629301629)
        ·
          refine ⟨2781246673592301610988111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7416657796246137629301629 2781246673592301610988111)
          ·
            refine ⟨4171870010388452416482167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781246673592301610988111 4171870010388452416482167)
            ·
              refine ⟨6257805015582678624723251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171870010388452416482167 6257805015582678624723251)
              ·
                refine ⟨9386707523374017937084877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257805015582678624723251 9386707523374017937084877)
                ·
                  refine ⟨3520015321265256726406829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9386707523374017937084877 3520015321265256726406829)
                  ·
                    refine ⟨1320005745474471272402561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3520015321265256726406829 1320005745474471272402561)
                    ·
                      rfl

theorem cell22_3856053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3856053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856053 prefixEnd_3856053 := by exact prefixLift 3856053
  have htrace : WordTrace (prefixWord ++ tailWord_3856053) baseStart_3856053 baseEnd_3856053 := by
    simpa [prefixWord, tailWord_3856053, baseEnd_3856053] using wordTrace_append hprefix tailTrace_3856053
  have hstable : (prefixWord ++ tailWord_3856053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856053).length < 2 ^ (prefixWord ++ tailWord_3856053).sum := by decide
  have hdescent : baseEnd_3856053 < baseStart_3856053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856075 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_3856075 : Nat := 118140960795 + 3856075 * 2 ^ 59
def prefixEnd_3856075 : Nat := 4983230072969 + 3 ^ 40 * 3856075 * 2
def baseEnd_3856075 : Nat := 1320013276524070548352493

theorem tailTrace_3856075 : CollatzResearch.WordTrace tailWord_3856075 prefixEnd_3856075 1320013276524070548352493 := by
  unfold tailWord_3856075
  simp only [CollatzResearch.WordTrace]
  refine ⟨140642609505106315024057679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93761739670070876682705119 140642609505106315024057679)
  ·
    refine ⟨210963914257659472536086519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140642609505106315024057679 210963914257659472536086519)
    ·
      refine ⟨316445871386489208804129779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210963914257659472536086519 316445871386489208804129779)
      ·
        refine ⟨474668807079733813206194669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316445871386489208804129779 474668807079733813206194669)
        ·
          refine ⟨178000802654900179952323001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474668807079733813206194669 178000802654900179952323001)
          ·
            refine ⟨133500601991175134964242251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178000802654900179952323001 133500601991175134964242251)
            ·
              refine ⟨200250902986762702446363377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133500601991175134964242251 200250902986762702446363377)
              ·
                refine ⟨150188177240072026834772533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200250902986762702446363377 150188177240072026834772533)
                ·
                  refine ⟨14080141616256752515759925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150188177240072026834772533 14080141616256752515759925)
                  ·
                    refine ⟨1320013276524070548352493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14080141616256752515759925 1320013276524070548352493)
                    ·
                      rfl

theorem cell22_3856075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_3856075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856075 prefixEnd_3856075 := by exact prefixLift 3856075
  have htrace : WordTrace (prefixWord ++ tailWord_3856075) baseStart_3856075 baseEnd_3856075 := by
    simpa [prefixWord, tailWord_3856075, baseEnd_3856075] using wordTrace_append hprefix tailTrace_3856075
  have hstable : (prefixWord ++ tailWord_3856075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856075).length < 2 ^ (prefixWord ++ tailWord_3856075).sum := by decide
  have hdescent : baseEnd_3856075 < baseStart_3856075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856107 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 2, 4]
def baseStart_3856107 : Nat := 118140960795 + 3856107 * 2 ^ 59
def prefixEnd_3856107 : Nat := 4983230072969 + 3 ^ 40 * 3856107 * 2
def baseEnd_3856107 : Nat := 1320024230778033131552395

theorem tailTrace_3856107 : CollatzResearch.WordTrace tailWord_3856107 prefixEnd_3856107 1320024230778033131552395 := by
  unfold tailWord_3856107
  simp only [CollatzResearch.WordTrace]
  refine ⟨140643776640990384489222575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93762517760660256326148383 140643776640990384489222575)
  ·
    refine ⟨210965664961485576733833863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140643776640990384489222575 210965664961485576733833863)
    ·
      refine ⟨316448497442228365100750795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210965664961485576733833863 316448497442228365100750795)
      ·
        refine ⟨474672746163342547651126193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316448497442228365100750795 474672746163342547651126193)
        ·
          refine ⟨356004559622506910738344645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474672746163342547651126193 356004559622506910738344645)
          ·
            refine ⟨66750854929220045763439621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356004559622506910738344645 66750854929220045763439621)
            ·
              refine ⟨12515785299228758580644929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66750854929220045763439621 12515785299228758580644929)
              ·
                refine ⟨9386838974421568935483697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12515785299228758580644929 9386838974421568935483697)
                ·
                  refine ⟨7040129230816176701612773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9386838974421568935483697 7040129230816176701612773)
                  ·
                    refine ⟨1320024230778033131552395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040129230816176701612773 1320024230778033131552395)
                    ·
                      rfl

theorem cell22_3856107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_3856107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856107 prefixEnd_3856107 := by exact prefixLift 3856107
  have htrace : WordTrace (prefixWord ++ tailWord_3856107) baseStart_3856107 baseEnd_3856107 := by
    simpa [prefixWord, tailWord_3856107, baseEnd_3856107] using wordTrace_append hprefix tailTrace_3856107
  have hstable : (prefixWord ++ tailWord_3856107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856107).length < 2 ^ (prefixWord ++ tailWord_3856107).sum := by decide
  have hdescent : baseEnd_3856107 < baseStart_3856107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856126 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3856126 : Nat := 118140960795 + 3856126 * 2 ^ 59
def prefixEnd_3856126 : Nat := 4983230072969 + 3 ^ 40 * 3856126 * 2
def baseEnd_3856126 : Nat := 1320030734866323415327337

theorem tailTrace_3856126 : CollatzResearch.WordTrace tailWord_3856126 prefixEnd_3856126 1320030734866323415327337 := by
  unfold tailWord_3856126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17580558703490193841770529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93762979751947700489442821 17580558703490193841770529)
  ·
    refine ⟨13185419027617645381327897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17580558703490193841770529 13185419027617645381327897)
    ·
      refine ⟨9889064270713234035995923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13185419027617645381327897 9889064270713234035995923)
      ·
        refine ⟨14833596406069851053993885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889064270713234035995923 14833596406069851053993885)
        ·
          refine ⟨5562598652276194145247707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14833596406069851053993885 5562598652276194145247707)
          ·
            refine ⟨8343897978414291217871561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562598652276194145247707 8343897978414291217871561)
            ·
              refine ⟨6257923483810718413403671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8343897978414291217871561 6257923483810718413403671)
              ·
                refine ⟨9386885225716077620105507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257923483810718413403671 9386885225716077620105507)
                ·
                  refine ⟨14080327838574116430158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9386885225716077620105507 14080327838574116430158261)
                  ·
                    refine ⟨1320030734866323415327337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14080327838574116430158261 1320030734866323415327337)
                    ·
                      rfl

theorem cell22_3856126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3856126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856126 prefixEnd_3856126 := by exact prefixLift 3856126
  have htrace : WordTrace (prefixWord ++ tailWord_3856126) baseStart_3856126 baseEnd_3856126 := by
    simpa [prefixWord, tailWord_3856126, baseEnd_3856126] using wordTrace_append hprefix tailTrace_3856126
  have hstable : (prefixWord ++ tailWord_3856126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856126).length < 2 ^ (prefixWord ++ tailWord_3856126).sum := by decide
  have hdescent : baseEnd_3856126 < baseStart_3856126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856205 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3856205 : Nat := 118140960795 + 3856205 * 2 ^ 59
def prefixEnd_3856205 : Nat := 4983230072969 + 3 ^ 40 * 3856205 * 2
def baseEnd_3856205 : Nat := 1320057778180793542602095

theorem tailTrace_3856205 : CollatzResearch.WordTrace tailWord_3856205 prefixEnd_3856205 1320057778180793542602095 := by
  unfold tailWord_3856205
  simp only [CollatzResearch.WordTrace]
  refine ⟨140647350994635347226290069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93764900663090231484193379 140647350994635347226290069)
  ·
    refine ⟨6592844577873531901232347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140647350994635347226290069 6592844577873531901232347)
    ·
      refine ⟨9889266866810297851848521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6592844577873531901232347 9889266866810297851848521)
      ·
        refine ⟨7416950150107723388886391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9889266866810297851848521 7416950150107723388886391)
        ·
          refine ⟨11125425225161585083329587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7416950150107723388886391 11125425225161585083329587)
          ·
            refine ⟨16688137837742377624994381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125425225161585083329587 16688137837742377624994381)
            ·
              refine ⟨6258051689153391609372893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16688137837742377624994381 6258051689153391609372893)
              ·
                refine ⟨2346769383432521853514835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6258051689153391609372893 2346769383432521853514835)
                ·
                  refine ⟨3520154075148782780272253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346769383432521853514835 3520154075148782780272253)
                  ·
                    refine ⟨1320057778180793542602095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3520154075148782780272253 1320057778180793542602095)
                    ·
                      rfl

theorem cell22_3856205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3856205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856205 prefixEnd_3856205 := by exact prefixLift 3856205
  have htrace : WordTrace (prefixWord ++ tailWord_3856205) baseStart_3856205 baseEnd_3856205 := by
    simpa [prefixWord, tailWord_3856205, baseEnd_3856205] using wordTrace_append hprefix tailTrace_3856205
  have hstable : (prefixWord ++ tailWord_3856205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856205).length < 2 ^ (prefixWord ++ tailWord_3856205).sum := by decide
  have hdescent : baseEnd_3856205 < baseStart_3856205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856259 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 2, 4]
def baseStart_3856259 : Nat := 118140960795 + 3856259 * 2 ^ 59
def prefixEnd_3856259 : Nat := 4983230072969 + 3 ^ 40 * 3856259 * 2
def baseEnd_3856259 : Nat := 1320076263484355401751929

theorem tailTrace_3856259 : CollatzResearch.WordTrace tailWord_3856259 prefixEnd_3856259 1320076263484355401751929 := by
  unfold tailWord_3856259
  simp only [CollatzResearch.WordTrace]
  refine ⟨140649320536439714448755831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93766213690959809632503887 140649320536439714448755831)
  ·
    refine ⟨210973980804659571673133747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140649320536439714448755831 210973980804659571673133747)
    ·
      refine ⟨316460971206989357509700621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210973980804659571673133747 316460971206989357509700621)
      ·
        refine ⟨118672864202621009066137733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316460971206989357509700621 118672864202621009066137733)
        ·
          refine ⟨22251162037991439199900825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118672864202621009066137733 22251162037991439199900825)
          ·
            refine ⟨16688371528493579399925619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22251162037991439199900825 16688371528493579399925619)
            ·
              refine ⟨25032557292740369099888429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16688371528493579399925619 25032557292740369099888429)
              ·
                refine ⟨9387208984777638412458161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25032557292740369099888429 9387208984777638412458161)
                ·
                  refine ⟨7040406738583228809343621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387208984777638412458161 7040406738583228809343621)
                  ·
                    refine ⟨1320076263484355401751929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040406738583228809343621 1320076263484355401751929)
                    ·
                      rfl

theorem cell22_3856259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_3856259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856259 prefixEnd_3856259 := by exact prefixLift 3856259
  have htrace : WordTrace (prefixWord ++ tailWord_3856259) baseStart_3856259 baseEnd_3856259 := by
    simpa [prefixWord, tailWord_3856259, baseEnd_3856259] using wordTrace_append hprefix tailTrace_3856259
  have hstable : (prefixWord ++ tailWord_3856259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856259).length < 2 ^ (prefixWord ++ tailWord_3856259).sum := by decide
  have hdescent : baseEnd_3856259 < baseStart_3856259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856274 : List Nat := [3, 2, 3, 2, 1, 11]
def baseStart_3856274 : Nat := 118140960795 + 3856274 * 2 ^ 59
def prefixEnd_3856274 : Nat := 4983230072969 + 3 ^ 40 * 3856274 * 2
def baseEnd_3856274 : Nat := 16297301213467905711443

theorem tailTrace_3856274 : CollatzResearch.WordTrace tailWord_3856274 prefixEnd_3856274 16297301213467905711443 := by
  unfold tailWord_3856274
  simp only [CollatzResearch.WordTrace]
  refine ⟨35162466907846343002637969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93766578420923581340367917 35162466907846343002637969)
  ·
    refine ⟨26371850180884757251978477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35162466907846343002637969 26371850180884757251978477)
    ·
      refine ⟨9889443817831783969491929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26371850180884757251978477 9889443817831783969491929)
      ·
        refine ⟨7417082863373837977118947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9889443817831783969491929 7417082863373837977118947)
        ·
          refine ⟨11125624295060756965678421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417082863373837977118947 11125624295060756965678421)
          ·
            refine ⟨16297301213467905711443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11125624295060756965678421 16297301213467905711443)
            ·
              rfl

theorem cell22_3856274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 11].length) (baseStart_3856274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856274 prefixEnd_3856274 := by exact prefixLift 3856274
  have htrace : WordTrace (prefixWord ++ tailWord_3856274) baseStart_3856274 baseEnd_3856274 := by
    simpa [prefixWord, tailWord_3856274, baseEnd_3856274] using wordTrace_append hprefix tailTrace_3856274
  have hstable : (prefixWord ++ tailWord_3856274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856274).length < 2 ^ (prefixWord ++ tailWord_3856274).sum := by decide
  have hdescent : baseEnd_3856274 < baseStart_3856274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856276 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3856276 : Nat := 118140960795 + 3856276 * 2 ^ 59
def prefixEnd_3856276 : Nat := 4983230072969 + 3 ^ 40 * 3856276 * 2
def baseEnd_3856276 : Nat := 1320082082931773024076877

theorem tailTrace_3856276 : CollatzResearch.WordTrace tailWord_3856276 prefixEnd_3856276 1320082082931773024076877 := by
  unfold tailWord_3856276
  simp only [CollatzResearch.WordTrace]
  refine ⟨70324970288689063176062341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93766627051585417568083121 70324970288689063176062341)
  ·
    refine ⟨13185931929129199345511689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70324970288689063176062341 13185931929129199345511689)
    ·
      refine ⟨9889448946846899509133767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13185931929129199345511689 9889448946846899509133767)
      ·
        refine ⟨14834173420270349263700651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889448946846899509133767 14834173420270349263700651)
        ·
          refine ⟨22251260130405523895550977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14834173420270349263700651 22251260130405523895550977)
          ·
            refine ⟨16688445097804142921663233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22251260130405523895550977 16688445097804142921663233)
            ·
              refine ⟨12516333823353107191247425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16688445097804142921663233 12516333823353107191247425)
              ·
                refine ⟨9387250367514830393435569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516333823353107191247425 9387250367514830393435569)
                ·
                  refine ⟨7040437775636122795076677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387250367514830393435569 7040437775636122795076677)
                  ·
                    refine ⟨1320082082931773024076877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040437775636122795076677 1320082082931773024076877)
                    ·
                      rfl

theorem cell22_3856276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3856276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856276 prefixEnd_3856276 := by exact prefixLift 3856276
  have htrace : WordTrace (prefixWord ++ tailWord_3856276) baseStart_3856276 baseEnd_3856276 := by
    simpa [prefixWord, tailWord_3856276, baseEnd_3856276] using wordTrace_append hprefix tailTrace_3856276
  have hstable : (prefixWord ++ tailWord_3856276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856276).length < 2 ^ (prefixWord ++ tailWord_3856276).sum := by decide
  have hdescent : baseEnd_3856276 < baseStart_3856276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856334 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_3856334 : Nat := 118140960795 + 3856334 * 2 ^ 59
def prefixEnd_3856334 : Nat := 4983230072969 + 3 ^ 40 * 3856334 * 2
def baseEnd_3856334 : Nat := 1320101937517080206126699

theorem tailTrace_3856334 : CollatzResearch.WordTrace tailWord_3856334 prefixEnd_3856334 1320101937517080206126699 := by
  unfold tailWord_3856334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17581507001396000282217007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93768037340778668171824037 17581507001396000282217007)
  ·
    refine ⟨26372260502094000423325511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17581507001396000282217007 26372260502094000423325511)
    ·
      refine ⟨39558390753141000634988267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26372260502094000423325511 39558390753141000634988267)
      ·
        refine ⟨59337586129711500952482401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39558390753141000634988267 59337586129711500952482401)
        ·
          refine ⟨44503189597283625714361801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59337586129711500952482401 44503189597283625714361801)
          ·
            refine ⟨33377392197962719285771351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44503189597283625714361801 33377392197962719285771351)
            ·
              refine ⟨50066088296944078928657027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33377392197962719285771351 50066088296944078928657027)
              ·
                refine ⟨75099132445416118392985541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50066088296944078928657027 75099132445416118392985541)
                ·
                  refine ⟨14081087333515522198684789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75099132445416118392985541 14081087333515522198684789)
                  ·
                    refine ⟨1320101937517080206126699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14081087333515522198684789 1320101937517080206126699)
                    ·
                      rfl

theorem cell22_3856334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_3856334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856334 prefixEnd_3856334 := by exact prefixLift 3856334
  have htrace : WordTrace (prefixWord ++ tailWord_3856334) baseStart_3856334 baseEnd_3856334 := by
    simpa [prefixWord, tailWord_3856334, baseEnd_3856334] using wordTrace_append hprefix tailTrace_3856334
  have hstable : (prefixWord ++ tailWord_3856334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856334).length < 2 ^ (prefixWord ++ tailWord_3856334).sum := by decide
  have hdescent : baseEnd_3856334 < baseStart_3856334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856374 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_3856374 : Nat := 118140960795 + 3856374 * 2 ^ 59
def prefixEnd_3856374 : Nat := 4983230072969 + 3 ^ 40 * 3856374 * 2
def baseEnd_3856374 : Nat := 1320115630334533435126577

theorem tailTrace_3856374 : CollatzResearch.WordTrace tailWord_3856374 prefixEnd_3856374 1320115630334533435126577 := by
  unfold tailWord_3856374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790844683188943068074511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93769009954015392726128117 8790844683188943068074511)
  ·
    refine ⟨13186267024783414602111767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8790844683188943068074511 13186267024783414602111767)
    ·
      refine ⟨19779400537175121903167651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13186267024783414602111767 19779400537175121903167651)
      ·
        refine ⟨29669100805762682854751477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19779400537175121903167651 29669100805762682854751477)
        ·
          refine ⟨2781478200540251517632951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29669100805762682854751477 2781478200540251517632951)
          ·
            refine ⟨4172217300810377276449427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781478200540251517632951 4172217300810377276449427)
            ·
              refine ⟨6258325951215565914674141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172217300810377276449427 6258325951215565914674141)
              ·
                refine ⟨2346872231705837218002803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6258325951215565914674141 2346872231705837218002803)
                ·
                  refine ⟨3520308347558755827004205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346872231705837218002803 3520308347558755827004205)
                  ·
                    refine ⟨1320115630334533435126577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3520308347558755827004205 1320115630334533435126577)
                    ·
                      rfl

theorem cell22_3856374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_3856374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856374 prefixEnd_3856374 := by exact prefixLift 3856374
  have htrace : WordTrace (prefixWord ++ tailWord_3856374) baseStart_3856374 baseEnd_3856374 := by
    simpa [prefixWord, tailWord_3856374, baseEnd_3856374] using wordTrace_append hprefix tailTrace_3856374
  have hstable : (prefixWord ++ tailWord_3856374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856374).length < 2 ^ (prefixWord ++ tailWord_3856374).sum := by decide
  have hdescent : baseEnd_3856374 < baseStart_3856374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856379 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 1, 5]
def baseStart_3856379 : Nat := 118140960795 + 3856379 * 2 ^ 59
def prefixEnd_3856379 : Nat := 4983230072969 + 3 ^ 40 * 3856379 * 2
def baseEnd_3856379 : Nat := 1320117341936715088751561

theorem tailTrace_3856379 : CollatzResearch.WordTrace tailWord_3856379 prefixEnd_3856379 1320117341936715088751561 := by
  unfold tailWord_3856379
  simp only [CollatzResearch.WordTrace]
  refine ⟨140653697296004974943124191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93769131530669983295416127 140653697296004974943124191)
  ·
    refine ⟨210980545944007462414686287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140653697296004974943124191 210980545944007462414686287)
    ·
      refine ⟨316470818916011193622029431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210980545944007462414686287 316470818916011193622029431)
      ·
        refine ⟨474706228374016790433044147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316470818916011193622029431 474706228374016790433044147)
        ·
          refine ⟨712059342561025185649566221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474706228374016790433044147 712059342561025185649566221)
          ·
            refine ⟨267022253460384444618587333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712059342561025185649566221 267022253460384444618587333)
            ·
              refine ⟨50066672523822083365985125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267022253460384444618587333 50066672523822083365985125)
              ·
                refine ⟨9387501098216640631122211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50066672523822083365985125 9387501098216640631122211)
                ·
                  refine ⟨14081251647324960946683317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387501098216640631122211 14081251647324960946683317)
                  ·
                    refine ⟨1320117341936715088751561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14081251647324960946683317 1320117341936715088751561)
                    ·
                      rfl

theorem cell22_3856379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_3856379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856379 prefixEnd_3856379 := by exact prefixLift 3856379
  have htrace : WordTrace (prefixWord ++ tailWord_3856379) baseStart_3856379 baseEnd_3856379 := by
    simpa [prefixWord, tailWord_3856379, baseEnd_3856379] using wordTrace_append hprefix tailTrace_3856379
  have hstable : (prefixWord ++ tailWord_3856379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856379).length < 2 ^ (prefixWord ++ tailWord_3856379).sum := by decide
  have hdescent : baseEnd_3856379 < baseStart_3856379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856396 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_3856396 : Nat := 118140960795 + 3856396 * 2 ^ 59
def prefixEnd_3856396 : Nat := 4983230072969 + 3 ^ 40 * 3856396 * 2
def baseEnd_3856396 : Nat := 1320123161384132711076509

theorem tailTrace_3856396 : CollatzResearch.WordTrace tailWord_3856396 prefixEnd_3856396 1320123161384132711076509 := by
  unfold tailWord_3856396
  simp only [CollatzResearch.WordTrace]
  refine ⟨70327158668471693423246521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93769544891295591230995361 70327158668471693423246521)
  ·
    refine ⟨52745369001353770067434891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70327158668471693423246521 52745369001353770067434891)
    ·
      refine ⟨79118053502030655101152337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52745369001353770067434891 79118053502030655101152337)
      ·
        refine ⟨59338540126522991325864253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79118053502030655101152337 59338540126522991325864253)
        ·
          refine ⟨22251952547446121747199095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59338540126522991325864253 22251952547446121747199095)
          ·
            refine ⟨33377928821169182620798643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22251952547446121747199095 33377928821169182620798643)
            ·
              refine ⟨50066893231753773931197965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33377928821169182620798643 50066893231753773931197965)
              ·
                refine ⟨18775084961907665224199237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50066893231753773931197965 18775084961907665224199237)
                ·
                  refine ⟨3520328430357687229537357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18775084961907665224199237 3520328430357687229537357)
                  ·
                    refine ⟨1320123161384132711076509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3520328430357687229537357 1320123161384132711076509)
                    ·
                      rfl

theorem cell22_3856396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_3856396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856396 prefixEnd_3856396 := by exact prefixLift 3856396
  have htrace : WordTrace (prefixWord ++ tailWord_3856396) baseStart_3856396 baseEnd_3856396 := by
    simpa [prefixWord, tailWord_3856396, baseEnd_3856396] using wordTrace_append hprefix tailTrace_3856396
  have hstable : (prefixWord ++ tailWord_3856396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856396).length < 2 ^ (prefixWord ++ tailWord_3856396).sum := by decide
  have hdescent : baseEnd_3856396 < baseStart_3856396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856404 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3856404 : Nat := 118140960795 + 3856404 * 2 ^ 59
def prefixEnd_3856404 : Nat := 4983230072969 + 3 ^ 40 * 3856404 * 2
def baseEnd_3856404 : Nat := 440041966649207785625495

theorem tailTrace_3856404 : CollatzResearch.WordTrace tailWord_3856404 prefixEnd_3856404 440041966649207785625495 := by
  unfold tailWord_3856404
  simp only [CollatzResearch.WordTrace]
  refine ⟨70327304560457202106392133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93769739413942936141856177 70327304560457202106392133)
  ·
    refine ⟨13186369605085725394948525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70327304560457202106392133 13186369605085725394948525)
    ·
      refine ⟨4944888601907147023105697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13186369605085725394948525 4944888601907147023105697)
      ·
        refine ⟨3708666451430360267329273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4944888601907147023105697 3708666451430360267329273)
        ·
          refine ⟨2781499838572770200496955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3708666451430360267329273 2781499838572770200496955)
          ·
            refine ⟨4172249757859155300745433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781499838572770200496955 4172249757859155300745433)
            ·
              refine ⟨3129187318394366475559075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172249757859155300745433 3129187318394366475559075)
              ·
                refine ⟨4693780977591549713338613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129187318394366475559075 4693780977591549713338613)
                ·
                  refine ⟨440041966649207785625495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4693780977591549713338613 440041966649207785625495)
                  ·
                    rfl

theorem cell22_3856404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3856404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856404 prefixEnd_3856404 := by exact prefixLift 3856404
  have htrace : WordTrace (prefixWord ++ tailWord_3856404) baseStart_3856404 baseEnd_3856404 := by
    simpa [prefixWord, tailWord_3856404, baseEnd_3856404] using wordTrace_append hprefix tailTrace_3856404
  have hstable : (prefixWord ++ tailWord_3856404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856404).length < 2 ^ (prefixWord ++ tailWord_3856404).sum := by decide
  have hdescent : baseEnd_3856404 < baseStart_3856404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856426 : List Nat := [3, 1, 4, 1, 2, 1, 2, 8]
def baseStart_3856426 : Nat := 118140960795 + 3856426 * 2 ^ 59
def prefixEnd_3856426 : Nat := 4983230072969 + 3 ^ 40 * 3856426 * 2
def baseEnd_3856426 : Nat := 146681492333024736980713

theorem tailTrace_3856426 : CollatzResearch.WordTrace tailWord_3856426 prefixEnd_3856426 146681492333024736980713 := by
  unfold tailWord_3856426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35163852881708675492521283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93770274351223134646723421 35163852881708675492521283)
  ·
    refine ⟨52745779322563013238781925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35163852881708675492521283 52745779322563013238781925)
    ·
      refine ⟨9889833622980564982271611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52745779322563013238781925 9889833622980564982271611)
      ·
        refine ⟨14834750434470847473407417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889833622980564982271611 14834750434470847473407417)
        ·
          refine ⟨11126062825853135605055563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14834750434470847473407417 11126062825853135605055563)
          ·
            refine ⟨16689094238779703407583345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126062825853135605055563 16689094238779703407583345)
            ·
              refine ⟨12516820679084777555687509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16689094238779703407583345 12516820679084777555687509)
              ·
                refine ⟨146681492333024736980713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12516820679084777555687509 146681492333024736980713)
                ·
                  rfl

theorem cell22_3856426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_3856426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856426 prefixEnd_3856426 := by exact prefixLift 3856426
  have htrace : WordTrace (prefixWord ++ tailWord_3856426) baseStart_3856426 baseEnd_3856426 := by
    simpa [prefixWord, tailWord_3856426, baseEnd_3856426] using wordTrace_append hprefix tailTrace_3856426
  have hstable : (prefixWord ++ tailWord_3856426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856426).length < 2 ^ (prefixWord ++ tailWord_3856426).sum := by decide
  have hdescent : baseEnd_3856426 < baseStart_3856426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856471 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 5]
def baseStart_3856471 : Nat := 118140960795 + 3856471 * 2 ^ 59
def prefixEnd_3856471 : Nat := 4983230072969 + 3 ^ 40 * 3856471 * 2
def baseEnd_3856471 : Nat := 440049611805619171817093

theorem tailTrace_3856471 : CollatzResearch.WordTrace tailWord_3856471 prefixEnd_3856471 440049611805619171817093 := by
  unfold tailWord_3856471
  simp only [CollatzResearch.WordTrace]
  refine ⟨140657052811671674655473267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93771368541114449770315511 140657052811671674655473267)
  ·
    refine ⟨210985579217507511983209901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140657052811671674655473267 210985579217507511983209901)
    ·
      refine ⟨79119592206565316993703713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210985579217507511983209901 79119592206565316993703713)
      ·
        refine ⟨59339694154923987745277785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79119592206565316993703713 59339694154923987745277785)
        ·
          refine ⟨44504770616192990808958339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59339694154923987745277785 44504770616192990808958339)
          ·
            refine ⟨66757155924289486213437509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44504770616192990808958339 66757155924289486213437509)
            ·
              refine ⟨12516966735804278665019533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66757155924289486213437509 12516966735804278665019533)
              ·
                refine ⟨4693862525926604499382325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12516966735804278665019533 4693862525926604499382325)
                ·
                  refine ⟨440049611805619171817093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4693862525926604499382325 440049611805619171817093)
                  ·
                    rfl

theorem cell22_3856471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 5].length) (baseStart_3856471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856471 prefixEnd_3856471 := by exact prefixLift 3856471
  have htrace : WordTrace (prefixWord ++ tailWord_3856471) baseStart_3856471 baseEnd_3856471 := by
    simpa [prefixWord, tailWord_3856471, baseEnd_3856471] using wordTrace_append hprefix tailTrace_3856471
  have hstable : (prefixWord ++ tailWord_3856471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856471).length < 2 ^ (prefixWord ++ tailWord_3856471).sum := by decide
  have hdescent : baseEnd_3856471 < baseStart_3856471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856535 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 1, 4]
def baseStart_3856535 : Nat := 118140960795 + 3856535 * 2 ^ 59
def prefixEnd_3856535 : Nat := 4983230072969 + 3 ^ 40 * 3856535 * 2
def baseEnd_3856535 : Nat := 1320170743924782681851083

theorem tailTrace_3856535 : CollatzResearch.WordTrace tailWord_3856535 prefixEnd_3856535 1320170743924782681851083 := by
  unfold tailWord_3856535
  simp only [CollatzResearch.WordTrace]
  refine ⟨140659387083439813585803059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93772924722293209057202039 140659387083439813585803059)
  ·
    refine ⟨210989080625159720378704589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140659387083439813585803059 210989080625159720378704589)
    ·
      refine ⟨79120905234434895142014221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210989080625159720378704589 79120905234434895142014221)
      ·
        refine ⟨29670339462913085678255333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79120905234434895142014221 29670339462913085678255333)
        ·
          refine ⟨5563188649296203564672875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29670339462913085678255333 5563188649296203564672875)
          ·
            refine ⟨8344782973944305347009313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563188649296203564672875 8344782973944305347009313)
            ·
              refine ⟨6258587230458229010256985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344782973944305347009313 6258587230458229010256985)
              ·
                refine ⟨4693940422843671757692739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258587230458229010256985 4693940422843671757692739)
                ·
                  refine ⟨7040910634265507636539109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693940422843671757692739 7040910634265507636539109)
                  ·
                    refine ⟨1320170743924782681851083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040910634265507636539109 1320170743924782681851083)
                    ·
                      rfl

theorem cell22_3856535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_3856535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856535 prefixEnd_3856535 := by exact prefixLift 3856535
  have htrace : WordTrace (prefixWord ++ tailWord_3856535) baseStart_3856535 baseEnd_3856535 := by
    simpa [prefixWord, tailWord_3856535, baseEnd_3856535] using wordTrace_append hprefix tailTrace_3856535
  have hstable : (prefixWord ++ tailWord_3856535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856535).length < 2 ^ (prefixWord ++ tailWord_3856535).sum := by decide
  have hdescent : baseEnd_3856535 < baseStart_3856535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856593 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_3856593 : Nat := 118140960795 + 3856593 * 2 ^ 59
def prefixEnd_3856593 : Nat := 4983230072969 + 3 ^ 40 * 3856593 * 2
def baseEnd_3856593 : Nat := 1320190598510089863900905

theorem tailTrace_3856593 : CollatzResearch.WordTrace tailWord_3856593 prefixEnd_3856593 1320190598510089863900905 := by
  unfold tailWord_3856593
  simp only [CollatzResearch.WordTrace]
  refine ⟨140661502517229689491414433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93774335011486459660942955 140661502517229689491414433)
  ·
    refine ⟨105496126887922267118560825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140661502517229689491414433 105496126887922267118560825)
    ·
      refine ⟨79122095165941700338920619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105496126887922267118560825 79122095165941700338920619)
      ·
        refine ⟨118683142748912550508380929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79122095165941700338920619 118683142748912550508380929)
        ·
          refine ⟨89012357061684412881285697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118683142748912550508380929 89012357061684412881285697)
          ·
            refine ⟨66759267796263309660964273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89012357061684412881285697 66759267796263309660964273)
            ·
              refine ⟨50069450847197482245723205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66759267796263309660964273 50069450847197482245723205)
              ·
                refine ⟨9388022033849527921073101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50069450847197482245723205 9388022033849527921073101)
                ·
                  refine ⟨3520508262693572970402413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9388022033849527921073101 3520508262693572970402413)
                  ·
                    refine ⟨1320190598510089863900905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3520508262693572970402413 1320190598510089863900905)
                    ·
                      rfl

theorem cell22_3856593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_3856593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856593 prefixEnd_3856593 := by exact prefixLift 3856593
  have htrace : WordTrace (prefixWord ++ tailWord_3856593) baseStart_3856593 baseEnd_3856593 := by
    simpa [prefixWord, tailWord_3856593, baseEnd_3856593] using wordTrace_append hprefix tailTrace_3856593
  have hstable : (prefixWord ++ tailWord_3856593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856593).length < 2 ^ (prefixWord ++ tailWord_3856593).sum := by decide
  have hdescent : baseEnd_3856593 < baseStart_3856593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856623 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 5]
def baseStart_3856623 : Nat := 118140960795 + 3856623 * 2 ^ 59
def prefixEnd_3856623 : Nat := 4983230072969 + 3 ^ 40 * 3856623 * 2
def baseEnd_3856623 : Nat := 440066956041059928550271

theorem tailTrace_3856623 : CollatzResearch.WordTrace tailWord_3856623 prefixEnd_3856623 440066956041059928550271 := by
  unfold tailWord_3856623
  simp only [CollatzResearch.WordTrace]
  refine ⟨140662596707121004615006523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93775064471414003076671015 140662596707121004615006523)
  ·
    refine ⟨210993895060681506922509785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140662596707121004615006523 210993895060681506922509785)
    ·
      refine ⟨158245421295511130191882339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210993895060681506922509785 158245421295511130191882339)
      ·
        refine ⟨237368131943266695287823509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158245421295511130191882339 237368131943266695287823509)
        ·
          refine ⟨11126631184840626341616727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237368131943266695287823509 11126631184840626341616727)
          ·
            refine ⟨16689946777260939512425091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126631184840626341616727 16689946777260939512425091)
            ·
              refine ⟨25034920165891409268637637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16689946777260939512425091 25034920165891409268637637)
              ·
                refine ⟨4694047531104639237869557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25034920165891409268637637 4694047531104639237869557)
                ·
                  refine ⟨440066956041059928550271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4694047531104639237869557 440066956041059928550271)
                  ·
                    rfl

theorem cell22_3856623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 5].length) (baseStart_3856623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856623 prefixEnd_3856623 := by exact prefixLift 3856623
  have htrace : WordTrace (prefixWord ++ tailWord_3856623) baseStart_3856623 baseEnd_3856623 := by
    simpa [prefixWord, tailWord_3856623, baseEnd_3856623] using wordTrace_append hprefix tailTrace_3856623
  have hstable : (prefixWord ++ tailWord_3856623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856623).length < 2 ^ (prefixWord ++ tailWord_3856623).sum := by decide
  have hdescent : baseEnd_3856623 < baseStart_3856623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856698 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_3856698 : Nat := 118140960795 + 3856698 * 2 ^ 59
def prefixEnd_3856698 : Nat := 4983230072969 + 3 ^ 40 * 3856698 * 2
def baseEnd_3856698 : Nat := 1320226542155904590025583

theorem tailTrace_3856698 : CollatzResearch.WordTrace tailWord_3856698 prefixEnd_3856698 1320226542155904590025583 := by
  unfold tailWord_3856698
  simp only [CollatzResearch.WordTrace]
  refine ⟨35166333045462323105996687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93776888121232861615991165 35166333045462323105996687)
  ·
    refine ⟨52749499568193484658995031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35166333045462323105996687 52749499568193484658995031)
    ·
      refine ⟨79124249352290226988492547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52749499568193484658995031 79124249352290226988492547)
      ·
        refine ⟨118686374028435340482738821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79124249352290226988492547 118686374028435340482738821)
        ·
          refine ⟨22253695130331626340513529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118686374028435340482738821 22253695130331626340513529)
          ·
            refine ⟨16690271347748719755385147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22253695130331626340513529 16690271347748719755385147)
            ·
              refine ⟨25035407021623079633077721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16690271347748719755385147 25035407021623079633077721)
              ·
                refine ⟨18776555266217309724808291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25035407021623079633077721 18776555266217309724808291)
                ·
                  refine ⟨28164832899325964587212437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18776555266217309724808291 28164832899325964587212437)
                  ·
                    refine ⟨1320226542155904590025583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28164832899325964587212437 1320226542155904590025583)
                    ·
                      rfl

theorem cell22_3856698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_3856698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856698 prefixEnd_3856698 := by exact prefixLift 3856698
  have htrace : WordTrace (prefixWord ++ tailWord_3856698) baseStart_3856698 baseEnd_3856698 := by
    simpa [prefixWord, tailWord_3856698, baseEnd_3856698] using wordTrace_append hprefix tailTrace_3856698
  have hstable : (prefixWord ++ tailWord_3856698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856698).length < 2 ^ (prefixWord ++ tailWord_3856698).sum := by decide
  have hdescent : baseEnd_3856698 < baseStart_3856698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856773 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3856773 : Nat := 118140960795 + 3856773 * 2 ^ 59
def prefixEnd_3856773 : Nat := 4983230072969 + 3 ^ 40 * 3856773 * 2
def baseEnd_3856773 : Nat := 1320252216188629394400353

theorem tailTrace_3856773 : CollatzResearch.WordTrace tailWord_3856773 prefixEnd_3856773 1320252216188629394400353 := by
  unfold tailWord_3856773
  simp only [CollatzResearch.WordTrace]
  refine ⟨140668067656577580232966973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93778711771051720155311315 140668067656577580232966973)
  ·
    refine ⟨52750525371216592587362615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140668067656577580232966973 52750525371216592587362615)
    ·
      refine ⟨79125788056824888881043923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52750525371216592587362615 79125788056824888881043923)
      ·
        refine ⟨118688682085237333321565885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79125788056824888881043923 118688682085237333321565885)
        ·
          refine ⟨44508255781963999995587207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118688682085237333321565885 44508255781963999995587207)
          ·
            refine ⟨66762383672945999993380811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44508255781963999995587207 66762383672945999993380811)
            ·
              refine ⟨100143575509418999990071217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66762383672945999993380811 100143575509418999990071217)
              ·
                refine ⟨75107681632064249992553413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100143575509418999990071217 75107681632064249992553413)
                ·
                  refine ⟨14082690306012046873603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75107681632064249992553413 14082690306012046873603765)
                  ·
                    refine ⟨1320252216188629394400353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14082690306012046873603765 1320252216188629394400353)
                    ·
                      rfl

theorem cell22_3856773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3856773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856773 prefixEnd_3856773 := by exact prefixLift 3856773
  have htrace : WordTrace (prefixWord ++ tailWord_3856773) baseStart_3856773 baseEnd_3856773 := by
    simpa [prefixWord, tailWord_3856773, baseEnd_3856773] using wordTrace_append hprefix tailTrace_3856773
  have hstable : (prefixWord ++ tailWord_3856773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856773).length < 2 ^ (prefixWord ++ tailWord_3856773).sum := by decide
  have hdescent : baseEnd_3856773 < baseStart_3856773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856792 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_3856792 : Nat := 118140960795 + 3856792 * 2 ^ 59
def prefixEnd_3856792 : Nat := 4983230072969 + 3 ^ 40 * 3856792 * 2
def baseEnd_3856792 : Nat := 440086240092306559391765

theorem tailTrace_3856792 : CollatzResearch.WordTrace tailWord_3856792 prefixEnd_3856792 440086240092306559391765 := by
  unfold tailWord_3856792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70334380321754373238954315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93779173762339164318605753 70334380321754373238954315)
  ·
    refine ⟨105501570482631559858431473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70334380321754373238954315 105501570482631559858431473)
    ·
      refine ⟨79126177861973669893823605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105501570482631559858431473 79126177861973669893823605)
      ·
        refine ⟨7418079174560031552545963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79126177861973669893823605 7418079174560031552545963)
        ·
          refine ⟨11127118761840047328818945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418079174560031552545963 11127118761840047328818945)
          ·
            refine ⟨8345339071380035496614209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11127118761840047328818945 8345339071380035496614209)
            ·
              refine ⟨6259004303535026622460657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8345339071380035496614209 6259004303535026622460657)
              ·
                refine ⟨4694253227651269966845493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6259004303535026622460657 4694253227651269966845493)
                ·
                  refine ⟨440086240092306559391765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4694253227651269966845493 440086240092306559391765)
                  ·
                    rfl

theorem cell22_3856792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_3856792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856792 prefixEnd_3856792 := by exact prefixLift 3856792
  have htrace : WordTrace (prefixWord ++ tailWord_3856792) baseStart_3856792 baseEnd_3856792 := by
    simpa [prefixWord, tailWord_3856792, baseEnd_3856792] using wordTrace_append hprefix tailTrace_3856792
  have hstable : (prefixWord ++ tailWord_3856792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856792).length < 2 ^ (prefixWord ++ tailWord_3856792).sum := by decide
  have hdescent : baseEnd_3856792 < baseStart_3856792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856835 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 4, 3]
def baseStart_3856835 : Nat := 118140960795 + 3856835 * 2 ^ 59
def prefixEnd_3856835 : Nat := 4983230072969 + 3 ^ 40 * 3856835 * 2
def baseEnd_3856835 : Nat := 1320273440055681899350163

theorem tailTrace_3856835 : CollatzResearch.WordTrace tailWord_3856835 prefixEnd_3856835 1320273440055681899350163 := by
  unfold tailWord_3856835
  simp only [CollatzResearch.WordTrace]
  refine ⟨140670328982352964821723959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93780219321568643214482639 140670328982352964821723959)
  ·
    refine ⟨211005493473529447232585939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140670328982352964821723959 211005493473529447232585939)
    ·
      refine ⟨316508240210294170848878909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211005493473529447232585939 316508240210294170848878909)
      ·
        refine ⟨118690590078860314068329591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316508240210294170848878909 118690590078860314068329591)
        ·
          refine ⟨178035885118290471102494387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118690590078860314068329591 178035885118290471102494387)
          ·
            refine ⟨267053827677435706653741581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178035885118290471102494387 267053827677435706653741581)
            ·
              refine ⟨100145185379038389995153093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267053827677435706653741581 100145185379038389995153093)
              ·
                refine ⟨18777222258569698124091205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100145185379038389995153093 18777222258569698124091205)
                ·
                  refine ⟨3520729173481818398267101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18777222258569698124091205 3520729173481818398267101)
                  ·
                    refine ⟨1320273440055681899350163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3520729173481818398267101 1320273440055681899350163)
                    ·
                      rfl

theorem cell22_3856835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 3].length) (baseStart_3856835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856835 prefixEnd_3856835 := by exact prefixLift 3856835
  have htrace : WordTrace (prefixWord ++ tailWord_3856835) baseStart_3856835 baseEnd_3856835 := by
    simpa [prefixWord, tailWord_3856835, baseEnd_3856835] using wordTrace_append hprefix tailTrace_3856835
  have hstable : (prefixWord ++ tailWord_3856835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856835).length < 2 ^ (prefixWord ++ tailWord_3856835).sum := by decide
  have hdescent : baseEnd_3856835 < baseStart_3856835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856839 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 1, 4]
def baseStart_3856839 : Nat := 118140960795 + 3856839 * 2 ^ 59
def prefixEnd_3856839 : Nat := 4983230072969 + 3 ^ 40 * 3856839 * 2
def baseEnd_3856839 : Nat := 1320274809337427222250151

theorem tailTrace_3856839 : CollatzResearch.WordTrace tailWord_3856839 prefixEnd_3856839 1320274809337427222250151 := by
  unfold tailWord_3856839
  simp only [CollatzResearch.WordTrace]
  refine ⟨140670474874338473504869571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93780316582892315669913047 140670474874338473504869571)
  ·
    refine ⟨211005712311507710257304357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140670474874338473504869571 211005712311507710257304357)
    ·
      refine ⟨39563571058407695673244567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211005712311507710257304357 39563571058407695673244567)
      ·
        refine ⟨59345356587611543509866851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39563571058407695673244567 59345356587611543509866851)
        ·
          refine ⟨89018034881417315264800277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59345356587611543509866851 89018034881417315264800277)
          ·
            refine ⟨4172720385066436653037513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89018034881417315264800277 4172720385066436653037513)
            ·
              refine ⟨3129540288799827489778135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172720385066436653037513 3129540288799827489778135)
              ·
                refine ⟨4694310433199741234667203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129540288799827489778135 4694310433199741234667203)
                ·
                  refine ⟨7041465649799611852000805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694310433199741234667203 7041465649799611852000805)
                  ·
                    refine ⟨1320274809337427222250151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7041465649799611852000805 1320274809337427222250151)
                    ·
                      rfl

theorem cell22_3856839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_3856839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856839 prefixEnd_3856839 := by exact prefixLift 3856839
  have htrace : WordTrace (prefixWord ++ tailWord_3856839) baseStart_3856839 baseEnd_3856839 := by
    simpa [prefixWord, tailWord_3856839, baseEnd_3856839] using wordTrace_append hprefix tailTrace_3856839
  have hstable : (prefixWord ++ tailWord_3856839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856839).length < 2 ^ (prefixWord ++ tailWord_3856839).sum := by decide
  have hdescent : baseEnd_3856839 < baseStart_3856839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856854 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3856854 : Nat := 118140960795 + 3856854 * 2 ^ 59
def prefixEnd_3856854 : Nat := 4983230072969 + 3 ^ 40 * 3856854 * 2
def baseEnd_3856854 : Nat := 440093314714657394375035

theorem tailTrace_3856854 : CollatzResearch.WordTrace tailWord_3856854 prefixEnd_3856854 440093314714657394375035 := by
  unfold tailWord_3856854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791938873080258191666601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93780681312856087377777077 8791938873080258191666601)
  ·
    refine ⟨6593954154810193643749951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8791938873080258191666601 6593954154810193643749951)
    ·
      refine ⟨9890931232215290465624927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6593954154810193643749951 9890931232215290465624927)
      ·
        refine ⟨14836396848322935698437391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890931232215290465624927 14836396848322935698437391)
        ·
          refine ⟨22254595272484403547656087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14836396848322935698437391 22254595272484403547656087)
          ·
            refine ⟨33381892908726605321484131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22254595272484403547656087 33381892908726605321484131)
            ·
              refine ⟨50072839363089907982226197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33381892908726605321484131 50072839363089907982226197)
              ·
                refine ⟨2347164345144839436666853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50072839363089907982226197 2347164345144839436666853)
                ·
                  refine ⟨440093314714657394375035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347164345144839436666853 440093314714657394375035)
                  ·
                    rfl

theorem cell22_3856854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3856854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856854 prefixEnd_3856854 := by exact prefixLift 3856854
  have htrace : WordTrace (prefixWord ++ tailWord_3856854) baseStart_3856854 baseEnd_3856854 := by
    simpa [prefixWord, tailWord_3856854, baseEnd_3856854] using wordTrace_append hprefix tailTrace_3856854
  have hstable : (prefixWord ++ tailWord_3856854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856854).length < 2 ^ (prefixWord ++ tailWord_3856854).sum := by decide
  have hdescent : baseEnd_3856854 < baseStart_3856854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856869 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_3856869 : Nat := 118140960795 + 3856869 * 2 ^ 59
def prefixEnd_3856869 : Nat := 4983230072969 + 3 ^ 40 * 3856869 * 2
def baseEnd_3856869 : Nat := 1320285078950517144000059

theorem tailTrace_3856869 : CollatzResearch.WordTrace tailWord_3856869 prefixEnd_3856869 1320285078950517144000059 := by
  unfold tailWord_3856869
  simp only [CollatzResearch.WordTrace]
  refine ⟨140671569064229788628461661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93781046042819859085641107 140671569064229788628461661)
  ·
    refine ⟨52751838399086170735673123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140671569064229788628461661 52751838399086170735673123)
    ·
      refine ⟨79127757598629256103509685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52751838399086170735673123 79127757598629256103509685)
      ·
        refine ⟨7418227274871492759704033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79127757598629256103509685 7418227274871492759704033)
        ·
          refine ⟨5563670456153619569778025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7418227274871492759704033 5563670456153619569778025)
          ·
            refine ⟨4172752842115214677333519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5563670456153619569778025 4172752842115214677333519)
            ·
              refine ⟨6259129263172822016000279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172752842115214677333519 6259129263172822016000279)
              ·
                refine ⟨9388693894759233024000419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259129263172822016000279 9388693894759233024000419)
                ·
                  refine ⟨14083040842138849536000629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388693894759233024000419 14083040842138849536000629)
                  ·
                    refine ⟨1320285078950517144000059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14083040842138849536000629 1320285078950517144000059)
                    ·
                      rfl

theorem cell22_3856869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_3856869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856869 prefixEnd_3856869 := by exact prefixLift 3856869
  have htrace : WordTrace (prefixWord ++ tailWord_3856869) baseStart_3856869 baseEnd_3856869 := by
    simpa [prefixWord, tailWord_3856869, baseEnd_3856869] using wordTrace_append hprefix tailTrace_3856869
  have hstable : (prefixWord ++ tailWord_3856869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856869).length < 2 ^ (prefixWord ++ tailWord_3856869).sum := by decide
  have hdescent : baseEnd_3856869 < baseStart_3856869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856882 : List Nat := [3, 2, 1, 4, 2, 1, 1, 8]
def baseStart_3856882 : Nat := 118140960795 + 3856882 * 2 ^ 59
def prefixEnd_3856882 : Nat := 4983230072969 + 3 ^ 40 * 3856882 * 2
def baseEnd_3856882 : Nat := 146698836568465493713891

theorem tailTrace_3856882 : CollatzResearch.WordTrace tailWord_3856882 prefixEnd_3856882 146698836568465493713891 := by
  unfold tailWord_3856882
  simp only [CollatzResearch.WordTrace]
  refine ⟨35168010803295672962171225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93781362142121794565789933 35168010803295672962171225)
  ·
    refine ⟨26376008102471754721628419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35168010803295672962171225 26376008102471754721628419)
    ·
      refine ⟨39564012153707632082442629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26376008102471754721628419 39564012153707632082442629)
      ·
        refine ⟨7418252278820181015457993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39564012153707632082442629 7418252278820181015457993)
        ·
          refine ⟨5563689209115135761593495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7418252278820181015457993 5563689209115135761593495)
          ·
            refine ⟨8345533813672703642390243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563689209115135761593495 8345533813672703642390243)
            ·
              refine ⟨12518300720509055463585365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8345533813672703642390243 12518300720509055463585365)
              ·
                refine ⟨146698836568465493713891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12518300720509055463585365 146698836568465493713891)
                ·
                  rfl

theorem cell22_3856882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_3856882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3856882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3856882 prefixEnd_3856882 := by exact prefixLift 3856882
  have htrace : WordTrace (prefixWord ++ tailWord_3856882) baseStart_3856882 baseEnd_3856882 := by
    simpa [prefixWord, tailWord_3856882, baseEnd_3856882] using wordTrace_append hprefix tailTrace_3856882
  have hstable : (prefixWord ++ tailWord_3856882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856882).length < 2 ^ (prefixWord ++ tailWord_3856882).sum := by decide
  have hdescent : baseEnd_3856882 < baseStart_3856882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857002 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3857002 : Nat := 118140960795 + 3857002 * 2 ^ 59
def prefixEnd_3857002 : Nat := 4983230072969 + 3 ^ 40 * 3857002 * 2
def baseEnd_3857002 : Nat := 1320330607568549130424651

theorem tailTrace_3857002 : CollatzResearch.WordTrace tailWord_3857002 prefixEnd_3857002 1320330607568549130424651 := by
  unfold tailWord_3857002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35169104993186988085763315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93784279981831968228702173 35169104993186988085763315)
  ·
    refine ⟨52753657489780482128644973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35169104993186988085763315 52753657489780482128644973)
    ·
      refine ⟨19782621558667680798241865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52753657489780482128644973 19782621558667680798241865)
      ·
        refine ⟨14836966169000760598681399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19782621558667680798241865 14836966169000760598681399)
        ·
          refine ⟨22255449253501140898022099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14836966169000760598681399 22255449253501140898022099)
          ·
            refine ⟨33383173880251711347033149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22255449253501140898022099 33383173880251711347033149)
            ·
              refine ⟨12518690205094391755137431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33383173880251711347033149 12518690205094391755137431)
              ·
                refine ⟨18778035307641587632706147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12518690205094391755137431 18778035307641587632706147)
                ·
                  refine ⟨28167052961462381449059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18778035307641587632706147 28167052961462381449059221)
                  ·
                    refine ⟨1320330607568549130424651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28167052961462381449059221 1320330607568549130424651)
                    ·
                      rfl

theorem cell22_3857002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3857002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857002 prefixEnd_3857002 := by exact prefixLift 3857002
  have htrace : WordTrace (prefixWord ++ tailWord_3857002) baseStart_3857002 baseEnd_3857002 := by
    simpa [prefixWord, tailWord_3857002, baseEnd_3857002] using wordTrace_append hprefix tailTrace_3857002
  have hstable : (prefixWord ++ tailWord_3857002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857002).length < 2 ^ (prefixWord ++ tailWord_3857002).sum := by decide
  have hdescent : baseEnd_3857002 < baseStart_3857002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857006 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_3857006 : Nat := 118140960795 + 3857006 * 2 ^ 59
def prefixEnd_3857006 : Nat := 4983230072969 + 3 ^ 40 * 3857006 * 2
def baseEnd_3857006 : Nat := 440110658950098151108213

theorem tailTrace_3857006 : CollatzResearch.WordTrace tailWord_3857006 prefixEnd_3857006 440110658950098151108213 := by
  unfold tailWord_3857006
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584570733091682628274859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93784377243155640684132581 17584570733091682628274859)
  ·
    refine ⟨26376856099637523942412289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17584570733091682628274859 26376856099637523942412289)
    ·
      refine ⟨19782642074728142956809217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26376856099637523942412289 19782642074728142956809217)
      ·
        refine ⟨14836981556046107217606913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19782642074728142956809217 14836981556046107217606913)
        ·
          refine ⟨11127736167034580413205185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14836981556046107217606913 11127736167034580413205185)
          ·
            refine ⟨8345802125275935309903889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11127736167034580413205185 8345802125275935309903889)
            ·
              refine ⟨6259351593956951482427917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8345802125275935309903889 6259351593956951482427917)
              ·
                refine ⟨2347256847733856805910469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6259351593956951482427917 2347256847733856805910469)
                ·
                  refine ⟨440110658950098151108213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347256847733856805910469 440110658950098151108213)
                  ·
                    rfl

theorem cell22_3857006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_3857006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857006 prefixEnd_3857006 := by exact prefixLift 3857006
  have htrace : WordTrace (prefixWord ++ tailWord_3857006) baseStart_3857006 baseEnd_3857006 := by
    simpa [prefixWord, tailWord_3857006, baseEnd_3857006] using wordTrace_append hprefix tailTrace_3857006
  have hstable : (prefixWord ++ tailWord_3857006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857006).length < 2 ^ (prefixWord ++ tailWord_3857006).sum := by decide
  have hdescent : baseEnd_3857006 < baseStart_3857006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857008 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 1, 4]
def baseStart_3857008 : Nat := 118140960795 + 3857008 * 2 ^ 59
def prefixEnd_3857008 : Nat := 4983230072969 + 3 ^ 40 * 3857008 * 2
def baseEnd_3857008 : Nat := 1320332661491167114774633

theorem tailTrace_3857008 : CollatzResearch.WordTrace tailWord_3857008 prefixEnd_3857008 1320332661491167114774633 := by
  unfold tailWord_3857008
  simp only [CollatzResearch.WordTrace]
  refine ⟨70338319405363107683885839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93784425873817476911847785 70338319405363107683885839)
  ·
    refine ⟨105507479108044661525828759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70338319405363107683885839 105507479108044661525828759)
    ·
      refine ⟨158261218662066992288743139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105507479108044661525828759 158261218662066992288743139)
      ·
        refine ⟨237391827993100488433114709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158261218662066992288743139 237391827993100488433114709)
        ·
          refine ⟨2781935484294146348825563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 237391827993100488433114709 2781935484294146348825563)
          ·
            refine ⟨4172903226441219523238345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781935484294146348825563 4172903226441219523238345)
            ·
              refine ⟨3129677419830914642428759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172903226441219523238345 3129677419830914642428759)
              ·
                refine ⟨4694516129746371963643139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129677419830914642428759 4694516129746371963643139)
                ·
                  refine ⟨7041774194619557945464709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694516129746371963643139 7041774194619557945464709)
                  ·
                    refine ⟨1320332661491167114774633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7041774194619557945464709 1320332661491167114774633)
                    ·
                      rfl

theorem cell22_3857008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_3857008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857008 prefixEnd_3857008 := by exact prefixLift 3857008
  have htrace : WordTrace (prefixWord ++ tailWord_3857008) baseStart_3857008 baseEnd_3857008 := by
    simpa [prefixWord, tailWord_3857008, baseEnd_3857008] using wordTrace_append hprefix tailTrace_3857008
  have hstable : (prefixWord ++ tailWord_3857008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857008).length < 2 ^ (prefixWord ++ tailWord_3857008).sum := by decide
  have hdescent : baseEnd_3857008 < baseStart_3857008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857096 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 5]
def baseStart_3857096 : Nat := 118140960795 + 3857096 * 2 ^ 59
def prefixEnd_3857096 : Nat := 4983230072969 + 3 ^ 40 * 3857096 * 2
def baseEnd_3857096 : Nat := 440120928563188072858121

theorem tailTrace_3857096 : CollatzResearch.WordTrace tailWord_3857096 prefixEnd_3857096 440120928563188072858121 := by
  unfold tailWord_3857096
  simp only [CollatzResearch.WordTrace]
  refine ⟨70339924217203703198487571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93786565622938270931316761 70339924217203703198487571)
  ·
    refine ⟨105509886325805554797731357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70339924217203703198487571 105509886325805554797731357)
    ·
      refine ⟨39566207372177083049149259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105509886325805554797731357 39566207372177083049149259)
      ·
        refine ⟨59349311058265624573723889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39566207372177083049149259 59349311058265624573723889)
        ·
          refine ⟨44511983293699218430292917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59349311058265624573723889 44511983293699218430292917)
          ·
            refine ⟨4172998433784301727839961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44511983293699218430292917 4172998433784301727839961)
            ·
              refine ⟨3129748825338226295879971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172998433784301727839961 3129748825338226295879971)
              ·
                refine ⟨4694623238007339443819957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129748825338226295879971 4694623238007339443819957)
                ·
                  refine ⟨440120928563188072858121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4694623238007339443819957 440120928563188072858121)
                  ·
                    rfl

theorem cell22_3857096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_3857096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857096 prefixEnd_3857096 := by exact prefixLift 3857096
  have htrace : WordTrace (prefixWord ++ tailWord_3857096) baseStart_3857096 baseEnd_3857096 := by
    simpa [prefixWord, tailWord_3857096, baseEnd_3857096] using wordTrace_append hprefix tailTrace_3857096
  have hstable : (prefixWord ++ tailWord_3857096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857096).length < 2 ^ (prefixWord ++ tailWord_3857096).sum := by decide
  have hdescent : baseEnd_3857096 < baseStart_3857096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857156 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_3857156 : Nat := 118140960795 + 3857156 * 2 ^ 59
def prefixEnd_3857156 : Nat := 4983230072969 + 3 ^ 40 * 3857156 * 2
def baseEnd_3857156 : Nat := 1320383324915744062074179

theorem tailTrace_3857156 : CollatzResearch.WordTrace tailWord_3857156 prefixEnd_3857156 1320383324915744062074179 := by
  unfold tailWord_3857156
  simp only [CollatzResearch.WordTrace]
  refine ⟨70341018407095018322079661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93788024542793357762772881 70341018407095018322079661)
  ·
    refine ⟨26377881902660631870779873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70341018407095018322079661 26377881902660631870779873)
    ·
      refine ⟨19783411426995473903084905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26377881902660631870779873 19783411426995473903084905)
      ·
        refine ⟨14837558570246605427313679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19783411426995473903084905 14837558570246605427313679)
        ·
          refine ⟨22256337855369908140970519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14837558570246605427313679 22256337855369908140970519)
          ·
            refine ⟨33384506783054862211455779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22256337855369908140970519 33384506783054862211455779)
            ·
              refine ⟨50076760174582293317183669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33384506783054862211455779 50076760174582293317183669)
              ·
                refine ⟨4694696266367089998485969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50076760174582293317183669 4694696266367089998485969)
                ·
                  refine ⟨3521022199775317498864477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4694696266367089998485969 3521022199775317498864477)
                  ·
                    refine ⟨1320383324915744062074179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521022199775317498864477 1320383324915744062074179)
                    ·
                      rfl

theorem cell22_3857156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_3857156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857156 prefixEnd_3857156 := by exact prefixLift 3857156
  have htrace : WordTrace (prefixWord ++ tailWord_3857156) baseStart_3857156 baseEnd_3857156 := by
    simpa [prefixWord, tailWord_3857156, baseEnd_3857156] using wordTrace_append hprefix tailTrace_3857156
  have hstable : (prefixWord ++ tailWord_3857156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857156).length < 2 ^ (prefixWord ++ tailWord_3857156).sum := by decide
  have hdescent : baseEnd_3857156 < baseStart_3857156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857201 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_3857201 : Nat := 118140960795 + 3857201 * 2 ^ 59
def prefixEnd_3857201 : Nat := 4983230072969 + 3 ^ 40 * 3857201 * 2
def baseEnd_3857201 : Nat := 1320398729335378944699041

theorem tailTrace_3857201 : CollatzResearch.WordTrace tailWord_3857201 prefixEnd_3857201 1320398729335378944699041 := by
  unfold tailWord_3857201
  simp only [CollatzResearch.WordTrace]
  refine ⟨140683678099027009329547457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93789118732684672886364971 140683678099027009329547457)
  ·
    refine ⟨105512758574270256997160593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140683678099027009329547457 105512758574270256997160593)
    ·
      refine ⟨79134568930702692747870445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105512758574270256997160593 79134568930702692747870445)
      ·
        refine ⟨29675463349013509780451417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79134568930702692747870445 29675463349013509780451417)
        ·
          refine ⟨22256597511760132335338563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29675463349013509780451417 22256597511760132335338563)
          ·
            refine ⟨33384896267640198503007845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22256597511760132335338563 33384896267640198503007845)
            ·
              refine ⟨6259668050182537219313971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33384896267640198503007845 6259668050182537219313971)
              ·
                refine ⟨9389502075273805828970957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259668050182537219313971 9389502075273805828970957)
                ·
                  refine ⟨3521063278227677185864109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9389502075273805828970957 3521063278227677185864109)
                  ·
                    refine ⟨1320398729335378944699041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521063278227677185864109 1320398729335378944699041)
                    ·
                      rfl

theorem cell22_3857201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_3857201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857201 prefixEnd_3857201 := by exact prefixLift 3857201
  have htrace : WordTrace (prefixWord ++ tailWord_3857201) baseStart_3857201 baseEnd_3857201 := by
    simpa [prefixWord, tailWord_3857201, baseEnd_3857201] using wordTrace_append hprefix tailTrace_3857201
  have hstable : (prefixWord ++ tailWord_3857201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857201).length < 2 ^ (prefixWord ++ tailWord_3857201).sum := by decide
  have hdescent : baseEnd_3857201 < baseStart_3857201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857220 : List Nat := [2, 3, 4, 2, 1, 2, 2, 6]
def baseStart_3857220 : Nat := 118140960795 + 3857220 * 2 ^ 59
def prefixEnd_3857220 : Nat := 4983230072969 + 3 ^ 40 * 3857220 * 2
def baseEnd_3857220 : Nat := 146711692602629914274887

theorem tailTrace_3857220 : CollatzResearch.WordTrace tailWord_3857220 prefixEnd_3857220 146711692602629914274887 := by
  unfold tailWord_3857220
  simp only [CollatzResearch.WordTrace]
  refine ⟨70342185542979087787244557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93789580723972117049659409 70342185542979087787244557)
  ·
    refine ⟨26378319578617157920216709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70342185542979087787244557 26378319578617157920216709)
    ·
      refine ⟨4945934920990717110040633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26378319578617157920216709 4945934920990717110040633)
      ·
        refine ⟨3709451190743037832530475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4945934920990717110040633 3709451190743037832530475)
        ·
          refine ⟨5564176786114556748795713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709451190743037832530475 5564176786114556748795713)
          ·
            refine ⟨4173132589585917561596785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5564176786114556748795713 4173132589585917561596785)
            ·
              refine ⟨3129849442189438171197589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173132589585917561596785 3129849442189438171197589)
              ·
                refine ⟨146711692602629914274887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3129849442189438171197589 146711692602629914274887)
                ·
                  rfl

theorem cell22_3857220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 6].length) (baseStart_3857220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857220 prefixEnd_3857220 := by exact prefixLift 3857220
  have htrace : WordTrace (prefixWord ++ tailWord_3857220) baseStart_3857220 baseEnd_3857220 := by
    simpa [prefixWord, tailWord_3857220, baseEnd_3857220] using wordTrace_append hprefix tailTrace_3857220
  have hstable : (prefixWord ++ tailWord_3857220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857220).length < 2 ^ (prefixWord ++ tailWord_3857220).sum := by decide
  have hdescent : baseEnd_3857220 < baseStart_3857220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857227 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_3857227 : Nat := 118140960795 + 3857227 * 2 ^ 59
def prefixEnd_3857227 : Nat := 4983230072969 + 3 ^ 40 * 3857227 * 2
def baseEnd_3857227 : Nat := 1320407629666723543548961

theorem tailTrace_3857227 : CollatzResearch.WordTrace tailWord_3857227 prefixEnd_3857227 1320407629666723543548961 := by
  unfold tailWord_3857227
  simp only [CollatzResearch.WordTrace]
  refine ⟨140684626396932815769993935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93789750931288543846662623 140684626396932815769993935)
  ·
    refine ⟨211026939595399223654990903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140684626396932815769993935 211026939595399223654990903)
    ·
      refine ⟨316540409393098835482486355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211026939595399223654990903 316540409393098835482486355)
      ·
        refine ⟨474810614089648253223729533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316540409393098835482486355 474810614089648253223729533)
        ·
          refine ⟨178053980283618094958898575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474810614089648253223729533 178053980283618094958898575)
          ·
            refine ⟨267080970425427142438347863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178053980283618094958898575 267080970425427142438347863)
            ·
              refine ⟨400621455638140713657521795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267080970425427142438347863 400621455638140713657521795)
              ·
                refine ⟨600932183457211070486282693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400621455638140713657521795 600932183457211070486282693)
                ·
                  refine ⟨112674784398227075716178005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600932183457211070486282693 112674784398227075716178005)
                  ·
                    refine ⟨1320407629666723543548961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112674784398227075716178005 1320407629666723543548961)
                    ·
                      rfl

theorem cell22_3857227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_3857227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857227 prefixEnd_3857227 := by exact prefixLift 3857227
  have htrace : WordTrace (prefixWord ++ tailWord_3857227) baseStart_3857227 baseEnd_3857227 := by
    simpa [prefixWord, tailWord_3857227, baseEnd_3857227] using wordTrace_append hprefix tailTrace_3857227
  have hstable : (prefixWord ++ tailWord_3857227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857227).length < 2 ^ (prefixWord ++ tailWord_3857227).sum := by decide
  have hdescent : baseEnd_3857227 < baseStart_3857227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857259 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 6]
def baseStart_3857259 : Nat := 118140960795 + 3857259 * 2 ^ 59
def prefixEnd_3857259 : Nat := 4983230072969 + 3 ^ 40 * 3857259 * 2
def baseEnd_3857259 : Nat := 440139527973562042249621

theorem tailTrace_3857259 : CollatzResearch.WordTrace tailWord_3857259 prefixEnd_3857259 440139527973562042249621 := by
  unfold tailWord_3857259
  simp only [CollatzResearch.WordTrace]
  refine ⟨140685793532816885235158831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93790529021877923490105887 140685793532816885235158831)
  ·
    refine ⟨211028690299225327852738247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140685793532816885235158831 211028690299225327852738247)
    ·
      refine ⟨316543035448837991779107371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211028690299225327852738247 316543035448837991779107371)
      ·
        refine ⟨474814553173256987668661057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316543035448837991779107371 474814553173256987668661057)
        ·
          refine ⟨356110914879942740751495793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474814553173256987668661057 356110914879942740751495793)
          ·
            refine ⟨267083186159957055563621845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356110914879942740751495793 267083186159957055563621845)
            ·
              refine ⟨6259762175623993489772387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267083186159957055563621845 6259762175623993489772387)
              ·
                refine ⟨9389643263435990234658581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259762175623993489772387 9389643263435990234658581)
                ·
                  refine ⟨440139527973562042249621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9389643263435990234658581 440139527973562042249621)
                  ·
                    rfl

theorem cell22_3857259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 6].length) (baseStart_3857259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857259 prefixEnd_3857259 := by exact prefixLift 3857259
  have htrace : WordTrace (prefixWord ++ tailWord_3857259) baseStart_3857259 baseEnd_3857259 := by
    simpa [prefixWord, tailWord_3857259, baseEnd_3857259] using wordTrace_append hprefix tailTrace_3857259
  have hstable : (prefixWord ++ tailWord_3857259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857259).length < 2 ^ (prefixWord ++ tailWord_3857259).sum := by decide
  have hdescent : baseEnd_3857259 < baseStart_3857259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857274 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_3857274 : Nat := 118140960795 + 3857274 * 2 ^ 59
def prefixEnd_3857274 : Nat := 4983230072969 + 3 ^ 40 * 3857274 * 2
def baseEnd_3857274 : Nat := 1320423718727231087623817

theorem tailTrace_3857274 : CollatzResearch.WordTrace tailWord_3857274 prefixEnd_3857274 1320423718727231087623817 := by
  unfold tailWord_3857274
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171585156940635699238719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93790893751841695197969917 35171585156940635699238719)
  ·
    refine ⟨52757377735410953548858079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35171585156940635699238719 52757377735410953548858079)
    ·
      refine ⟨79136066603116430323287119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52757377735410953548858079 79136066603116430323287119)
      ·
        refine ⟨118704099904674645484930679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79136066603116430323287119 118704099904674645484930679)
        ·
          refine ⟨178056149857011968227396019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118704099904674645484930679 178056149857011968227396019)
          ·
            refine ⟨267084224785517952341094029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178056149857011968227396019 267084224785517952341094029)
            ·
              refine ⟨100156584294569232127910261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267084224785517952341094029 100156584294569232127910261)
              ·
                refine ⟨9389679777615865511991587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100156584294569232127910261 9389679777615865511991587)
                ·
                  refine ⟨14084519666423798267987381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9389679777615865511991587 14084519666423798267987381)
                  ·
                    refine ⟨1320423718727231087623817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14084519666423798267987381 1320423718727231087623817)
                    ·
                      rfl

theorem cell22_3857274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_3857274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857274 prefixEnd_3857274 := by exact prefixLift 3857274
  have htrace : WordTrace (prefixWord ++ tailWord_3857274) baseStart_3857274 baseEnd_3857274 := by
    simpa [prefixWord, tailWord_3857274, baseEnd_3857274] using wordTrace_append hprefix tailTrace_3857274
  have hstable : (prefixWord ++ tailWord_3857274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857274).length < 2 ^ (prefixWord ++ tailWord_3857274).sum := by decide
  have hdescent : baseEnd_3857274 < baseStart_3857274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857325 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3857325 : Nat := 118140960795 + 3857325 * 2 ^ 59
def prefixEnd_3857325 : Nat := 4983230072969 + 3 ^ 40 * 3857325 * 2
def baseEnd_3857325 : Nat := 1320441177069483954598661

theorem tailTrace_3857325 : CollatzResearch.WordTrace tailWord_3857325 prefixEnd_3857325 1320441177069483954598661 := by
  unfold tailWord_3857325
  simp only [CollatzResearch.WordTrace]
  refine ⟨140688200750577778507061429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93792133833718519004707619 140688200750577778507061429)
  ·
    refine ⟨13189518820366666735037009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140688200750577778507061429 13189518820366666735037009)
    ·
      refine ⟨9892139115275000051277757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13189518820366666735037009 9892139115275000051277757)
      ·
        refine ⟨3709552168228125019229159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9892139115275000051277757 3709552168228125019229159)
        ·
          refine ⟨5564328252342187528843739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709552168228125019229159 5564328252342187528843739)
          ·
            refine ⟨8346492378513281293265609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564328252342187528843739 8346492378513281293265609)
            ·
              refine ⟨6259869283884960969949207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346492378513281293265609 6259869283884960969949207)
              ·
                refine ⟨9389803925827441454923811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259869283884960969949207 9389803925827441454923811)
                ·
                  refine ⟨14084705888741162182385717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9389803925827441454923811 14084705888741162182385717)
                  ·
                    refine ⟨1320441177069483954598661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14084705888741162182385717 1320441177069483954598661)
                    ·
                      rfl

theorem cell22_3857325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3857325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857325 prefixEnd_3857325 := by exact prefixLift 3857325
  have htrace : WordTrace (prefixWord ++ tailWord_3857325) baseStart_3857325 baseEnd_3857325 := by
    simpa [prefixWord, tailWord_3857325, baseEnd_3857325] using wordTrace_append hprefix tailTrace_3857325
  have hstable : (prefixWord ++ tailWord_3857325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857325).length < 2 ^ (prefixWord ++ tailWord_3857325).sum := by decide
  have hdescent : baseEnd_3857325 < baseStart_3857325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857336 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_3857336 : Nat := 118140960795 + 3857336 * 2 ^ 59
def prefixEnd_3857336 : Nat := 4983230072969 + 3 ^ 40 * 3857336 * 2
def baseEnd_3857336 : Nat := 1320444942594283592573627

theorem tailTrace_3857336 : CollatzResearch.WordTrace tailWord_3857336 prefixEnd_3857336 1320444942594283592573627 := by
  unfold tailWord_3857336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70344300976768963692855931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93792401302358618257141241 70344300976768963692855931)
  ·
    refine ⟨105516451465153445539283897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70344300976768963692855931 105516451465153445539283897)
    ·
      refine ⟨79137338598865084154462923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105516451465153445539283897 79137338598865084154462923)
      ·
        refine ⟨118706007898297626231694385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79137338598865084154462923 118706007898297626231694385)
        ·
          refine ⟨89029505923723219673770789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118706007898297626231694385 89029505923723219673770789)
          ·
            refine ⟨16693032360698103688832023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89029505923723219673770789 16693032360698103688832023)
            ·
              refine ⟨25039548541047155533248035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16693032360698103688832023 25039548541047155533248035)
              ·
                refine ⟨37559322811570733299872053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25039548541047155533248035 37559322811570733299872053)
                ·
                  refine ⟨3521186513584756246863005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37559322811570733299872053 3521186513584756246863005)
                  ·
                    refine ⟨1320444942594283592573627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521186513584756246863005 1320444942594283592573627)
                    ·
                      rfl

theorem cell22_3857336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_3857336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857336 prefixEnd_3857336 := by exact prefixLift 3857336
  have htrace : WordTrace (prefixWord ++ tailWord_3857336) baseStart_3857336 baseEnd_3857336 := by
    simpa [prefixWord, tailWord_3857336, baseEnd_3857336] using wordTrace_append hprefix tailTrace_3857336
  have hstable : (prefixWord ++ tailWord_3857336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857336).length < 2 ^ (prefixWord ++ tailWord_3857336).sum := by decide
  have hdescent : baseEnd_3857336 < baseStart_3857336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857370 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_3857370 : Nat := 118140960795 + 3857370 * 2 ^ 59
def prefixEnd_3857370 : Nat := 4983230072969 + 3 ^ 40 * 3857370 * 2
def baseEnd_3857370 : Nat := 1320456581489118837223523

theorem tailTrace_3857370 : CollatzResearch.WordTrace tailWord_3857370 prefixEnd_3857370 1320456581489118837223523 := by
  unfold tailWord_3857370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35172460508853687798112391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93793228023609834128299709 35172460508853687798112391)
  ·
    refine ⟨52758690763280531697168587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35172460508853687798112391 52758690763280531697168587)
    ·
      refine ⟨79138036144920797545752881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52758690763280531697168587 79138036144920797545752881)
      ·
        refine ⟨59353527108690598159314661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79138036144920797545752881 59353527108690598159314661)
        ·
          refine ⟨11128786332879487154871499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59353527108690598159314661 11128786332879487154871499)
          ·
            refine ⟨16693179499319230732307249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128786332879487154871499 16693179499319230732307249)
            ·
              refine ⟨12519884624489423049230437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16693179499319230732307249 12519884624489423049230437)
              ·
                refine ⟨2347478367091766821730707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12519884624489423049230437 2347478367091766821730707)
                ·
                  refine ⟨3521217550637650232596061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347478367091766821730707 3521217550637650232596061)
                  ·
                    refine ⟨1320456581489118837223523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521217550637650232596061 1320456581489118837223523)
                    ·
                      rfl

theorem cell22_3857370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_3857370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857370 prefixEnd_3857370 := by exact prefixLift 3857370
  have htrace : WordTrace (prefixWord ++ tailWord_3857370) baseStart_3857370 baseEnd_3857370 := by
    simpa [prefixWord, tailWord_3857370, baseEnd_3857370] using wordTrace_append hprefix tailTrace_3857370
  have hstable : (prefixWord ++ tailWord_3857370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857370).length < 2 ^ (prefixWord ++ tailWord_3857370).sum := by decide
  have hdescent : baseEnd_3857370 < baseStart_3857370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857447 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3857447 : Nat := 118140960795 + 3857447 * 2 ^ 59
def prefixEnd_3857447 : Nat := 4983230072969 + 3 ^ 40 * 3857447 * 2
def baseEnd_3857447 : Nat := 1320482940162716303048287

theorem tailTrace_3857447 : CollatzResearch.WordTrace tailWord_3857447 prefixEnd_3857447 1320482940162716303048287 := by
  unfold tailWord_3857447
  simp only [CollatzResearch.WordTrace]
  refine ⟨140692650456135793343002595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93795100304090528895335063 140692650456135793343002595)
  ·
    refine ⟨211038975684203690014503893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140692650456135793343002595 211038975684203690014503893)
    ·
      refine ⟨4946225992598523984714935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 211038975684203690014503893 4946225992598523984714935)
      ·
        refine ⟨7419338988897785977072403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946225992598523984714935 7419338988897785977072403)
        ·
          refine ⟨11129008483346678965608605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419338988897785977072403 11129008483346678965608605)
          ·
            refine ⟨4173378181255004612103227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11129008483346678965608605 4173378181255004612103227)
            ·
              refine ⟨6260067271882506918154841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173378181255004612103227 6260067271882506918154841)
              ·
                refine ⟨4695050453911880188616131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6260067271882506918154841 4695050453911880188616131)
                ·
                  refine ⟨7042575680867820282924197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695050453911880188616131 7042575680867820282924197)
                  ·
                    refine ⟨1320482940162716303048287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042575680867820282924197 1320482940162716303048287)
                    ·
                      rfl

theorem cell22_3857447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3857447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857447 prefixEnd_3857447 := by exact prefixLift 3857447
  have htrace : WordTrace (prefixWord ++ tailWord_3857447) baseStart_3857447 baseEnd_3857447 := by
    simpa [prefixWord, tailWord_3857447, baseEnd_3857447] using wordTrace_append hprefix tailTrace_3857447
  have hstable : (prefixWord ++ tailWord_3857447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857447).length < 2 ^ (prefixWord ++ tailWord_3857447).sum := by decide
  have hdescent : baseEnd_3857447 < baseStart_3857447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857458 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_3857458 : Nat := 118140960795 + 3857458 * 2 ^ 59
def prefixEnd_3857458 : Nat := 4983230072969 + 3 ^ 40 * 3857458 * 2
def baseEnd_3857458 : Nat := 1320486705687515941023253

theorem tailTrace_3857458 : CollatzResearch.WordTrace tailWord_3857458 prefixEnd_3857458 1320486705687515941023253 := by
  unfold tailWord_3857458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35173262914773985555413257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93795367772730628147768685 35173262914773985555413257)
  ·
    refine ⟨26379947186080489166559943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35173262914773985555413257 26379947186080489166559943)
    ·
      refine ⟨39569920779120733749839915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26379947186080489166559943 39569920779120733749839915)
      ·
        refine ⟨59354881168681100624759873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39569920779120733749839915 59354881168681100624759873)
        ·
          refine ⟨44516160876510825468569905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59354881168681100624759873 44516160876510825468569905)
          ·
            refine ⟨33387120657383119101427429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44516160876510825468569905 33387120657383119101427429)
            ·
              refine ⟨6260085123259334831517643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33387120657383119101427429 6260085123259334831517643)
              ·
                refine ⟨9390127684889002247276465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260085123259334831517643 9390127684889002247276465)
                ·
                  refine ⟨7042595763666751685457349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390127684889002247276465 7042595763666751685457349)
                  ·
                    refine ⟨1320486705687515941023253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042595763666751685457349 1320486705687515941023253)
                    ·
                      rfl

theorem cell22_3857458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_3857458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857458 prefixEnd_3857458 := by exact prefixLift 3857458
  have htrace : WordTrace (prefixWord ++ tailWord_3857458) baseStart_3857458 baseEnd_3857458 := by
    simpa [prefixWord, tailWord_3857458, baseEnd_3857458] using wordTrace_append hprefix tailTrace_3857458
  have hstable : (prefixWord ++ tailWord_3857458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857458).length < 2 ^ (prefixWord ++ tailWord_3857458).sum := by decide
  have hdescent : baseEnd_3857458 < baseStart_3857458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857460 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3857460 : Nat := 118140960795 + 3857460 * 2 ^ 59
def prefixEnd_3857460 : Nat := 4983230072969 + 3 ^ 40 * 3857460 * 2
def baseEnd_3857460 : Nat := 1320487390328388602473247

theorem tailTrace_3857460 : CollatzResearch.WordTrace tailWord_3857460 prefixEnd_3857460 1320487390328388602473247 := by
  unfold tailWord_3857460
  simp only [CollatzResearch.WordTrace]
  refine ⟨70346562302544348281612917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93795416403392464375483889 70346562302544348281612917)
  ·
    refine ⟨6594990215863532651401211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70346562302544348281612917 6594990215863532651401211)
    ·
      refine ⟨9892485323795298977101817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6594990215863532651401211 9892485323795298977101817)
      ·
        refine ⟨7419363992846474232826363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9892485323795298977101817 7419363992846474232826363)
        ·
          refine ⟨11129045989269711349239545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419363992846474232826363 11129045989269711349239545)
          ·
            refine ⟨8346784491952283511929659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11129045989269711349239545 8346784491952283511929659)
            ·
              refine ⟨12520176737928425267894489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8346784491952283511929659 12520176737928425267894489)
              ·
                refine ⟨9390132553446318950920867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12520176737928425267894489 9390132553446318950920867)
                ·
                  refine ⟨14085198830169478426381301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9390132553446318950920867 14085198830169478426381301)
                  ·
                    refine ⟨1320487390328388602473247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14085198830169478426381301 1320487390328388602473247)
                    ·
                      rfl

theorem cell22_3857460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3857460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857460 prefixEnd_3857460 := by exact prefixLift 3857460
  have htrace : WordTrace (prefixWord ++ tailWord_3857460) baseStart_3857460 baseEnd_3857460 := by
    simpa [prefixWord, tailWord_3857460, baseEnd_3857460] using wordTrace_append hprefix tailTrace_3857460
  have hstable : (prefixWord ++ tailWord_3857460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857460).length < 2 ^ (prefixWord ++ tailWord_3857460).sum := by decide
  have hdescent : baseEnd_3857460 < baseStart_3857460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857473 : List Nat := [1, 2, 5, 1, 4, 9]
def baseStart_3857473 : Nat := 118140960795 + 3857473 * 2 ^ 59
def prefixEnd_3857473 : Nat := 4983230072969 + 3 ^ 40 * 3857473 * 2
def baseEnd_3857473 : Nat := 16302368401161245702447

theorem tailTrace_3857473 : CollatzResearch.WordTrace tailWord_3857473 prefixEnd_3857473 16302368401161245702447 := by
  unfold tailWord_3857473
  simp only [CollatzResearch.WordTrace]
  refine ⟨140693598754041599783449073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93795732502694399855632715 140693598754041599783449073)
  ·
    refine ⟨105520199065531199837586805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140693598754041599783449073 105520199065531199837586805)
    ·
      refine ⟨9892518662393549984773763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105520199065531199837586805 9892518662393549984773763)
      ·
        refine ⟨14838777993590324977160645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9892518662393549984773763 14838777993590324977160645)
        ·
          refine ⟨2782270873798185933217621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14838777993590324977160645 2782270873798185933217621)
          ·
            refine ⟨16302368401161245702447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2782270873798185933217621 16302368401161245702447)
            ·
              rfl

theorem cell22_3857473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 9].length) (baseStart_3857473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857473 prefixEnd_3857473 := by exact prefixLift 3857473
  have htrace : WordTrace (prefixWord ++ tailWord_3857473) baseStart_3857473 baseEnd_3857473 := by
    simpa [prefixWord, tailWord_3857473, baseEnd_3857473] using wordTrace_append hprefix tailTrace_3857473
  have hstable : (prefixWord ++ tailWord_3857473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857473).length < 2 ^ (prefixWord ++ tailWord_3857473).sum := by decide
  have hdescent : baseEnd_3857473 < baseStart_3857473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857486 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_3857486 : Nat := 118140960795 + 3857486 * 2 ^ 59
def prefixEnd_3857486 : Nat := 4983230072969 + 3 ^ 40 * 3857486 * 2
def baseEnd_3857486 : Nat := 1320496290659733201323167

theorem tailTrace_3857486 : CollatzResearch.WordTrace tailWord_3857486 prefixEnd_3857486 1320496290659733201323167 := by
  unfold tailWord_3857486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17586759112874312875459039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93796048601996335335781541 17586759112874312875459039)
  ·
    refine ⟨26380138669311469313188559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17586759112874312875459039 26380138669311469313188559)
    ·
      refine ⟨39570208003967203969782839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26380138669311469313188559 39570208003967203969782839)
      ·
        refine ⟨59355312005950805954674259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39570208003967203969782839 59355312005950805954674259)
        ·
          refine ⟨89032968008926208932011389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59355312005950805954674259 89032968008926208932011389)
          ·
            refine ⟨33387363003347328349504271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89032968008926208932011389 33387363003347328349504271)
            ·
              refine ⟨50081044505020992524256407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33387363003347328349504271 50081044505020992524256407)
              ·
                refine ⟨75121566757531488786384611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50081044505020992524256407 75121566757531488786384611)
                ·
                  refine ⟨112682350136297233179576917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75121566757531488786384611 112682350136297233179576917)
                  ·
                    refine ⟨1320496290659733201323167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112682350136297233179576917 1320496290659733201323167)
                    ·
                      rfl

theorem cell22_3857486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_3857486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857486 prefixEnd_3857486 := by exact prefixLift 3857486
  have htrace : WordTrace (prefixWord ++ tailWord_3857486) baseStart_3857486 baseEnd_3857486 := by
    simpa [prefixWord, tailWord_3857486, baseEnd_3857486] using wordTrace_append hprefix tailTrace_3857486
  have hstable : (prefixWord ++ tailWord_3857486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857486).length < 2 ^ (prefixWord ++ tailWord_3857486).sum := by decide
  have hdescent : baseEnd_3857486 < baseStart_3857486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857516 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_3857516 : Nat := 118140960795 + 3857516 * 2 ^ 59
def prefixEnd_3857516 : Nat := 4983230072969 + 3 ^ 40 * 3857516 * 2
def baseEnd_3857516 : Nat := 1320506560272823123073075

theorem tailTrace_3857516 : CollatzResearch.WordTrace tailWord_3857516 prefixEnd_3857516 1320506560272823123073075 := by
  unfold tailWord_3857516
  simp only [CollatzResearch.WordTrace]
  refine ⟨70347583546442909063632201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93796778061923878751509601 70347583546442909063632201)
  ·
    refine ⟨52760687659832181797724151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70347583546442909063632201 52760687659832181797724151)
    ·
      refine ⟨79141031489748272696586227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52760687659832181797724151 79141031489748272696586227)
      ·
        refine ⟨118711547234622409044879341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79141031489748272696586227 118711547234622409044879341)
        ·
          refine ⟨44516830212983403391829753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118711547234622409044879341 44516830212983403391829753)
          ·
            refine ⟨33387622659737552543872315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44516830212983403391829753 33387622659737552543872315)
            ·
              refine ⟨50081433989606328815808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33387622659737552543872315 50081433989606328815808473)
              ·
                refine ⟨37561075492204746611856355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50081433989606328815808473 37561075492204746611856355)
                ·
                  refine ⟨56341613238307119917784533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37561075492204746611856355 56341613238307119917784533)
                  ·
                    refine ⟨1320506560272823123073075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56341613238307119917784533 1320506560272823123073075)
                    ·
                      rfl

theorem cell22_3857516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_3857516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857516 prefixEnd_3857516 := by exact prefixLift 3857516
  have htrace : WordTrace (prefixWord ++ tailWord_3857516) baseStart_3857516 baseEnd_3857516 := by
    simpa [prefixWord, tailWord_3857516, baseEnd_3857516] using wordTrace_append hprefix tailTrace_3857516
  have hstable : (prefixWord ++ tailWord_3857516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857516).length < 2 ^ (prefixWord ++ tailWord_3857516).sum := by decide
  have hdescent : baseEnd_3857516 < baseStart_3857516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857522 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_3857522 : Nat := 118140960795 + 3857522 * 2 ^ 59
def prefixEnd_3857522 : Nat := 4983230072969 + 3 ^ 40 * 3857522 * 2
def baseEnd_3857522 : Nat := 1320508614195441107423057

theorem tailTrace_3857522 : CollatzResearch.WordTrace tailWord_3857522 prefixEnd_3857522 1320508614195441107423057 := by
  unfold tailWord_3857522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35173846482716020287995705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93796923953909387434655213 35173846482716020287995705)
  ·
    refine ⟨26380384862037015215996779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35173846482716020287995705 26380384862037015215996779)
    ·
      refine ⟨39570577293055522823995169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26380384862037015215996779 39570577293055522823995169)
      ·
        refine ⟨29677932969791642117996377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39570577293055522823995169 29677932969791642117996377)
        ·
          refine ⟨22258449727343731588497283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29677932969791642117996377 22258449727343731588497283)
          ·
            refine ⟨33387674591015597382745925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22258449727343731588497283 33387674591015597382745925)
            ·
              refine ⟨6260188985815424509264861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33387674591015597382745925 6260188985815424509264861)
              ·
                refine ⟨2347570869680784190974323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6260188985815424509264861 2347570869680784190974323)
                ·
                  refine ⟨3521356304521176286461485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347570869680784190974323 3521356304521176286461485)
                  ·
                    refine ⟨1320508614195441107423057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521356304521176286461485 1320508614195441107423057)
                    ·
                      rfl

theorem cell22_3857522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_3857522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857522 prefixEnd_3857522 := by exact prefixLift 3857522
  have htrace : WordTrace (prefixWord ++ tailWord_3857522) baseStart_3857522 baseEnd_3857522 := by
    simpa [prefixWord, tailWord_3857522, baseEnd_3857522] using wordTrace_append hprefix tailTrace_3857522
  have hstable : (prefixWord ++ tailWord_3857522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857522).length < 2 ^ (prefixWord ++ tailWord_3857522).sum := by decide
  have hdescent : baseEnd_3857522 < baseStart_3857522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857565 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3857565 : Nat := 118140960795 + 3857565 * 2 ^ 59
def prefixEnd_3857565 : Nat := 4983230072969 + 3 ^ 40 * 3857565 * 2
def baseEnd_3857565 : Nat := 1320523333974203328597925

theorem tailTrace_3857565 : CollatzResearch.WordTrace tailWord_3857565 prefixEnd_3857565 1320523333974203328597925 := by
  unfold tailWord_3857565
  simp only [CollatzResearch.WordTrace]
  refine ⟨140696954269708299495798149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93797969513138866330532099 140696954269708299495798149)
  ·
    refine ⟨26380678925570306155462153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140696954269708299495798149 26380678925570306155462153)
    ·
      refine ⟨19785509194177729616596615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26380678925570306155462153 19785509194177729616596615)
      ·
        refine ⟨29678263791266594424894923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19785509194177729616596615 29678263791266594424894923)
        ·
          refine ⟨44517395686899891637342385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29678263791266594424894923 44517395686899891637342385)
          ·
            refine ⟨33388046765174918728006789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44517395686899891637342385 33388046765174918728006789)
            ·
              refine ⟨6260258768470297261501273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33388046765174918728006789 6260258768470297261501273)
              ·
                refine ⟨4695194076352722946125955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6260258768470297261501273 4695194076352722946125955)
                ·
                  refine ⟨7042791114529084419188933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695194076352722946125955 7042791114529084419188933)
                  ·
                    refine ⟨1320523333974203328597925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042791114529084419188933 1320523333974203328597925)
                    ·
                      rfl

theorem cell22_3857565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3857565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857565 prefixEnd_3857565 := by exact prefixLift 3857565
  have htrace : WordTrace (prefixWord ++ tailWord_3857565) baseStart_3857565 baseEnd_3857565 := by
    simpa [prefixWord, tailWord_3857565, baseEnd_3857565] using wordTrace_append hprefix tailTrace_3857565
  have hstable : (prefixWord ++ tailWord_3857565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857565).length < 2 ^ (prefixWord ++ tailWord_3857565).sum := by decide
  have hdescent : baseEnd_3857565 < baseStart_3857565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857593 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_3857593 : Nat := 118140960795 + 3857593 * 2 ^ 59
def prefixEnd_3857593 : Nat := 4983230072969 + 3 ^ 40 * 3857593 * 2
def baseEnd_3857593 : Nat := 1320532918946420588897839

theorem tailTrace_3857593 : CollatzResearch.WordTrace tailWord_3857593 prefixEnd_3857593 1320532918946420588897839 := by
  unfold tailWord_3857593
  simp only [CollatzResearch.WordTrace]
  refine ⟨140697975513606860277817433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93798650342404573518544955 140697975513606860277817433)
  ·
    refine ⟨105523481635205145208363075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140697975513606860277817433 105523481635205145208363075)
    ·
      refine ⟨158285222452807717812544613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105523481635205145208363075 158285222452807717812544613)
      ·
        refine ⟨29678479209901447089852115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158285222452807717812544613 29678479209901447089852115)
        ·
          refine ⟨44517718814852170634778173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29678479209901447089852115 44517718814852170634778173)
          ·
            refine ⟨16694144555569563988041815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44517718814852170634778173 16694144555569563988041815)
            ·
              refine ⟨25041216833354345982062723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16694144555569563988041815 25041216833354345982062723)
              ·
                refine ⟨37561825250031518973094085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25041216833354345982062723 37561825250031518973094085)
                ·
                  refine ⟨7042842234380909807455141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37561825250031518973094085 7042842234380909807455141)
                  ·
                    refine ⟨1320532918946420588897839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042842234380909807455141 1320532918946420588897839)
                    ·
                      rfl

theorem cell22_3857593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_3857593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857593 prefixEnd_3857593 := by exact prefixLift 3857593
  have htrace : WordTrace (prefixWord ++ tailWord_3857593) baseStart_3857593 baseEnd_3857593 := by
    simpa [prefixWord, tailWord_3857593, baseEnd_3857593] using wordTrace_append hprefix tailTrace_3857593
  have hstable : (prefixWord ++ tailWord_3857593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857593).length < 2 ^ (prefixWord ++ tailWord_3857593).sum := by decide
  have hdescent : baseEnd_3857593 < baseStart_3857593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857657 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 1, 3]
def baseStart_3857657 : Nat := 118140960795 + 3857657 * 2 ^ 59
def prefixEnd_3857657 : Nat := 4983230072969 + 3 ^ 40 * 3857657 * 2
def baseEnd_3857657 : Nat := 1320554827454345755297643

theorem tailTrace_3857657 : CollatzResearch.WordTrace tailWord_3857657 prefixEnd_3857657 1320554827454345755297643 := by
  unfold tailWord_3857657
  simp only [CollatzResearch.WordTrace]
  refine ⟨140700309785374999208147225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93800206523583332805431483 140700309785374999208147225)
  ·
    refine ⟨105525232339031249406110419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140700309785374999208147225 105525232339031249406110419)
    ·
      refine ⟨158287848508546874109165629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105525232339031249406110419 158287848508546874109165629)
      ·
        refine ⟨59357943190705077790937111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158287848508546874109165629 59357943190705077790937111)
        ·
          refine ⟨89036914786057616686405667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59357943190705077790937111 89036914786057616686405667)
          ·
            refine ⟨133555372179086425029608501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89036914786057616686405667 133555372179086425029608501)
            ·
              refine ⟨12520816141789352346525797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133555372179086425029608501 12520816141789352346525797)
              ·
                refine ⟨2347653026585503564973587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12520816141789352346525797 2347653026585503564973587)
                ·
                  refine ⟨3521479539878255347460381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347653026585503564973587 3521479539878255347460381)
                  ·
                    refine ⟨1320554827454345755297643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521479539878255347460381 1320554827454345755297643)
                    ·
                      rfl

theorem cell22_3857657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_3857657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857657 prefixEnd_3857657 := by exact prefixLift 3857657
  have htrace : WordTrace (prefixWord ++ tailWord_3857657) baseStart_3857657 baseEnd_3857657 := by
    simpa [prefixWord, tailWord_3857657, baseEnd_3857657] using wordTrace_append hprefix tailTrace_3857657
  have hstable : (prefixWord ++ tailWord_3857657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857657).length < 2 ^ (prefixWord ++ tailWord_3857657).sum := by decide
  have hdescent : baseEnd_3857657 < baseStart_3857657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857715 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 6]
def baseStart_3857715 : Nat := 118140960795 + 3857715 * 2 ^ 59
def prefixEnd_3857715 : Nat := 4983230072969 + 3 ^ 40 * 3857715 * 2
def baseEnd_3857715 : Nat := 440191560679884312449155

theorem tailTrace_3857715 : CollatzResearch.WordTrace tailWord_3857715 prefixEnd_3857715 440191560679884312449155 := by
  unfold tailWord_3857715
  simp only [CollatzResearch.WordTrace]
  refine ⟨140702425219164875113758599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93801616812776583409172399 140702425219164875113758599)
  ·
    refine ⟨211053637828747312670637899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140702425219164875113758599 211053637828747312670637899)
    ·
      refine ⟨316580456743120969005956849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211053637828747312670637899 316580456743120969005956849)
      ·
        refine ⟨237435342557340726754467637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316580456743120969005956849 237435342557340726754467637)
        ·
          refine ⟨22259563364750693133231341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237435342557340726754467637 22259563364750693133231341)
          ·
            refine ⟨8347336261781509924961753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22259563364750693133231341 8347336261781509924961753)
            ·
              refine ⟨6260502196336132443721315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8347336261781509924961753 6260502196336132443721315)
              ·
                refine ⟨9390753294504198665581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260502196336132443721315 9390753294504198665581973)
                ·
                  refine ⟨440191560679884312449155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9390753294504198665581973 440191560679884312449155)
                  ·
                    rfl

theorem cell22_3857715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 6].length) (baseStart_3857715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857715 prefixEnd_3857715 := by exact prefixLift 3857715
  have htrace : WordTrace (prefixWord ++ tailWord_3857715) baseStart_3857715 baseEnd_3857715 := by
    simpa [prefixWord, tailWord_3857715, baseEnd_3857715] using wordTrace_append hprefix tailTrace_3857715
  have hstable : (prefixWord ++ tailWord_3857715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857715).length < 2 ^ (prefixWord ++ tailWord_3857715).sum := by decide
  have hdescent : baseEnd_3857715 < baseStart_3857715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857728 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_3857728 : Nat := 118140960795 + 3857728 * 2 ^ 59
def prefixEnd_3857728 : Nat := 4983230072969 + 3 ^ 40 * 3857728 * 2
def baseEnd_3857728 : Nat := 1320579132205325236772425

theorem tailTrace_3857728 : CollatzResearch.WordTrace tailWord_3857728 prefixEnd_3857728 1320579132205325236772425 := by
  unfold tailWord_3857728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70351449684058889166990919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93801932912078518889321225 70351449684058889166990919)
  ·
    refine ⟨105527174526088333750486379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70351449684058889166990919 105527174526088333750486379)
    ·
      refine ⟨158290761789132500625729569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105527174526088333750486379 158290761789132500625729569)
      ·
        refine ⟨118718071341849375469297177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158290761789132500625729569 118718071341849375469297177)
        ·
          refine ⟨89038553506387031601972883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118718071341849375469297177 89038553506387031601972883)
          ·
            refine ⟨133557830259580547402959325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89038553506387031601972883 133557830259580547402959325)
            ·
              refine ⟨50084186347342705276109747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133557830259580547402959325 50084186347342705276109747)
              ·
                refine ⟨75126279521014057914164621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50084186347342705276109747 75126279521014057914164621)
                ·
                  refine ⟨28172354820380271717811733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75126279521014057914164621 28172354820380271717811733)
                  ·
                    refine ⟨1320579132205325236772425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28172354820380271717811733 1320579132205325236772425)
                    ·
                      rfl

theorem cell22_3857728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_3857728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857728 prefixEnd_3857728 := by exact prefixLift 3857728
  have htrace : WordTrace (prefixWord ++ tailWord_3857728) baseStart_3857728 baseEnd_3857728 := by
    simpa [prefixWord, tailWord_3857728, baseEnd_3857728] using wordTrace_append hprefix tailTrace_3857728
  have hstable : (prefixWord ++ tailWord_3857728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857728).length < 2 ^ (prefixWord ++ tailWord_3857728).sum := by decide
  have hdescent : baseEnd_3857728 < baseStart_3857728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857732 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_3857732 : Nat := 118140960795 + 3857732 * 2 ^ 59
def prefixEnd_3857732 : Nat := 4983230072969 + 3 ^ 40 * 3857732 * 2
def baseEnd_3857732 : Nat := 440193500495690186557471

theorem tailTrace_3857732 : CollatzResearch.WordTrace tailWord_3857732 prefixEnd_3857732 440193500495690186557471 := by
  unfold tailWord_3857732
  simp only [CollatzResearch.WordTrace]
  refine ⟨70351522630051643508563725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93802030173402191344751633 70351522630051643508563725)
  ·
    refine ⟨26381820986269366315711397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70351522630051643508563725 26381820986269366315711397)
    ·
      refine ⟨4946591434925506184195887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26381820986269366315711397 4946591434925506184195887)
      ·
        refine ⟨7419887152388259276293831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946591434925506184195887 7419887152388259276293831)
        ·
          refine ⟨11129830728582388914440747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419887152388259276293831 11129830728582388914440747)
          ·
            refine ⟨16694746092873583371661121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11129830728582388914440747 16694746092873583371661121)
            ·
              refine ⟨12521059569655187528745841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16694746092873583371661121 12521059569655187528745841)
              ·
                refine ⟨9390794677241390646559381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12521059569655187528745841 9390794677241390646559381)
                ·
                  refine ⟨440193500495690186557471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9390794677241390646559381 440193500495690186557471)
                  ·
                    rfl

theorem cell22_3857732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_3857732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857732 prefixEnd_3857732 := by exact prefixLift 3857732
  have htrace : WordTrace (prefixWord ++ tailWord_3857732) baseStart_3857732 baseEnd_3857732 := by
    simpa [prefixWord, tailWord_3857732, baseEnd_3857732] using wordTrace_append hprefix tailTrace_3857732
  have hstable : (prefixWord ++ tailWord_3857732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857732).length < 2 ^ (prefixWord ++ tailWord_3857732).sum := by decide
  have hdescent : baseEnd_3857732 < baseStart_3857732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857745 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3857745 : Nat := 118140960795 + 3857745 * 2 ^ 59
def prefixEnd_3857745 : Nat := 4983230072969 + 3 ^ 40 * 3857745 * 2
def baseEnd_3857745 : Nat := 1320584951652742859097373

theorem tailTrace_3857745 : CollatzResearch.WordTrace tailWord_3857745 prefixEnd_3857745 1320584951652742859097373 := by
  unfold tailWord_3857745
  simp only [CollatzResearch.WordTrace]
  refine ⟨140703519409056190237350689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93802346272704126824900459 140703519409056190237350689)
  ·
    refine ⟨105527639556792142678013017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140703519409056190237350689 105527639556792142678013017)
    ·
      refine ⟨79145729667594107008509763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105527639556792142678013017 79145729667594107008509763)
      ·
        refine ⟨118718594501391160512764645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79145729667594107008509763 118718594501391160512764645)
        ·
          refine ⟨22259736469010842596143371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118718594501391160512764645 22259736469010842596143371)
          ·
            refine ⟨33389604703516263894215057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22259736469010842596143371 33389604703516263894215057)
            ·
              refine ⟨25042203527637197920661293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33389604703516263894215057 25042203527637197920661293)
              ·
                refine ⟨9390826322863949220247985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25042203527637197920661293 9390826322863949220247985)
                ·
                  refine ⟨7043119742147961915185989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390826322863949220247985 7043119742147961915185989)
                  ·
                    refine ⟨1320584951652742859097373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7043119742147961915185989 1320584951652742859097373)
                    ·
                      rfl

theorem cell22_3857745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3857745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857745 prefixEnd_3857745 := by exact prefixLift 3857745
  have htrace : WordTrace (prefixWord ++ tailWord_3857745) baseStart_3857745 baseEnd_3857745 := by
    simpa [prefixWord, tailWord_3857745, baseEnd_3857745] using wordTrace_append hprefix tailTrace_3857745
  have hstable : (prefixWord ++ tailWord_3857745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857745).length < 2 ^ (prefixWord ++ tailWord_3857745).sum := by decide
  have hdescent : baseEnd_3857745 < baseStart_3857745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857749 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 4]
def baseStart_3857749 : Nat := 118140960795 + 3857749 * 2 ^ 59
def prefixEnd_3857749 : Nat := 4983230072969 + 3 ^ 40 * 3857749 * 2
def baseEnd_3857749 : Nat := 440195440311496060665787

theorem tailTrace_3857749 : CollatzResearch.WordTrace tailWord_3857749 prefixEnd_3857749 440195440311496060665787 := by
  unfold tailWord_3857749
  simp only [CollatzResearch.WordTrace]
  refine ⟨140703665301041698920496301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93802443534027799280330867 140703665301041698920496301)
  ·
    refine ⟨52763874487890637095186113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140703665301041698920496301 52763874487890637095186113)
    ·
      refine ⟨39572905865917977821389585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52763874487890637095186113 39572905865917977821389585)
      ·
        refine ⟨29679679399438483366042189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39572905865917977821389585 29679679399438483366042189)
        ·
          refine ⟨11129879774789431262265821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29679679399438483366042189 11129879774789431262265821)
          ·
            refine ⟨4173704915546036723349683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11129879774789431262265821 4173704915546036723349683)
            ·
              refine ⟨6260557373319055085024525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173704915546036723349683 6260557373319055085024525)
              ·
                refine ⟨2347709014994645656884197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6260557373319055085024525 2347709014994645656884197)
                ·
                  refine ⟨440195440311496060665787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347709014994645656884197 440195440311496060665787)
                  ·
                    rfl

theorem cell22_3857749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_3857749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857749 prefixEnd_3857749 := by exact prefixLift 3857749
  have htrace : WordTrace (prefixWord ++ tailWord_3857749) baseStart_3857749 baseEnd_3857749 := by
    simpa [prefixWord, tailWord_3857749, baseEnd_3857749] using wordTrace_append hprefix tailTrace_3857749
  have hstable : (prefixWord ++ tailWord_3857749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857749).length < 2 ^ (prefixWord ++ tailWord_3857749).sum := by decide
  have hdescent : baseEnd_3857749 < baseStart_3857749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857760 : List Nat := [2, 1, 1, 3, 4, 3, 8]
def baseStart_3857760 : Nat := 118140960795 + 3857760 * 2 ^ 59
def prefixEnd_3857760 : Nat := 4983230072969 + 3 ^ 40 * 3857760 * 2
def baseEnd_3857760 : Nat := 48910743942936585924901

theorem tailTrace_3857760 : CollatzResearch.WordTrace tailWord_3857760 prefixEnd_3857760 48910743942936585924901 := by
  unfold tailWord_3857760
  simp only [CollatzResearch.WordTrace]
  refine ⟨70352033252000923899573367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93802711002667898532764489 70352033252000923899573367)
  ·
    refine ⟨105528049878001385849360051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70352033252000923899573367 105528049878001385849360051)
    ·
      refine ⟨158292074817002078774040077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105528049878001385849360051 158292074817002078774040077)
      ·
        refine ⟨59359528056375779540265029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158292074817002078774040077 59359528056375779540265029)
        ·
          refine ⟨11129911510570458663799693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59359528056375779540265029 11129911510570458663799693)
          ·
            refine ⟨4173716816463921998924885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11129911510570458663799693 4173716816463921998924885)
            ·
              refine ⟨48910743942936585924901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4173716816463921998924885 48910743942936585924901)
              ·
                rfl

theorem cell22_3857760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 8].length) (baseStart_3857760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857760 prefixEnd_3857760 := by exact prefixLift 3857760
  have htrace : WordTrace (prefixWord ++ tailWord_3857760) baseStart_3857760 baseEnd_3857760 := by
    simpa [prefixWord, tailWord_3857760, baseEnd_3857760] using wordTrace_append hprefix tailTrace_3857760
  have hstable : (prefixWord ++ tailWord_3857760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857760).length < 2 ^ (prefixWord ++ tailWord_3857760).sum := by decide
  have hdescent : baseEnd_3857760 < baseStart_3857760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857762 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3857762 : Nat := 118140960795 + 3857762 * 2 ^ 59
def prefixEnd_3857762 : Nat := 4983230072969 + 3 ^ 40 * 3857762 * 2
def baseEnd_3857762 : Nat := 1320590771100160481422321

theorem tailTrace_3857762 : CollatzResearch.WordTrace tailWord_3857762 prefixEnd_3857762 1320590771100160481422321 := by
  unfold tailWord_3857762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35176034862498650535179885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93802759633329734760479693 35176034862498650535179885)
  ·
    refine ⟨13191013073436993950692457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35176034862498650535179885 13191013073436993950692457)
    ·
      refine ⟨9893259805077745463019343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13191013073436993950692457 9893259805077745463019343)
      ·
        refine ⟨14839889707616618194529015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9893259805077745463019343 14839889707616618194529015)
        ·
          refine ⟨22259834561424927291793523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14839889707616618194529015 22259834561424927291793523)
          ·
            refine ⟨33389751842137390937690285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22259834561424927291793523 33389751842137390937690285)
            ·
              refine ⟨12521156940801521601633857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33389751842137390937690285 12521156940801521601633857)
              ·
                refine ⟨9390867705601141201225393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12521156940801521601633857 9390867705601141201225393)
                ·
                  refine ⟨7043150779200855900919045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390867705601141201225393 7043150779200855900919045)
                  ·
                    refine ⟨1320590771100160481422321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7043150779200855900919045 1320590771100160481422321)
                    ·
                      rfl

theorem cell22_3857762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3857762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857762 prefixEnd_3857762 := by exact prefixLift 3857762
  have htrace : WordTrace (prefixWord ++ tailWord_3857762) baseStart_3857762 baseEnd_3857762 := by
    simpa [prefixWord, tailWord_3857762, baseEnd_3857762] using wordTrace_append hprefix tailTrace_3857762
  have hstable : (prefixWord ++ tailWord_3857762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857762).length < 2 ^ (prefixWord ++ tailWord_3857762).sum := by decide
  have hdescent : baseEnd_3857762 < baseStart_3857762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857826 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3857826 : Nat := 118140960795 + 3857826 * 2 ^ 59
def prefixEnd_3857826 : Nat := 4983230072969 + 3 ^ 40 * 3857826 * 2
def baseEnd_3857826 : Nat := 1320612679608085647822125

theorem tailTrace_3857826 : CollatzResearch.WordTrace tailWord_3857826 prefixEnd_3857826 1320612679608085647822125 := by
  unfold tailWord_3857826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35176618430440685267762333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93804315814508494047366221 35176618430440685267762333)
  ·
    refine ⟨13191231911415256975410875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35176618430440685267762333 13191231911415256975410875)
    ·
      refine ⟨19786847867122885463116313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191231911415256975410875 19786847867122885463116313)
      ·
        refine ⟨14840135900342164097337235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19786847867122885463116313 14840135900342164097337235)
        ·
          refine ⟨22260203850513246146005853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14840135900342164097337235 22260203850513246146005853)
          ·
            refine ⟨8347576443942467304752195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22260203850513246146005853 8347576443942467304752195)
            ·
              refine ⟨12521364665913700957128293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8347576443942467304752195 12521364665913700957128293)
              ·
                refine ⟨2347755874858818929461555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12521364665913700957128293 2347755874858818929461555)
                ·
                  refine ⟨3521633812288228394192333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347755874858818929461555 3521633812288228394192333)
                  ·
                    refine ⟨1320612679608085647822125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521633812288228394192333 1320612679608085647822125)
                    ·
                      rfl

theorem cell22_3857826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3857826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857826 prefixEnd_3857826 := by exact prefixLift 3857826
  have htrace : WordTrace (prefixWord ++ tailWord_3857826) baseStart_3857826 baseEnd_3857826 := by
    simpa [prefixWord, tailWord_3857826, baseEnd_3857826] using wordTrace_append hprefix tailTrace_3857826
  have hstable : (prefixWord ++ tailWord_3857826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857826).length < 2 ^ (prefixWord ++ tailWord_3857826).sum := by decide
  have hdescent : baseEnd_3857826 < baseStart_3857826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857837 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3857837 : Nat := 118140960795 + 3857837 * 2 ^ 59
def prefixEnd_3857837 : Nat := 4983230072969 + 3 ^ 40 * 3857837 * 2
def baseEnd_3857837 : Nat := 1320616445132885285797091

theorem tailTrace_3857837 : CollatzResearch.WordTrace tailWord_3857837 prefixEnd_3857837 1320616445132885285797091 := by
  unfold tailWord_3857837
  simp only [CollatzResearch.WordTrace]
  refine ⟨140706874924722889949699765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93804583283148593299799843 140706874924722889949699765)
  ·
    refine ⟨13191269524192770932784353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140706874924722889949699765 13191269524192770932784353)
    ·
      refine ⟨9893452143144578199588265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13191269524192770932784353 9893452143144578199588265)
      ·
        refine ⟨7420089107358433649691199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9893452143144578199588265 7420089107358433649691199)
        ·
          refine ⟨11130133661037650474536799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420089107358433649691199 11130133661037650474536799)
          ·
            refine ⟨16695200491556475711805199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130133661037650474536799 16695200491556475711805199)
            ·
              refine ⟨25042800737334713567707799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695200491556475711805199 25042800737334713567707799)
              ·
                refine ⟨37564201106002070351561699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25042800737334713567707799 37564201106002070351561699)
                ·
                  refine ⟨56346301659003105527342549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37564201106002070351561699 56346301659003105527342549)
                  ·
                    refine ⟨1320616445132885285797091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56346301659003105527342549 1320616445132885285797091)
                    ·
                      rfl

theorem cell22_3857837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3857837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857837 prefixEnd_3857837 := by exact prefixLift 3857837
  have htrace : WordTrace (prefixWord ++ tailWord_3857837) baseStart_3857837 baseEnd_3857837 := by
    simpa [prefixWord, tailWord_3857837, baseEnd_3857837] using wordTrace_append hprefix tailTrace_3857837
  have hstable : (prefixWord ++ tailWord_3857837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857837).length < 2 ^ (prefixWord ++ tailWord_3857837).sum := by decide
  have hdescent : baseEnd_3857837 < baseStart_3857837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857867 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 4]
def baseStart_3857867 : Nat := 118140960795 + 3857867 * 2 ^ 59
def prefixEnd_3857867 : Nat := 4983230072969 + 3 ^ 40 * 3857867 * 2
def baseEnd_3857867 : Nat := 440208904915325069182333

theorem tailTrace_3857867 : CollatzResearch.WordTrace tailWord_3857867 prefixEnd_3857867 440208904915325069182333 := by
  unfold tailWord_3857867
  simp only [CollatzResearch.WordTrace]
  refine ⟨140707969114614205073291855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93805312743076136715527903 140707969114614205073291855)
  ·
    refine ⟨211061953671921307609937783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140707969114614205073291855 211061953671921307609937783)
    ·
      refine ⟨316592930507881961414906675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211061953671921307609937783 316592930507881961414906675)
      ·
        refine ⟨474889395761822942122360013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316592930507881961414906675 474889395761822942122360013)
        ·
          refine ⟨178083523410683603295885005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474889395761822942122360013 178083523410683603295885005)
          ·
            refine ⟨66781321279006351235956877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178083523410683603295885005 66781321279006351235956877)
            ·
              refine ⟨25042995479627381713483829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66781321279006351235956877 25042995479627381713483829)
              ·
                refine ⟨2347780826215067035639109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25042995479627381713483829 2347780826215067035639109)
                ·
                  refine ⟨440208904915325069182333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347780826215067035639109 440208904915325069182333)
                  ·
                    rfl

theorem cell22_3857867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 4].length) (baseStart_3857867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857867 prefixEnd_3857867 := by exact prefixLift 3857867
  have htrace : WordTrace (prefixWord ++ tailWord_3857867) baseStart_3857867 baseEnd_3857867 := by
    simpa [prefixWord, tailWord_3857867, baseEnd_3857867] using wordTrace_append hprefix tailTrace_3857867
  have hstable : (prefixWord ++ tailWord_3857867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857867).length < 2 ^ (prefixWord ++ tailWord_3857867).sum := by decide
  have hdescent : baseEnd_3857867 < baseStart_3857867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857912 : List Nat := [2, 1, 2, 1, 1, 5, 4, 6]
def baseStart_3857912 : Nat := 118140960795 + 3857912 * 2 ^ 59
def prefixEnd_3857912 : Nat := 4983230072969 + 3 ^ 40 * 3857912 * 2
def baseEnd_3857912 : Nat := 146738013240623343352429

theorem tailTrace_3857912 : CollatzResearch.WordTrace tailWord_3857912 prefixEnd_3857912 146738013240623343352429 := by
  unfold tailWord_3857912
  simp only [CollatzResearch.WordTrace]
  refine ⟨70354805199725588879339995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93806406932967451839119993 70354805199725588879339995)
  ·
    refine ⟨105532207799588383319009993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70354805199725588879339995 105532207799588383319009993)
    ·
      refine ⟨79149155849691287489257495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105532207799588383319009993 79149155849691287489257495)
      ·
        refine ⟨118723733774536931233886243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79149155849691287489257495 118723733774536931233886243)
        ·
          refine ⟨178085600661805396850829365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118723733774536931233886243 178085600661805396850829365)
          ·
            refine ⟨16695525062044255954765253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178085600661805396850829365 16695525062044255954765253)
            ·
              refine ⟨3130410949133297991518485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16695525062044255954765253 3130410949133297991518485)
              ·
                refine ⟨146738013240623343352429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3130410949133297991518485 146738013240623343352429)
                ·
                  rfl

theorem cell22_3857912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_3857912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857912 prefixEnd_3857912 := by exact prefixLift 3857912
  have htrace : WordTrace (prefixWord ++ tailWord_3857912) baseStart_3857912 baseEnd_3857912 := by
    simpa [prefixWord, tailWord_3857912, baseEnd_3857912] using wordTrace_append hprefix tailTrace_3857912
  have hstable : (prefixWord ++ tailWord_3857912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857912).length < 2 ^ (prefixWord ++ tailWord_3857912).sum := by decide
  have hdescent : baseEnd_3857912 < baseStart_3857912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857925 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3857925 : Nat := 118140960795 + 3857925 * 2 ^ 59
def prefixEnd_3857925 : Nat := 4983230072969 + 3 ^ 40 * 3857925 * 2
def baseEnd_3857925 : Nat := 1320646569331282389596821

theorem tailTrace_3857925 : CollatzResearch.WordTrace tailWord_3857925 prefixEnd_3857925 1320646569331282389596821 := by
  unfold tailWord_3857925
  simp only [CollatzResearch.WordTrace]
  refine ⟨140710084548404080978903229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93806723032269387319268819 140710084548404080978903229)
  ·
    refine ⟨52766281705651530367088711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140710084548404080978903229 52766281705651530367088711)
    ·
      refine ⟨79149422558477295550633067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52766281705651530367088711 79149422558477295550633067)
      ·
        refine ⟨118724133837715943325949601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79149422558477295550633067 118724133837715943325949601)
        ·
          refine ⟨89043100378286957494462201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118724133837715943325949601 89043100378286957494462201)
          ·
            refine ⟨66782325283715218120846651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89043100378286957494462201 66782325283715218120846651)
            ·
              refine ⟨100173487925572827181269977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66782325283715218120846651 100173487925572827181269977)
              ·
                refine ⟨75130115944179620385952483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100173487925572827181269977 75130115944179620385952483)
                ·
                  refine ⟨112695173916269430578928725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75130115944179620385952483 112695173916269430578928725)
                  ·
                    refine ⟨1320646569331282389596821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112695173916269430578928725 1320646569331282389596821)
                    ·
                      rfl

theorem cell22_3857925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3857925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3857925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3857925 prefixEnd_3857925 := by exact prefixLift 3857925
  have htrace : WordTrace (prefixWord ++ tailWord_3857925) baseStart_3857925 baseEnd_3857925 := by
    simpa [prefixWord, tailWord_3857925, baseEnd_3857925] using wordTrace_append hprefix tailTrace_3857925
  have hstable : (prefixWord ++ tailWord_3857925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857925).length < 2 ^ (prefixWord ++ tailWord_3857925).sum := by decide
  have hdescent : baseEnd_3857925 < baseStart_3857925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858034 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3858034 : Nat := 118140960795 + 3858034 * 2 ^ 59
def prefixEnd_3858034 : Nat := 4983230072969 + 3 ^ 40 * 3858034 * 2
def baseEnd_3858034 : Nat := 1320683882258842438621487

theorem tailTrace_3858034 : CollatzResearch.WordTrace tailWord_3858034 prefixEnd_3858034 1320683882258842438621487 := by
  unfold tailWord_3858034
  simp only [CollatzResearch.WordTrace]
  refine ⟨35178515026252298148655289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93809373403339461729747437 35178515026252298148655289)
  ·
    refine ⟨26383886269689223611491467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35178515026252298148655289 26383886269689223611491467)
    ·
      refine ⟨39575829404533835417237201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26383886269689223611491467 39575829404533835417237201)
      ·
        refine ⟨29681872053400376562927901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39575829404533835417237201 29681872053400376562927901)
        ·
          refine ⟨11130702020025141211097963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29681872053400376562927901 11130702020025141211097963)
          ·
            refine ⟨16696053030037711816646945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130702020025141211097963 16696053030037711816646945)
            ·
              refine ⟨12522039772528283862485209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16696053030037711816646945 12522039772528283862485209)
              ·
                refine ⟨9391529829396212896863907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522039772528283862485209 9391529829396212896863907)
                ·
                  refine ⟨14087294744094319345295861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391529829396212896863907 14087294744094319345295861)
                  ·
                    refine ⟨1320683882258842438621487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14087294744094319345295861 1320683882258842438621487)
                    ·
                      rfl

theorem cell22_3858034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3858034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858034 prefixEnd_3858034 := by exact prefixLift 3858034
  have htrace : WordTrace (prefixWord ++ tailWord_3858034) baseStart_3858034 baseEnd_3858034 := by
    simpa [prefixWord, tailWord_3858034, baseEnd_3858034] using wordTrace_append hprefix tailTrace_3858034
  have hstable : (prefixWord ++ tailWord_3858034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858034).length < 2 ^ (prefixWord ++ tailWord_3858034).sum := by decide
  have hdescent : baseEnd_3858034 < baseStart_3858034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858038 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3858038 : Nat := 118140960795 + 3858038 * 2 ^ 59
def prefixEnd_3858038 : Nat := 4983230072969 + 3 ^ 40 * 3858038 * 2
def baseEnd_3858038 : Nat := 1320685251540587761521475

theorem tailTrace_3858038 : CollatzResearch.WordTrace tailWord_3858038 prefixEnd_3858038 1320685251540587761521475 := by
  unfold tailWord_3858038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794637874812168829860423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93809470664663134185177845 8794637874812168829860423)
  ·
    refine ⟨13191956812218253244790635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794637874812168829860423 13191956812218253244790635)
    ·
      refine ⟨19787935218327379867185953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191956812218253244790635 19787935218327379867185953)
      ·
        refine ⟨14840951413745534900389465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19787935218327379867185953 14840951413745534900389465)
        ·
          refine ⟨11130713560309151175292099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14840951413745534900389465 11130713560309151175292099)
          ·
            refine ⟨16696070340463726762938149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130713560309151175292099 16696070340463726762938149)
            ·
              refine ⟨3130513188836948768050903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16696070340463726762938149 3130513188836948768050903)
              ·
                refine ⟨4695769783255423152076355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130513188836948768050903 4695769783255423152076355)
                ·
                  refine ⟨7043654674883134728114533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695769783255423152076355 7043654674883134728114533)
                  ·
                    refine ⟨1320685251540587761521475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7043654674883134728114533 1320685251540587761521475)
                    ·
                      rfl

theorem cell22_3858038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3858038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858038 prefixEnd_3858038 := by exact prefixLift 3858038
  have htrace : WordTrace (prefixWord ++ tailWord_3858038) baseStart_3858038 baseEnd_3858038 := by
    simpa [prefixWord, tailWord_3858038, baseEnd_3858038] using wordTrace_append hprefix tailTrace_3858038
  have hstable : (prefixWord ++ tailWord_3858038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858038).length < 2 ^ (prefixWord ++ tailWord_3858038).sum := by decide
  have hdescent : baseEnd_3858038 < baseStart_3858038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858068 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3858068 : Nat := 118140960795 + 3858068 * 2 ^ 59
def prefixEnd_3858068 : Nat := 4983230072969 + 3 ^ 40 * 3858068 * 2
def baseEnd_3858068 : Nat := 1320695521153677683271383

theorem tailTrace_3858068 : CollatzResearch.WordTrace tailWord_3858068 prefixEnd_3858068 1320695521153677683271383 := by
  unfold tailWord_3858068
  simp only [CollatzResearch.WordTrace]
  refine ⟨70357650093443008200679429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93810200124590677600905905 70357650093443008200679429)
  ·
    refine ⟨13192059392520564037627393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70357650093443008200679429 13192059392520564037627393)
    ·
      refine ⟨9894044544390423028220545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13192059392520564037627393 9894044544390423028220545)
      ·
        refine ⟨7420533408292817271165409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9894044544390423028220545 7420533408292817271165409)
        ·
          refine ⟨5565400056219612953374057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7420533408292817271165409 5565400056219612953374057)
          ·
            refine ⟨4174050042164709715030543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5565400056219612953374057 4174050042164709715030543)
            ·
              refine ⟨6261075063247064572545815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174050042164709715030543 6261075063247064572545815)
              ·
                refine ⟨9391612594870596858818723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261075063247064572545815 9391612594870596858818723)
                ·
                  refine ⟨14087418892305895288228085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391612594870596858818723 14087418892305895288228085)
                  ·
                    refine ⟨1320695521153677683271383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14087418892305895288228085 1320695521153677683271383)
                    ·
                      rfl

theorem cell22_3858068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3858068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858068 prefixEnd_3858068 := by exact prefixLift 3858068
  have htrace : WordTrace (prefixWord ++ tailWord_3858068) baseStart_3858068 baseEnd_3858068 := by
    simpa [prefixWord, tailWord_3858068, baseEnd_3858068] using wordTrace_append hprefix tailTrace_3858068
  have hstable : (prefixWord ++ tailWord_3858068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858068).length < 2 ^ (prefixWord ++ tailWord_3858068).sum := by decide
  have hdescent : baseEnd_3858068 < baseStart_3858068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858081 : List Nat := [1, 2, 3, 3, 2, 3, 2, 6]
def baseStart_3858081 : Nat := 118140960795 + 3858081 * 2 ^ 59
def prefixEnd_3858081 : Nat := 4983230072969 + 3 ^ 40 * 3858081 * 2
def baseEnd_3858081 : Nat := 146744441257705553632927

theorem tailTrace_3858081 : CollatzResearch.WordTrace tailWord_3858081 prefixEnd_3858081 146744441257705553632927 := by
  unfold tailWord_3858081
  simp only [CollatzResearch.WordTrace]
  refine ⟨140715774335838919621582097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93810516223892613081054731 140715774335838919621582097)
  ·
    refine ⟨105536830751879189716186573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140715774335838919621582097 105536830751879189716186573)
    ·
      refine ⟨39576311531954696143569965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105536830751879189716186573 39576311531954696143569965)
      ·
        refine ⟨14841116824483011053838737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39576311531954696143569965 14841116824483011053838737)
        ·
          refine ⟨11130837618362258290379053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14841116824483011053838737 11130837618362258290379053)
          ·
            refine ⟨4174064106885846858892145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11130837618362258290379053 4174064106885846858892145)
            ·
              refine ⟨3130548080164385144169109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174064106885846858892145 3130548080164385144169109)
              ·
                refine ⟨146744441257705553632927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3130548080164385144169109 146744441257705553632927)
                ·
                  rfl

theorem cell22_3858081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 6].length) (baseStart_3858081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858081 prefixEnd_3858081 := by exact prefixLift 3858081
  have htrace : WordTrace (prefixWord ++ tailWord_3858081) baseStart_3858081 baseEnd_3858081 := by
    simpa [prefixWord, tailWord_3858081, baseEnd_3858081] using wordTrace_append hprefix tailTrace_3858081
  have hstable : (prefixWord ++ tailWord_3858081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858081).length < 2 ^ (prefixWord ++ tailWord_3858081).sum := by decide
  have hdescent : baseEnd_3858081 < baseStart_3858081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858107 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_3858107 : Nat := 118140960795 + 3858107 * 2 ^ 59
def prefixEnd_3858107 : Nat := 4983230072969 + 3 ^ 40 * 3858107 * 2
def baseEnd_3858107 : Nat := 1320708871650694581546263

theorem tailTrace_3858107 : CollatzResearch.WordTrace tailWord_3858107 prefixEnd_3858107 1320708871650694581546263 := by
  unfold tailWord_3858107
  simp only [CollatzResearch.WordTrace]
  refine ⟨140716722633744726062028575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93811148422496484041352383 140716722633744726062028575)
  ·
    refine ⟨211075083950617089093042863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140716722633744726062028575 211075083950617089093042863)
    ·
      refine ⟨316612625925925633639564295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211075083950617089093042863 316612625925925633639564295)
      ·
        refine ⟨474918938888888450459346443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316612625925925633639564295 474918938888888450459346443)
        ·
          refine ⟨712378408333332675689019665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474918938888888450459346443 712378408333332675689019665)
          ·
            refine ⟨534283806249999506766764749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712378408333332675689019665 534283806249999506766764749)
            ·
              refine ⟨200356427343749815037536781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534283806249999506766764749 200356427343749815037536781)
              ·
                refine ⟨75133660253906180639076293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200356427343749815037536781 75133660253906180639076293)
                ·
                  refine ⟨14087561297607408869826805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75133660253906180639076293 14087561297607408869826805)
                  ·
                    refine ⟨1320708871650694581546263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14087561297607408869826805 1320708871650694581546263)
                    ·
                      rfl

theorem cell22_3858107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_3858107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858107 prefixEnd_3858107 := by exact prefixLift 3858107
  have htrace : WordTrace (prefixWord ++ tailWord_3858107) baseStart_3858107 baseEnd_3858107 := by
    simpa [prefixWord, tailWord_3858107, baseEnd_3858107] using wordTrace_append hprefix tailTrace_3858107
  have hstable : (prefixWord ++ tailWord_3858107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858107).length < 2 ^ (prefixWord ++ tailWord_3858107).sum := by decide
  have hdescent : baseEnd_3858107 < baseStart_3858107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858109 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 5]
def baseStart_3858109 : Nat := 118140960795 + 3858109 * 2 ^ 59
def prefixEnd_3858109 : Nat := 4983230072969 + 3 ^ 40 * 3858109 * 2
def baseEnd_3858109 : Nat := 440236518763855747665419

theorem tailTrace_3858109 : CollatzResearch.WordTrace tailWord_3858109 prefixEnd_3858109 440236518763855747665419 := by
  unfold tailWord_3858109
  simp only [CollatzResearch.WordTrace]
  refine ⟨140716795579737480403601381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93811197053158320269067587 140716795579737480403601381)
  ·
    refine ⟨26384399171200777575675259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140716795579737480403601381 26384399171200777575675259)
    ·
      refine ⟨39576598756801166363512889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26384399171200777575675259 39576598756801166363512889)
      ·
        refine ⟨29682449067600874772634667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39576598756801166363512889 29682449067600874772634667)
        ·
          refine ⟨44523673601401312158952001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29682449067600874772634667 44523673601401312158952001)
          ·
            refine ⟨33392755201050984119214001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44523673601401312158952001 33392755201050984119214001)
            ·
              refine ⟨25044566400788238089410501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33392755201050984119214001 25044566400788238089410501)
              ·
                refine ⟨4695856200147794641764469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25044566400788238089410501 4695856200147794641764469)
                ·
                  refine ⟨440236518763855747665419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4695856200147794641764469 440236518763855747665419)
                  ·
                    rfl

theorem cell22_3858109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_3858109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858109 prefixEnd_3858109 := by exact prefixLift 3858109
  have htrace : WordTrace (prefixWord ++ tailWord_3858109) baseStart_3858109 baseEnd_3858109 := by
    simpa [prefixWord, tailWord_3858109, baseEnd_3858109] using wordTrace_append hprefix tailTrace_3858109
  have hstable : (prefixWord ++ tailWord_3858109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858109).length < 2 ^ (prefixWord ++ tailWord_3858109).sum := by decide
  have hdescent : baseEnd_3858109 < baseStart_3858109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858164 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3858164 : Nat := 118140960795 + 3858164 * 2 ^ 59
def prefixEnd_3858164 : Nat := 4983230072969 + 3 ^ 40 * 3858164 * 2
def baseEnd_3858164 : Nat := 1320728383915565432871089

theorem tailTrace_3858164 : CollatzResearch.WordTrace tailWord_3858164 prefixEnd_3858164 1320728383915565432871089 := by
  unfold tailWord_3858164
  simp only [CollatzResearch.WordTrace]
  refine ⟨70359400797269112398426773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93812534396358816531235697 70359400797269112398426773)
  ·
    refine ⟨3298096912371989643676255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70359400797269112398426773 3298096912371989643676255)
    ·
      refine ⟨4947145368557984465514383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298096912371989643676255 4947145368557984465514383)
      ·
        refine ⟨7420718052836976698271575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947145368557984465514383 7420718052836976698271575)
        ·
          refine ⟨11131077079255465047407363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420718052836976698271575 11131077079255465047407363)
          ·
            refine ⟨16696615618883197571111045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131077079255465047407363 16696615618883197571111045)
            ·
              refine ⟨3130615428540599544583321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16696615618883197571111045 3130615428540599544583321)
              ·
                refine ⟨2347961571405449658437491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130615428540599544583321 2347961571405449658437491)
                ·
                  refine ⟨3521942357108174487656237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347961571405449658437491 3521942357108174487656237)
                  ·
                    refine ⟨1320728383915565432871089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521942357108174487656237 1320728383915565432871089)
                    ·
                      rfl

theorem cell22_3858164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3858164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858164 prefixEnd_3858164 := by exact prefixLift 3858164
  have htrace : WordTrace (prefixWord ++ tailWord_3858164) baseStart_3858164 baseEnd_3858164 := by
    simpa [prefixWord, tailWord_3858164, baseEnd_3858164] using wordTrace_append hprefix tailTrace_3858164
  have hstable : (prefixWord ++ tailWord_3858164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858164).length < 2 ^ (prefixWord ++ tailWord_3858164).sum := by decide
  have hdescent : baseEnd_3858164 < baseStart_3858164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858184 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_3858184 : Nat := 118140960795 + 3858184 * 2 ^ 59
def prefixEnd_3858184 : Nat := 4983230072969 + 3 ^ 40 * 3858184 * 2
def baseEnd_3858184 : Nat := 1320735230324292047371027

theorem tailTrace_3858184 : CollatzResearch.WordTrace tailWord_3858184 prefixEnd_3858184 1320735230324292047371027 := by
  unfold tailWord_3858184
  simp only [CollatzResearch.WordTrace]
  refine ⟨70359765527232884106290803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93813020702977178808387737 70359765527232884106290803)
  ·
    refine ⟨105539648290849326159436205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70359765527232884106290803 105539648290849326159436205)
    ·
      refine ⟨39577368109068497309788577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105539648290849326159436205 39577368109068497309788577)
      ·
        refine ⟨29683026081801372982341433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39577368109068497309788577 29683026081801372982341433)
        ·
          refine ⟨22262269561351029736756075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29683026081801372982341433 22262269561351029736756075)
          ·
            refine ⟨33393404342026544605134113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22262269561351029736756075 33393404342026544605134113)
            ·
              refine ⟨25045053256519908453850585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33393404342026544605134113 25045053256519908453850585)
              ·
                refine ⟨18783789942389931340387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25045053256519908453850585 18783789942389931340387939)
                ·
                  refine ⟨28175684913584897010581909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18783789942389931340387939 28175684913584897010581909)
                  ·
                    refine ⟨1320735230324292047371027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28175684913584897010581909 1320735230324292047371027)
                    ·
                      rfl

theorem cell22_3858184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_3858184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858184 prefixEnd_3858184 := by exact prefixLift 3858184
  have htrace : WordTrace (prefixWord ++ tailWord_3858184) baseStart_3858184 baseEnd_3858184 := by
    simpa [prefixWord, tailWord_3858184, baseEnd_3858184] using wordTrace_append hprefix tailTrace_3858184
  have hstable : (prefixWord ++ tailWord_3858184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858184).length < 2 ^ (prefixWord ++ tailWord_3858184).sum := by decide
  have hdescent : baseEnd_3858184 < baseStart_3858184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858186 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3858186 : Nat := 118140960795 + 3858186 * 2 ^ 59
def prefixEnd_3858186 : Nat := 4983230072969 + 3 ^ 40 * 3858186 * 2
def baseEnd_3858186 : Nat := 1320735914965164708821021

theorem tailTrace_3858186 : CollatzResearch.WordTrace tailWord_3858186 prefixEnd_3858186 1320735914965164708821021 := by
  unfold tailWord_3858186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35179901000114630638538603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93813069333639015036102941 35179901000114630638538603)
  ·
    refine ⟨52769851500171945957807905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35179901000114630638538603 52769851500171945957807905)
    ·
      refine ⟨39577388625128959468355929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52769851500171945957807905 39577388625128959468355929)
      ·
        refine ⟨29683041468846719601266947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39577388625128959468355929 29683041468846719601266947)
        ·
          refine ⟨44524562203270079401900421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29683041468846719601266947 44524562203270079401900421)
          ·
            refine ⟨8348355413113139887856329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44524562203270079401900421 8348355413113139887856329)
            ·
              refine ⟨6261266559834854915892247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8348355413113139887856329 6261266559834854915892247)
              ·
                refine ⟨9391899839752282373838371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261266559834854915892247 9391899839752282373838371)
                ·
                  refine ⟨14087849759628423560757557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391899839752282373838371 14087849759628423560757557)
                  ·
                    refine ⟨1320735914965164708821021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14087849759628423560757557 1320735914965164708821021)
                    ·
                      rfl

theorem cell22_3858186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3858186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858186 prefixEnd_3858186 := by exact prefixLift 3858186
  have htrace : WordTrace (prefixWord ++ tailWord_3858186) baseStart_3858186 baseEnd_3858186 := by
    simpa [prefixWord, tailWord_3858186, baseEnd_3858186] using wordTrace_append hprefix tailTrace_3858186
  have hstable : (prefixWord ++ tailWord_3858186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858186).length < 2 ^ (prefixWord ++ tailWord_3858186).sum := by decide
  have hdescent : baseEnd_3858186 < baseStart_3858186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858282 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_3858282 : Nat := 118140960795 + 3858282 * 2 ^ 59
def prefixEnd_3858282 : Nat := 4983230072969 + 3 ^ 40 * 3858282 * 2
def baseEnd_3858282 : Nat := 1320768777727052458420727

theorem tailTrace_3858282 : CollatzResearch.WordTrace tailWord_3858282 prefixEnd_3858282 1320768777727052458420727 := by
  unfold tailWord_3858282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35180776352027682737412275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93815403605407153966432733 35180776352027682737412275)
  ·
    refine ⟨52771164528041524106118413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35180776352027682737412275 52771164528041524106118413)
    ·
      refine ⟨19789186698015571539794405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52771164528041524106118413 19789186698015571539794405)
      ·
        refine ⟨3710472505877919663711451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19789186698015571539794405 3710472505877919663711451)
        ·
          refine ⟨5565708758816879495567177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710472505877919663711451 5565708758816879495567177)
          ·
            refine ⟨4174281569112659621675383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5565708758816879495567177 4174281569112659621675383)
            ·
              refine ⟨6261422353668989432513075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174281569112659621675383 6261422353668989432513075)
              ·
                refine ⟨9392133530503484148769613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261422353668989432513075 9392133530503484148769613)
                ·
                  refine ⟨3522050073938806555788605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9392133530503484148769613 3522050073938806555788605)
                  ·
                    refine ⟨1320768777727052458420727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522050073938806555788605 1320768777727052458420727)
                    ·
                      rfl

theorem cell22_3858282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_3858282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858282 prefixEnd_3858282 := by exact prefixLift 3858282
  have htrace : WordTrace (prefixWord ++ tailWord_3858282) baseStart_3858282 baseEnd_3858282 := by
    simpa [prefixWord, tailWord_3858282, baseEnd_3858282] using wordTrace_append hprefix tailTrace_3858282
  have hstable : (prefixWord ++ tailWord_3858282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858282).length < 2 ^ (prefixWord ++ tailWord_3858282).sum := by decide
  have hdescent : baseEnd_3858282 < baseStart_3858282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858308 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3858308 : Nat := 118140960795 + 3858308 * 2 ^ 59
def prefixEnd_3858308 : Nat := 4983230072969 + 3 ^ 40 * 3858308 * 2
def baseEnd_3858308 : Nat := 1320777678058397057270647

theorem tailTrace_3858308 : CollatzResearch.WordTrace tailWord_3858308 prefixEnd_3858308 1320777678058397057270647 := by
  unfold tailWord_3858308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70362026853008268695047789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93816035804011024926730385 70362026853008268695047789)
  ·
    refine ⟨26385760069878100760642921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70362026853008268695047789 26385760069878100760642921)
    ·
      refine ⟨19789320052408575570482191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26385760069878100760642921 19789320052408575570482191)
      ·
        refine ⟨29683980078612863355723287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19789320052408575570482191 29683980078612863355723287)
        ·
          refine ⟨44525970117919295033584931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29683980078612863355723287 44525970117919295033584931)
          ·
            refine ⟨66788955176878942550377397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44525970117919295033584931 66788955176878942550377397)
            ·
              refine ⟨6261464547832400864097881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66788955176878942550377397 6261464547832400864097881)
              ·
                refine ⟨4696098410874300648073411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261464547832400864097881 4696098410874300648073411)
                ·
                  refine ⟨7044147616311450972110117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696098410874300648073411 7044147616311450972110117)
                  ·
                    refine ⟨1320777678058397057270647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7044147616311450972110117 1320777678058397057270647)
                    ·
                      rfl

theorem cell22_3858308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3858308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858308 prefixEnd_3858308 := by exact prefixLift 3858308
  have htrace : WordTrace (prefixWord ++ tailWord_3858308) baseStart_3858308 baseEnd_3858308 := by
    simpa [prefixWord, tailWord_3858308, baseEnd_3858308] using wordTrace_append hprefix tailTrace_3858308
  have hstable : (prefixWord ++ tailWord_3858308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858308).length < 2 ^ (prefixWord ++ tailWord_3858308).sum := by decide
  have hdescent : baseEnd_3858308 < baseStart_3858308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858319 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_3858319 : Nat := 118140960795 + 3858319 * 2 ^ 59
def prefixEnd_3858319 : Nat := 4983230072969 + 3 ^ 40 * 3858319 * 2
def baseEnd_3858319 : Nat := 1320781443583196695245613

theorem tailTrace_3858319 : CollatzResearch.WordTrace tailWord_3858319 prefixEnd_3858319 1320781443583196695245613 := by
  unfold tailWord_3858319
  simp only [CollatzResearch.WordTrace]
  refine ⟨140724454908976686268746011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93816303272651124179164007 140724454908976686268746011)
  ·
    refine ⟨211086682363465029403119017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140724454908976686268746011 211086682363465029403119017)
    ·
      refine ⟨158315011772598772052339263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211086682363465029403119017 158315011772598772052339263)
      ·
        refine ⟨237472517658898158078508895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158315011772598772052339263 237472517658898158078508895)
        ·
          refine ⟨356208776488347237117763343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237472517658898158078508895 356208776488347237117763343)
          ·
            refine ⟨534313164732520855676645015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356208776488347237117763343 534313164732520855676645015)
            ·
              refine ⟨801469747098781283514967523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534313164732520855676645015 801469747098781283514967523)
              ·
                refine ⟨1202204620648171925272451285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801469747098781283514967523 1202204620648171925272451285)
                ·
                  refine ⟨28176670796441529498573077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1202204620648171925272451285 28176670796441529498573077)
                  ·
                    refine ⟨1320781443583196695245613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28176670796441529498573077 1320781443583196695245613)
                    ·
                      rfl

theorem cell22_3858319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_3858319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858319 prefixEnd_3858319 := by exact prefixLift 3858319
  have htrace : WordTrace (prefixWord ++ tailWord_3858319) baseStart_3858319 baseEnd_3858319 := by
    simpa [prefixWord, tailWord_3858319, baseEnd_3858319] using wordTrace_append hprefix tailTrace_3858319
  have hstable : (prefixWord ++ tailWord_3858319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858319).length < 2 ^ (prefixWord ++ tailWord_3858319).sum := by decide
  have hdescent : baseEnd_3858319 < baseStart_3858319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858321 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_3858321 : Nat := 118140960795 + 3858321 * 2 ^ 59
def prefixEnd_3858321 : Nat := 4983230072969 + 3 ^ 40 * 3858321 * 2
def baseEnd_3858321 : Nat := 1320782128224069356695607

theorem tailTrace_3858321 : CollatzResearch.WordTrace tailWord_3858321 prefixEnd_3858321 1320782128224069356695607 := by
  unfold tailWord_3858321
  simp only [CollatzResearch.WordTrace]
  refine ⟨140724527854969440610318817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93816351903312960406879211 140724527854969440610318817)
  ·
    refine ⟨105543395891227080457739113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140724527854969440610318817 105543395891227080457739113)
    ·
      refine ⟨79157546918420310343304335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105543395891227080457739113 79157546918420310343304335)
      ·
        refine ⟨118736320377630465514956503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79157546918420310343304335 118736320377630465514956503)
        ·
          refine ⟨178104480566445698272434755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118736320377630465514956503 178104480566445698272434755)
          ·
            refine ⟨267156720849668547408652133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178104480566445698272434755 267156720849668547408652133)
            ·
              refine ⟨50091885159312852639122275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267156720849668547408652133 50091885159312852639122275)
              ·
                refine ⟨75137827738969278958683413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50091885159312852639122275 75137827738969278958683413)
                ·
                  refine ⟨3522085675264184951188285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75137827738969278958683413 3522085675264184951188285)
                  ·
                    refine ⟨1320782128224069356695607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522085675264184951188285 1320782128224069356695607)
                    ·
                      rfl

theorem cell22_3858321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_3858321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858321 prefixEnd_3858321 := by exact prefixLift 3858321
  have htrace : WordTrace (prefixWord ++ tailWord_3858321) baseStart_3858321 baseEnd_3858321 := by
    simpa [prefixWord, tailWord_3858321, baseEnd_3858321] using wordTrace_append hprefix tailTrace_3858321
  have hstable : (prefixWord ++ tailWord_3858321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858321).length < 2 ^ (prefixWord ++ tailWord_3858321).sum := by decide
  have hdescent : baseEnd_3858321 < baseStart_3858321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858340 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 4]
def baseStart_3858340 : Nat := 118140960795 + 3858340 * 2 ^ 59
def prefixEnd_3858340 : Nat := 4983230072969 + 3 ^ 40 * 3858340 * 2
def baseEnd_3858340 : Nat := 440262877437453213490183

theorem tailTrace_3858340 : CollatzResearch.WordTrace tailWord_3858340 prefixEnd_3858340 440262877437453213490183 := by
  unfold tailWord_3858340
  simp only [CollatzResearch.WordTrace]
  refine ⟨70362610420950303427630237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93816813894600404570173649 70362610420950303427630237)
  ·
    refine ⟨26385978907856363785361339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70362610420950303427630237 26385978907856363785361339)
    ·
      refine ⟨39578968361784545678042009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26385978907856363785361339 39578968361784545678042009)
      ·
        refine ⟨29684226271338409258531507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39578968361784545678042009 29684226271338409258531507)
        ·
          refine ⟨44526339407007613887797261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29684226271338409258531507 44526339407007613887797261)
          ·
            refine ⟨16697377277627855207923973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44526339407007613887797261 16697377277627855207923973)
            ·
              refine ⟨3130758239555222851485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16697377277627855207923973 3130758239555222851485745)
              ·
                refine ⟨2348068679666417138614309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130758239555222851485745 2348068679666417138614309)
                ·
                  refine ⟨440262877437453213490183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348068679666417138614309 440262877437453213490183)
                  ·
                    rfl

theorem cell22_3858340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_3858340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858340 prefixEnd_3858340 := by exact prefixLift 3858340
  have htrace : WordTrace (prefixWord ++ tailWord_3858340) baseStart_3858340 baseEnd_3858340 := by
    simpa [prefixWord, tailWord_3858340, baseEnd_3858340] using wordTrace_append hprefix tailTrace_3858340
  have hstable : (prefixWord ++ tailWord_3858340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858340).length < 2 ^ (prefixWord ++ tailWord_3858340).sum := by decide
  have hdescent : baseEnd_3858340 < baseStart_3858340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858443 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 1, 4]
def baseStart_3858443 : Nat := 118140960795 + 3858443 * 2 ^ 59
def prefixEnd_3858443 : Nat := 4983230072969 + 3 ^ 40 * 3858443 * 2
def baseEnd_3858443 : Nat := 1320823891317301705145233

theorem tailTrace_3858443 : CollatzResearch.WordTrace tailWord_3858443 prefixEnd_3858443 1320823891317301705145233 := by
  unfold tailWord_3858443
  simp only [CollatzResearch.WordTrace]
  refine ⟨140728977560527455446259983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93819318373684970297506655 140728977560527455446259983)
  ·
    refine ⟨211093466340791183169389975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140728977560527455446259983 211093466340791183169389975)
    ·
      refine ⟨316640199511186774754084963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211093466340791183169389975 316640199511186774754084963)
      ·
        refine ⟨474960299266780162131127445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316640199511186774754084963 474960299266780162131127445)
        ·
          refine ⟨22263764028130320099896599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 474960299266780162131127445 22263764028130320099896599)
          ·
            refine ⟨33395646042195480149844899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22263764028130320099896599 33395646042195480149844899)
            ·
              refine ⟨50093469063293220224767349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33395646042195480149844899 50093469063293220224767349)
              ·
                refine ⟨4696262724683739396071939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50093469063293220224767349 4696262724683739396071939)
                ·
                  refine ⟨7044394087025609094107909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696262724683739396071939 7044394087025609094107909)
                  ·
                    refine ⟨1320823891317301705145233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7044394087025609094107909 1320823891317301705145233)
                    ·
                      rfl

theorem cell22_3858443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 4].length) (baseStart_3858443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858443 prefixEnd_3858443 := by exact prefixLift 3858443
  have htrace : WordTrace (prefixWord ++ tailWord_3858443) baseStart_3858443 baseEnd_3858443 := by
    simpa [prefixWord, tailWord_3858443, baseEnd_3858443] using wordTrace_append hprefix tailTrace_3858443
  have hstable : (prefixWord ++ tailWord_3858443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858443).length < 2 ^ (prefixWord ++ tailWord_3858443).sum := by decide
  have hdescent : baseEnd_3858443 < baseStart_3858443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858458 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_3858458 : Nat := 118140960795 + 3858458 * 2 ^ 59
def prefixEnd_3858458 : Nat := 4983230072969 + 3 ^ 40 * 3858458 * 2
def baseEnd_3858458 : Nat := 440276342041282222006729

theorem tailTrace_3858458 : CollatzResearch.WordTrace tailWord_3858458 prefixEnd_3858458 440276342041282222006729 := by
  unfold tailWord_3858458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35182381163868278252014007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93819683103648742005370685 35182381163868278252014007)
  ·
    refine ⟨52773571745802417378021011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35182381163868278252014007 52773571745802417378021011)
    ·
      refine ⟨79160357618703626067031517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52773571745802417378021011 79160357618703626067031517)
      ·
        refine ⟨29685134107013859775136819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79160357618703626067031517 29685134107013859775136819)
        ·
          refine ⟨44527701160520789662705229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29685134107013859775136819 44527701160520789662705229)
          ·
            refine ⟨16697887935195296123514461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44527701160520789662705229 16697887935195296123514461)
            ·
              refine ⟨6261707975698236046317923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16697887935195296123514461 6261707975698236046317923)
              ·
                refine ⟨9392561963547354069476885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261707975698236046317923 9392561963547354069476885)
                ·
                  refine ⟨440276342041282222006729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9392561963547354069476885 440276342041282222006729)
                  ·
                    rfl

theorem cell22_3858458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_3858458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858458 prefixEnd_3858458 := by exact prefixLift 3858458
  have htrace : WordTrace (prefixWord ++ tailWord_3858458) baseStart_3858458 baseEnd_3858458 := by
    simpa [prefixWord, tailWord_3858458, baseEnd_3858458] using wordTrace_append hprefix tailTrace_3858458
  have hstable : (prefixWord ++ tailWord_3858458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858458).length < 2 ^ (prefixWord ++ tailWord_3858458).sum := by decide
  have hdescent : baseEnd_3858458 < baseStart_3858458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858494 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3858494 : Nat := 118140960795 + 3858494 * 2 ^ 59
def prefixEnd_3858494 : Nat := 4983230072969 + 3 ^ 40 * 3858494 * 2
def baseEnd_3858494 : Nat := 1320841349659554572120077

theorem tailTrace_3858494 : CollatzResearch.WordTrace tailWord_3858494 prefixEnd_3858494 1320841349659554572120077 := by
  unfold tailWord_3858494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17591354710417836394545817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93820558455561794104244357 17591354710417836394545817)
  ·
    refine ⟨13193516032813377295909363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17591354710417836394545817 13193516032813377295909363)
    ·
      refine ⟨19790274049220065943864045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13193516032813377295909363 19790274049220065943864045)
      ·
        refine ⟨7421352768457524728949017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19790274049220065943864045 7421352768457524728949017)
        ·
          refine ⟨5566014576343143546711763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7421352768457524728949017 5566014576343143546711763)
          ·
            refine ⟨8349021864514715320067645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566014576343143546711763 8349021864514715320067645)
            ·
              refine ⟨3130883199193018245025367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8349021864514715320067645 3130883199193018245025367)
              ·
                refine ⟨4696324798789527367538051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130883199193018245025367 4696324798789527367538051)
                ·
                  refine ⟨7044487198184291051307077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696324798789527367538051 7044487198184291051307077)
                  ·
                    refine ⟨1320841349659554572120077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7044487198184291051307077 1320841349659554572120077)
                    ·
                      rfl

theorem cell22_3858494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3858494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858494 prefixEnd_3858494 := by exact prefixLift 3858494
  have htrace : WordTrace (prefixWord ++ tailWord_3858494) baseStart_3858494 baseEnd_3858494 := by
    simpa [prefixWord, tailWord_3858494, baseEnd_3858494] using wordTrace_append hprefix tailTrace_3858494
  have hstable : (prefixWord ++ tailWord_3858494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858494).length < 2 ^ (prefixWord ++ tailWord_3858494).sum := by decide
  have hdescent : baseEnd_3858494 < baseStart_3858494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858535 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3858535 : Nat := 118140960795 + 3858535 * 2 ^ 59
def prefixEnd_3858535 : Nat := 4983230072969 + 3 ^ 40 * 3858535 * 2
def baseEnd_3858535 : Nat := 1320855384797444131844951

theorem tailTrace_3858535 : CollatzResearch.WordTrace tailWord_3858535 prefixEnd_3858535 1320855384797444131844951 := by
  unfold tailWord_3858535
  simp only [CollatzResearch.WordTrace]
  refine ⟨140732333076194155158609059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93821555384129436772406039 140732333076194155158609059)
  ·
    refine ⟨211098499614291232737913589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140732333076194155158609059 211098499614291232737913589)
    ·
      refine ⟨19790484338839803069179399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211098499614291232737913589 19790484338839803069179399)
      ·
        refine ⟨29685726508259704603769099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19790484338839803069179399 29685726508259704603769099)
        ·
          refine ⟨44528589762389556905653649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29685726508259704603769099 44528589762389556905653649)
          ·
            refine ⟨33396442321792167679240237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44528589762389556905653649 33396442321792167679240237)
            ·
              refine ⟨12523665870672062879715089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33396442321792167679240237 12523665870672062879715089)
              ·
                refine ⟨9392749403004047159786317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12523665870672062879715089 9392749403004047159786317)
                ·
                  refine ⟨3522281026126517684919869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9392749403004047159786317 3522281026126517684919869)
                  ·
                    refine ⟨1320855384797444131844951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522281026126517684919869 1320855384797444131844951)
                    ·
                      rfl

theorem cell22_3858535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3858535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858535 prefixEnd_3858535 := by exact prefixLift 3858535
  have htrace : WordTrace (prefixWord ++ tailWord_3858535) baseStart_3858535 baseEnd_3858535 := by
    simpa [prefixWord, tailWord_3858535, baseEnd_3858535] using wordTrace_append hprefix tailTrace_3858535
  have hstable : (prefixWord ++ tailWord_3858535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858535).length < 2 ^ (prefixWord ++ tailWord_3858535).sum := by decide
  have hdescent : baseEnd_3858535 < baseStart_3858535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858563 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_3858563 : Nat := 118140960795 + 3858563 * 2 ^ 59
def prefixEnd_3858563 : Nat := 4983230072969 + 3 ^ 40 * 3858563 * 2
def baseEnd_3858563 : Nat := 1320864969769661392144865

theorem tailTrace_3858563 : CollatzResearch.WordTrace tailWord_3858563 prefixEnd_3858563 1320864969769661392144865 := by
  unfold tailWord_3858563
  simp only [CollatzResearch.WordTrace]
  refine ⟨140733354320092715940628343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93822236213395143960418895 140733354320092715940628343)
  ·
    refine ⟨211100031480139073910942515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140733354320092715940628343 211100031480139073910942515)
    ·
      refine ⟨316650047220208610866413773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211100031480139073910942515 316650047220208610866413773)
      ·
        refine ⟨118743767707578229074905165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316650047220208610866413773 118743767707578229074905165)
        ·
          refine ⟨44528912890341835903089437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118743767707578229074905165 44528912890341835903089437)
          ·
            refine ⟨16698342333878188463658539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44528912890341835903089437 16698342333878188463658539)
            ·
              refine ⟨25047513500817282695487809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16698342333878188463658539 25047513500817282695487809)
              ·
                refine ⟨18785635125612962021615857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25047513500817282695487809 18785635125612962021615857)
                ·
                  refine ⟨14089226344209721516211893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18785635125612962021615857 14089226344209721516211893)
                  ·
                    refine ⟨1320864969769661392144865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14089226344209721516211893 1320864969769661392144865)
                    ·
                      rfl

theorem cell22_3858563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_3858563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858563 prefixEnd_3858563 := by exact prefixLift 3858563
  have htrace : WordTrace (prefixWord ++ tailWord_3858563) baseStart_3858563 baseEnd_3858563 := by
    simpa [prefixWord, tailWord_3858563, baseEnd_3858563] using wordTrace_append hprefix tailTrace_3858563
  have hstable : (prefixWord ++ tailWord_3858563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858563).length < 2 ^ (prefixWord ++ tailWord_3858563).sum := by decide
  have hdescent : baseEnd_3858563 < baseStart_3858563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858565 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 5]
def baseStart_3858565 : Nat := 118140960795 + 3858565 * 2 ^ 59
def prefixEnd_3858565 : Nat := 4983230072969 + 3 ^ 40 * 3858565 * 2
def baseEnd_3858565 : Nat := 440288551470178017864953

theorem tailTrace_3858565 : CollatzResearch.WordTrace tailWord_3858565 prefixEnd_3858565 440288551470178017864953 := by
  unfold tailWord_3858565
  simp only [CollatzResearch.WordTrace]
  refine ⟨140733427266085470282201149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93822284844056980188134099 140733427266085470282201149)
  ·
    refine ⟨52775035224782051355825431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140733427266085470282201149 52775035224782051355825431)
    ·
      refine ⟨79162552837173077033738147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52775035224782051355825431 79162552837173077033738147)
      ·
        refine ⟨118743829255759615550607221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79162552837173077033738147 118743829255759615550607221)
        ·
          refine ⟨11132233992727463957869427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118743829255759615550607221 11132233992727463957869427)
          ·
            refine ⟨16698350989091195936804141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132233992727463957869427 16698350989091195936804141)
            ·
              refine ⟨6261881620909198476301553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16698350989091195936804141 6261881620909198476301553)
              ·
                refine ⟨4696411215681898857226165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261881620909198476301553 4696411215681898857226165)
                ·
                  refine ⟨440288551470178017864953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696411215681898857226165 440288551470178017864953)
                  ·
                    rfl

theorem cell22_3858565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_3858565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858565 prefixEnd_3858565 := by exact prefixLift 3858565
  have htrace : WordTrace (prefixWord ++ tailWord_3858565) baseStart_3858565 baseEnd_3858565 := by
    simpa [prefixWord, tailWord_3858565, baseEnd_3858565] using wordTrace_append hprefix tailTrace_3858565
  have hstable : (prefixWord ++ tailWord_3858565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858565).length < 2 ^ (prefixWord ++ tailWord_3858565).sum := by decide
  have hdescent : baseEnd_3858565 < baseStart_3858565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858646 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3858646 : Nat := 118140960795 + 3858646 * 2 ^ 59
def prefixEnd_3858646 : Nat := 4983230072969 + 3 ^ 40 * 3858646 * 2
def baseEnd_3858646 : Nat := 1320893382365876842319611

theorem tailTrace_3858646 : CollatzResearch.WordTrace tailWord_3858646 prefixEnd_3858646 1320893382365876842319611 := by
  unfold tailWord_3858646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796023848674501319743737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93824254385861347410599861 8796023848674501319743737)
  ·
    refine ⟨6597017886505875989807803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8796023848674501319743737 6597017886505875989807803)
    ·
      refine ⟨9895526829758813984711705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597017886505875989807803 9895526829758813984711705)
      ·
        refine ⟨7421645122319110488533779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9895526829758813984711705 7421645122319110488533779)
        ·
          refine ⟨11132467683478665732800669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421645122319110488533779 11132467683478665732800669)
          ·
            refine ⟨4174675381304499649800251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11132467683478665732800669 4174675381304499649800251)
            ·
              refine ⟨6262013071956749474700377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174675381304499649800251 6262013071956749474700377)
              ·
                refine ⟨4696509803967562106025283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262013071956749474700377 4696509803967562106025283)
                ·
                  refine ⟨7044764705951343159037925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696509803967562106025283 7044764705951343159037925)
                  ·
                    refine ⟨1320893382365876842319611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7044764705951343159037925 1320893382365876842319611)
                    ·
                      rfl

theorem cell22_3858646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3858646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858646 prefixEnd_3858646 := by exact prefixLift 3858646
  have htrace : WordTrace (prefixWord ++ tailWord_3858646) baseStart_3858646 baseEnd_3858646 := by
    simpa [prefixWord, tailWord_3858646, baseEnd_3858646] using wordTrace_append hprefix tailTrace_3858646
  have hstable : (prefixWord ++ tailWord_3858646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858646).length < 2 ^ (prefixWord ++ tailWord_3858646).sum := by decide
  have hdescent : baseEnd_3858646 < baseStart_3858646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858700 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_3858700 : Nat := 118140960795 + 3858700 * 2 ^ 59
def prefixEnd_3858700 : Nat := 4983230072969 + 3 ^ 40 * 3858700 * 2
def baseEnd_3858700 : Nat := 440303955889812900489815

theorem tailTrace_3858700 : CollatzResearch.WordTrace tailWord_3858700 prefixEnd_3858700 440303955889812900489815 := by
  unfold tailWord_3858700
  simp only [CollatzResearch.WordTrace]
  refine ⟨70369175560298194169182777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93825567413730925558910369 70369175560298194169182777)
  ·
    refine ⟨52776881670223645626887083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70369175560298194169182777 52776881670223645626887083)
    ·
      refine ⟨79165322505335468440330625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52776881670223645626887083 79165322505335468440330625)
      ·
        refine ⟨59373991879001601330247969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79165322505335468440330625 59373991879001601330247969)
        ·
          refine ⟨44530493909251200997685977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59373991879001601330247969 44530493909251200997685977)
          ·
            refine ⟨33397870431938400748264483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44530493909251200997685977 33397870431938400748264483)
            ·
              refine ⟨50096805647907601122396725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33397870431938400748264483 50096805647907601122396725)
              ·
                refine ⟨4696575529491337605224693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50096805647907601122396725 4696575529491337605224693)
                ·
                  refine ⟨440303955889812900489815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696575529491337605224693 440303955889812900489815)
                  ·
                    rfl

theorem cell22_3858700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_3858700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858700 prefixEnd_3858700 := by exact prefixLift 3858700
  have htrace : WordTrace (prefixWord ++ tailWord_3858700) baseStart_3858700 baseEnd_3858700 := by
    simpa [prefixWord, tailWord_3858700, baseEnd_3858700] using wordTrace_append hprefix tailTrace_3858700
  have hstable : (prefixWord ++ tailWord_3858700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858700).length < 2 ^ (prefixWord ++ tailWord_3858700).sum := by decide
  have hdescent : baseEnd_3858700 < baseStart_3858700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858734 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_3858734 : Nat := 118140960795 + 3858734 * 2 ^ 59
def prefixEnd_3858734 : Nat := 4983230072969 + 3 ^ 40 * 3858734 * 2
def baseEnd_3858734 : Nat := 440307835521424648706447

theorem tailTrace_3858734 : CollatzResearch.WordTrace tailWord_3858734 prefixEnd_3858734 440307835521424648706447 := by
  unfold tailWord_3858734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17592448900309151518137907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93826394134982141430068837 17592448900309151518137907)
  ·
    refine ⟨26388673350463727277206861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17592448900309151518137907 26388673350463727277206861)
    ·
      refine ⟨9895752506423897728952573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26388673350463727277206861 9895752506423897728952573)
      ·
        refine ⟨3710907189908961648357215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9895752506423897728952573 3710907189908961648357215)
        ·
          refine ⟨5566360784863442472535823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710907189908961648357215 5566360784863442472535823)
          ·
            refine ⟨8349541177295163708803735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566360784863442472535823 8349541177295163708803735)
            ·
              refine ⟨12524311765942745563205603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8349541177295163708803735 12524311765942745563205603)
              ·
                refine ⟨18786467648914118344808405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12524311765942745563205603 18786467648914118344808405)
                ·
                  refine ⟨440307835521424648706447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18786467648914118344808405 440307835521424648706447)
                  ·
                    rfl

theorem cell22_3858734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_3858734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858734 prefixEnd_3858734 := by exact prefixLift 3858734
  have htrace : WordTrace (prefixWord ++ tailWord_3858734) baseStart_3858734 baseEnd_3858734 := by
    simpa [prefixWord, tailWord_3858734, baseEnd_3858734] using wordTrace_append hprefix tailTrace_3858734
  have hstable : (prefixWord ++ tailWord_3858734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858734).length < 2 ^ (prefixWord ++ tailWord_3858734).sum := by decide
  have hdescent : baseEnd_3858734 < baseStart_3858734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858775 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_3858775 : Nat := 118140960795 + 3858775 * 2 ^ 59
def prefixEnd_3858775 : Nat := 4983230072969 + 3 ^ 40 * 3858775 * 2
def baseEnd_3858775 : Nat := 1320937541702163505844215

theorem tailTrace_3858775 : CollatzResearch.WordTrace tailWord_3858775 prefixEnd_3858775 1320937541702163505844215 := by
  unfold tailWord_3858775
  simp only [CollatzResearch.WordTrace]
  refine ⟨140741086595324676147345779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93827391063549784098230519 140741086595324676147345779)
  ·
    refine ⟨211111629892987014221018669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140741086595324676147345779 211111629892987014221018669)
    ·
      refine ⟨79166861209870130332882001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211111629892987014221018669 79166861209870130332882001)
      ·
        refine ⟨59375145907402597749661501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79166861209870130332882001 59375145907402597749661501)
        ·
          refine ⟨22265679715275974156123063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59375145907402597749661501 22265679715275974156123063)
          ·
            refine ⟨33398519572913961234184595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22265679715275974156123063 33398519572913961234184595)
            ·
              refine ⟨50097779359370941851276893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33398519572913961234184595 50097779359370941851276893)
              ·
                refine ⟨18786667259764103194228835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50097779359370941851276893 18786667259764103194228835)
                ·
                  refine ⟨28180000889646154791343253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18786667259764103194228835 28180000889646154791343253)
                  ·
                    refine ⟨1320937541702163505844215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28180000889646154791343253 1320937541702163505844215)
                    ·
                      rfl

theorem cell22_3858775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_3858775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858775 prefixEnd_3858775 := by exact prefixLift 3858775
  have htrace : WordTrace (prefixWord ++ tailWord_3858775) baseStart_3858775 baseEnd_3858775 := by
    simpa [prefixWord, tailWord_3858775, baseEnd_3858775] using wordTrace_append hprefix tailTrace_3858775
  have hstable : (prefixWord ++ tailWord_3858775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858775).length < 2 ^ (prefixWord ++ tailWord_3858775).sum := by decide
  have hdescent : baseEnd_3858775 < baseStart_3858775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858792 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3858792 : Nat := 118140960795 + 3858792 * 2 ^ 59
def prefixEnd_3858792 : Nat := 4983230072969 + 3 ^ 40 * 3858792 * 2
def baseEnd_3858792 : Nat := 1320943361149581128169163

theorem tailTrace_3858792 : CollatzResearch.WordTrace tailWord_3858792 prefixEnd_3858792 1320943361149581128169163 := by
  unfold tailWord_3858792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370853318131544025357315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93827804424175392033809753 70370853318131544025357315)
  ·
    refine ⟨105556279977197316038035973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70370853318131544025357315 105556279977197316038035973)
    ·
      refine ⟨19791802495724496757131745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105556279977197316038035973 19791802495724496757131745)
      ·
        refine ⟨14843851871793372567848809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19791802495724496757131745 14843851871793372567848809)
        ·
          refine ⟨11132888903845029425886607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14843851871793372567848809 11132888903845029425886607)
          ·
            refine ⟨16699333355767544138829911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132888903845029425886607 16699333355767544138829911)
            ·
              refine ⟨25049000033651316208244867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16699333355767544138829911 25049000033651316208244867)
              ·
                refine ⟨37573500050476974312367301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25049000033651316208244867 37573500050476974312367301)
                ·
                  refine ⟨7045031259464432683568869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37573500050476974312367301 7045031259464432683568869)
                  ·
                    refine ⟨1320943361149581128169163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045031259464432683568869 1320943361149581128169163)
                    ·
                      rfl

theorem cell22_3858792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3858792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858792 prefixEnd_3858792 := by exact prefixLift 3858792
  have htrace : WordTrace (prefixWord ++ tailWord_3858792) baseStart_3858792 baseEnd_3858792 := by
    simpa [prefixWord, tailWord_3858792, baseEnd_3858792] using wordTrace_append hprefix tailTrace_3858792
  have hstable : (prefixWord ++ tailWord_3858792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858792).length < 2 ^ (prefixWord ++ tailWord_3858792).sum := by decide
  have hdescent : baseEnd_3858792 < baseStart_3858792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858794 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3858794 : Nat := 118140960795 + 3858794 * 2 ^ 59
def prefixEnd_3858794 : Nat := 4983230072969 + 3 ^ 40 * 3858794 * 2
def baseEnd_3858794 : Nat := 1320944045790453789619157

theorem tailTrace_3858794 : CollatzResearch.WordTrace tailWord_3858794 prefixEnd_3858794 1320944045790453789619157 := by
  unfold tailWord_3858794
  simp only [CollatzResearch.WordTrace]
  refine ⟨35185444895563960598071859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93827853054837228261524957 35185444895563960598071859)
  ·
    refine ⟨52778167343345940897107789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35185444895563960598071859 52778167343345940897107789)
    ·
      refine ⟨19791812753754727836415421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52778167343345940897107789 19791812753754727836415421)
      ·
        refine ⟨7421929782658022938655783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19791812753754727836415421 7421929782658022938655783)
        ·
          refine ⟨11132894673987034407983675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421929782658022938655783 11132894673987034407983675)
          ·
            refine ⟨16699342010980551611975513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132894673987034407983675 16699342010980551611975513)
            ·
              refine ⟨12524506508235413708981635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16699342010980551611975513 12524506508235413708981635)
              ·
                refine ⟨18786759762353120563472453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12524506508235413708981635 18786759762353120563472453)
                ·
                  refine ⟨3522517455441210105651085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18786759762353120563472453 3522517455441210105651085)
                  ·
                    refine ⟨1320944045790453789619157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522517455441210105651085 1320944045790453789619157)
                    ·
                      rfl

theorem cell22_3858794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3858794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858794 prefixEnd_3858794 := by exact prefixLift 3858794
  have htrace : WordTrace (prefixWord ++ tailWord_3858794) baseStart_3858794 baseEnd_3858794 := by
    simpa [prefixWord, tailWord_3858794, baseEnd_3858794] using wordTrace_append hprefix tailTrace_3858794
  have hstable : (prefixWord ++ tailWord_3858794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858794).length < 2 ^ (prefixWord ++ tailWord_3858794).sum := by decide
  have hdescent : baseEnd_3858794 < baseStart_3858794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858796 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 4]
def baseStart_3858796 : Nat := 118140960795 + 3858796 * 2 ^ 59
def prefixEnd_3858796 : Nat := 4983230072969 + 3 ^ 40 * 3858796 * 2
def baseEnd_3858796 : Nat := 440314910143775483689717

theorem tailTrace_3858796 : CollatzResearch.WordTrace tailWord_3858796 prefixEnd_3858796 440314910143775483689717 := by
  unfold tailWord_3858796
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370926264124298366930121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93827901685499064489240161 70370926264124298366930121)
  ·
    refine ⟨52778194698093223775197591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70370926264124298366930121 52778194698093223775197591)
    ·
      refine ⟨79167292047139835662796387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52778194698093223775197591 79167292047139835662796387)
      ·
        refine ⟨118750938070709753494194581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79167292047139835662796387 118750938070709753494194581)
        ·
          refine ⟨5566450222064519695040371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118750938070709753494194581 5566450222064519695040371)
          ·
            refine ⟨8349675333096779542560557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566450222064519695040371 8349675333096779542560557)
            ·
              refine ⟨3131128249911292328460209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8349675333096779542560557 3131128249911292328460209)
              ·
                refine ⟨2348346187433469246345157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131128249911292328460209 2348346187433469246345157)
                ·
                  refine ⟨440314910143775483689717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348346187433469246345157 440314910143775483689717)
                  ·
                    rfl

theorem cell22_3858796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_3858796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858796 prefixEnd_3858796 := by exact prefixLift 3858796
  have htrace : WordTrace (prefixWord ++ tailWord_3858796) baseStart_3858796 baseEnd_3858796 := by
    simpa [prefixWord, tailWord_3858796, baseEnd_3858796] using wordTrace_append hprefix tailTrace_3858796
  have hstable : (prefixWord ++ tailWord_3858796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858796).length < 2 ^ (prefixWord ++ tailWord_3858796).sum := by decide
  have hdescent : baseEnd_3858796 < baseStart_3858796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858811 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 2, 3]
def baseStart_3858811 : Nat := 118140960795 + 3858811 * 2 ^ 59
def prefixEnd_3858811 : Nat := 4983230072969 + 3 ^ 40 * 3858811 * 2
def baseEnd_3858811 : Nat := 1320949865237871411944105

theorem tailTrace_3858811 : CollatzResearch.WordTrace tailWord_3858811 prefixEnd_3858811 1320949865237871411944105 := by
  unfold tailWord_3858811
  simp only [CollatzResearch.WordTrace]
  refine ⟨140742399623194254295656287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93828266415462836197104191 140742399623194254295656287)
  ·
    refine ⟨211113599434791381443484431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140742399623194254295656287 211113599434791381443484431)
    ·
      refine ⟨316670399152187072165226647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211113599434791381443484431 316670399152187072165226647)
      ·
        refine ⟨475005598728280608247839971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316670399152187072165226647 475005598728280608247839971)
        ·
          refine ⟨712508398092420912371759957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475005598728280608247839971 712508398092420912371759957)
          ·
            refine ⟨4174853895072778783428281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 712508398092420912371759957 4174853895072778783428281)
            ·
              refine ⟨3131140421304584087571211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174853895072778783428281 3131140421304584087571211)
              ·
                refine ⟨4696710631956876131356817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131140421304584087571211 4696710631956876131356817)
                ·
                  refine ⟨3522532973967657098517613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696710631956876131356817 3522532973967657098517613)
                  ·
                    refine ⟨1320949865237871411944105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522532973967657098517613 1320949865237871411944105)
                    ·
                      rfl

theorem cell22_3858811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 3].length) (baseStart_3858811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858811 prefixEnd_3858811 := by exact prefixLift 3858811
  have htrace : WordTrace (prefixWord ++ tailWord_3858811) baseStart_3858811 baseEnd_3858811 := by
    simpa [prefixWord, tailWord_3858811, baseEnd_3858811] using wordTrace_append hprefix tailTrace_3858811
  have hstable : (prefixWord ++ tailWord_3858811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858811).length < 2 ^ (prefixWord ++ tailWord_3858811).sum := by decide
  have hdescent : baseEnd_3858811 < baseStart_3858811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858826 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_3858826 : Nat := 118140960795 + 3858826 * 2 ^ 59
def prefixEnd_3858826 : Nat := 4983230072969 + 3 ^ 40 * 3858826 * 2
def baseEnd_3858826 : Nat := 1320955000044416372819059

theorem tailTrace_3858826 : CollatzResearch.WordTrace tailWord_3858826 prefixEnd_3858826 1320955000044416372819059 := by
  unfold tailWord_3858826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35185736679534977964363083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93828631145426607904968221 35185736679534977964363083)
  ·
    refine ⟨52778605019302466946544625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35185736679534977964363083 52778605019302466946544625)
    ·
      refine ⟨39583953764476850209908469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52778605019302466946544625 39583953764476850209908469)
      ·
        refine ⟨3710995665419704707178919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39583953764476850209908469 3710995665419704707178919)
        ·
          refine ⟨5566493498129557060768379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710995665419704707178919 5566493498129557060768379)
          ·
            refine ⟨8349740247194335591152569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566493498129557060768379 8349740247194335591152569)
            ·
              refine ⟨6262305185395751693364427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8349740247194335591152569 6262305185395751693364427)
              ·
                refine ⟨9393457778093627540046641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262305185395751693364427 9393457778093627540046641)
                ·
                  refine ⟨7045093333570220655034981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9393457778093627540046641 7045093333570220655034981)
                  ·
                    refine ⟨1320955000044416372819059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045093333570220655034981 1320955000044416372819059)
                    ·
                      rfl

theorem cell22_3858826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_3858826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858826 prefixEnd_3858826 := by exact prefixLift 3858826
  have htrace : WordTrace (prefixWord ++ tailWord_3858826) baseStart_3858826 baseEnd_3858826 := by
    simpa [prefixWord, tailWord_3858826, baseEnd_3858826] using wordTrace_append hprefix tailTrace_3858826
  have hstable : (prefixWord ++ tailWord_3858826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858826).length < 2 ^ (prefixWord ++ tailWord_3858826).sum := by decide
  have hdescent : baseEnd_3858826 < baseStart_3858826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858852 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_3858852 : Nat := 118140960795 + 3858852 * 2 ^ 59
def prefixEnd_3858852 : Nat := 4983230072969 + 3 ^ 40 * 3858852 * 2
def baseEnd_3858852 : Nat := 440321300125253657222993

theorem tailTrace_3858852 : CollatzResearch.WordTrace tailWord_3858852 prefixEnd_3858852 440321300125253657222993 := by
  unfold tailWord_3858852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70371947508022859148949405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93829263344030478865265873 70371947508022859148949405)
  ·
    refine ⟨26389480315508572180856027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70371947508022859148949405 26389480315508572180856027)
    ·
      refine ⟨39584220473262858271284041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26389480315508572180856027 39584220473262858271284041)
      ·
        refine ⟨29688165354947143703463031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39584220473262858271284041 29688165354947143703463031)
        ·
          refine ⟨44532248032420715555194547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29688165354947143703463031 44532248032420715555194547)
          ·
            refine ⟨66798372048631073332791821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44532248032420715555194547 66798372048631073332791821)
            ·
              refine ⟨25049389518236652499796933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66798372048631073332791821 25049389518236652499796933)
              ·
                refine ⟨4696760534669372343711925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25049389518236652499796933 4696760534669372343711925)
                ·
                  refine ⟨440321300125253657222993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696760534669372343711925 440321300125253657222993)
                  ·
                    rfl

theorem cell22_3858852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_3858852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858852 prefixEnd_3858852 := by exact prefixLift 3858852
  have htrace : WordTrace (prefixWord ++ tailWord_3858852) baseStart_3858852 baseEnd_3858852 := by
    simpa [prefixWord, tailWord_3858852, baseEnd_3858852] using wordTrace_append hprefix tailTrace_3858852
  have hstable : (prefixWord ++ tailWord_3858852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858852).length < 2 ^ (prefixWord ++ tailWord_3858852).sum := by decide
  have hdescent : baseEnd_3858852 < baseStart_3858852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858858 : List Nat := [3, 1, 6, 1, 1, 2, 1, 7]
def baseStart_3858858 : Nat := 118140960795 + 3858858 * 2 ^ 59
def prefixEnd_3858858 : Nat := 4983230072969 + 3 ^ 40 * 3858858 * 2
def baseEnd_3858858 : Nat := 146773994922042106224329

theorem tailTrace_3858858 : CollatzResearch.WordTrace tailWord_3858858 prefixEnd_3858858 146773994922042106224329 := by
  unfold tailWord_3858858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35186028463505995330654307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93829409236015987548411485 35186028463505995330654307)
  ·
    refine ⟨52779042695258992995981461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35186028463505995330654307 52779042695258992995981461)
    ·
      refine ⟨2474017626340265296686631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52779042695258992995981461 2474017626340265296686631)
      ·
        refine ⟨3711026439510397945029947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474017626340265296686631 3711026439510397945029947)
        ·
          refine ⟨5566539659265596917544921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711026439510397945029947 5566539659265596917544921)
          ·
            refine ⟨4174904744449197688158691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566539659265596917544921 4174904744449197688158691)
            ·
              refine ⟨6262357116673796532238037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174904744449197688158691 6262357116673796532238037)
              ·
                refine ⟨146773994922042106224329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6262357116673796532238037 146773994922042106224329)
                ·
                  rfl

theorem cell22_3858858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_3858858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858858 prefixEnd_3858858 := by exact prefixLift 3858858
  have htrace : WordTrace (prefixWord ++ tailWord_3858858) baseStart_3858858 baseEnd_3858858 := by
    simpa [prefixWord, tailWord_3858858, baseEnd_3858858] using wordTrace_append hprefix tailTrace_3858858
  have hstable : (prefixWord ++ tailWord_3858858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858858).length < 2 ^ (prefixWord ++ tailWord_3858858).sum := by decide
  have hdescent : baseEnd_3858858 < baseStart_3858858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858933 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3858933 : Nat := 118140960795 + 3858933 * 2 ^ 59
def prefixEnd_3858933 : Nat := 4983230072969 + 3 ^ 40 * 3858933 * 2
def baseEnd_3858933 : Nat := 1320991628331103760393731

theorem tailTrace_3858933 : CollatzResearch.WordTrace tailWord_3858933 prefixEnd_3858933 1320991628331103760393731 := by
  unfold tailWord_3858933
  simp only [CollatzResearch.WordTrace]
  refine ⟨140746849328752269131597453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93831232885834846087731635 140746849328752269131597453)
  ·
    refine ⟨52780068498282100924349045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140746849328752269131597453 52780068498282100924349045)
    ·
      refine ⟨4948131421713946961657723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52780068498282100924349045 4948131421713946961657723)
      ·
        refine ⟨7422197132570920442486585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948131421713946961657723 7422197132570920442486585)
        ·
          refine ⟨5566647849428190331864939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7422197132570920442486585 5566647849428190331864939)
          ·
            refine ⟨8349971774142285497797409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566647849428190331864939 8349971774142285497797409)
            ·
              refine ⟨6262478830606714123348057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8349971774142285497797409 6262478830606714123348057)
              ·
                refine ⟨4696859122955035592511043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262478830606714123348057 4696859122955035592511043)
                ·
                  refine ⟨7045288684432553388766565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696859122955035592511043 7045288684432553388766565)
                  ·
                    refine ⟨1320991628331103760393731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045288684432553388766565 1320991628331103760393731)
                    ·
                      rfl

theorem cell22_3858933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3858933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858933 prefixEnd_3858933 := by exact prefixLift 3858933
  have htrace : WordTrace (prefixWord ++ tailWord_3858933) baseStart_3858933 baseEnd_3858933 := by
    simpa [prefixWord, tailWord_3858933, baseEnd_3858933] using wordTrace_append hprefix tailTrace_3858933
  have hstable : (prefixWord ++ tailWord_3858933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858933).length < 2 ^ (prefixWord ++ tailWord_3858933).sum := by decide
  have hdescent : baseEnd_3858933 < baseStart_3858933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858948 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 4]
def baseStart_3858948 : Nat := 118140960795 + 3858948 * 2 ^ 59
def prefixEnd_3858948 : Nat := 4983230072969 + 3 ^ 40 * 3858948 * 2
def baseEnd_3858948 : Nat := 440332254379216240422895

theorem tailTrace_3858948 : CollatzResearch.WordTrace tailWord_3858948 prefixEnd_3858948 440332254379216240422895 := by
  unfold tailWord_3858948
  simp only [CollatzResearch.WordTrace]
  refine ⟨70373698211848963346696749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93831597615798617795595665 70373698211848963346696749)
  ·
    refine ⟨26390136829443361255011281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70373698211848963346696749 26390136829443361255011281)
    ·
      refine ⟨19792602622082520941258461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26390136829443361255011281 19792602622082520941258461)
      ·
        refine ⟨7422225983280945352971923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19792602622082520941258461 7422225983280945352971923)
        ·
          refine ⟨11133338974921418029457885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7422225983280945352971923 11133338974921418029457885)
          ·
            refine ⟨4175002115595531761046707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11133338974921418029457885 4175002115595531761046707)
            ·
              refine ⟨6262503173393297641570061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175002115595531761046707 6262503173393297641570061)
              ·
                refine ⟨2348438690022486615588773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6262503173393297641570061 2348438690022486615588773)
                ·
                  refine ⟨440332254379216240422895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348438690022486615588773 440332254379216240422895)
                  ·
                    rfl

theorem cell22_3858948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_3858948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858948 prefixEnd_3858948 := by exact prefixLift 3858948
  have htrace : WordTrace (prefixWord ++ tailWord_3858948) baseStart_3858948 baseEnd_3858948 := by
    simpa [prefixWord, tailWord_3858948, baseEnd_3858948] using wordTrace_append hprefix tailTrace_3858948
  have hstable : (prefixWord ++ tailWord_3858948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858948).length < 2 ^ (prefixWord ++ tailWord_3858948).sum := by decide
  have hdescent : baseEnd_3858948 < baseStart_3858948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858950 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3858950 : Nat := 118140960795 + 3858950 * 2 ^ 59
def prefixEnd_3858950 : Nat := 4983230072969 + 3 ^ 40 * 3858950 * 2
def baseEnd_3858950 : Nat := 1320997447778521382718679

theorem tailTrace_3858950 : CollatzResearch.WordTrace tailWord_3858950 prefixEnd_3858950 1320997447778521382718679 := by
  unfold tailWord_3858950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398358417802833782342697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93831646246460454023310869 4398358417802833782342697)
  ·
    refine ⟨3298768813352125336757023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4398358417802833782342697 3298768813352125336757023)
    ·
      refine ⟨4948153220028188005135535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298768813352125336757023 4948153220028188005135535)
      ·
        refine ⟨7422229830042282007703303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948153220028188005135535 7422229830042282007703303)
        ·
          refine ⟨11133344745063423011554955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7422229830042282007703303 11133344745063423011554955)
          ·
            refine ⟨16700017117595134517332433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11133344745063423011554955 16700017117595134517332433)
            ·
              refine ⟨12525012838196350887999325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16700017117595134517332433 12525012838196350887999325)
              ·
                refine ⟨4696879814323631582999747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12525012838196350887999325 4696879814323631582999747)
                ·
                  refine ⟨7045319721485447374499621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696879814323631582999747 7045319721485447374499621)
                  ·
                    refine ⟨1320997447778521382718679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045319721485447374499621 1320997447778521382718679)
                    ·
                      rfl

theorem cell22_3858950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3858950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3858950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3858950 prefixEnd_3858950 := by exact prefixLift 3858950
  have htrace : WordTrace (prefixWord ++ tailWord_3858950) baseStart_3858950 baseEnd_3858950 := by
    simpa [prefixWord, tailWord_3858950, baseEnd_3858950] using wordTrace_append hprefix tailTrace_3858950
  have hstable : (prefixWord ++ tailWord_3858950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858950).length < 2 ^ (prefixWord ++ tailWord_3858950).sum := by decide
  have hdescent : baseEnd_3858950 < baseStart_3858950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859021 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3859021 : Nat := 118140960795 + 3859021 * 2 ^ 59
def prefixEnd_3859021 : Nat := 4983230072969 + 3 ^ 40 * 3859021 * 2
def baseEnd_3859021 : Nat := 440340584176500288064487

theorem tailTrace_3859021 : CollatzResearch.WordTrace tailWord_3859021 prefixEnd_3859021 440340584176500288064487 := by
  unfold tailWord_3859021
  simp only [CollatzResearch.WordTrace]
  refine ⟨140750058952433460160800917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93833372634955640107200611 140750058952433460160800917)
  ·
    refine ⟨6597659013395318445037543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140750058952433460160800917 6597659013395318445037543)
    ·
      refine ⟨9896488520092977667556315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597659013395318445037543 9896488520092977667556315)
      ·
        refine ⟨14844732780139466501334473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896488520092977667556315 14844732780139466501334473)
        ·
          refine ⟨11133549585104599876000855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14844732780139466501334473 11133549585104599876000855)
          ·
            refine ⟨16700324377656899814001283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11133549585104599876000855 16700324377656899814001283)
            ·
              refine ⟨25050486566485349721001925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16700324377656899814001283 25050486566485349721001925)
              ·
                refine ⟨4696966231216003072687861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25050486566485349721001925 4696966231216003072687861)
                ·
                  refine ⟨440340584176500288064487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696966231216003072687861 440340584176500288064487)
                  ·
                    rfl

theorem cell22_3859021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3859021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859021 prefixEnd_3859021 := by exact prefixLift 3859021
  have htrace : WordTrace (prefixWord ++ tailWord_3859021) baseStart_3859021 baseEnd_3859021 := by
    simpa [prefixWord, tailWord_3859021, baseEnd_3859021] using wordTrace_append hprefix tailTrace_3859021
  have hstable : (prefixWord ++ tailWord_3859021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859021).length < 2 ^ (prefixWord ++ tailWord_3859021).sum := by decide
  have hdescent : baseEnd_3859021 < baseStart_3859021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859025 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 1, 3]
def baseStart_3859025 : Nat := 118140960795 + 3859025 * 2 ^ 59
def prefixEnd_3859025 : Nat := 4983230072969 + 3 ^ 40 * 3859025 * 2
def baseEnd_3859025 : Nat := 1321023121811246187093449

theorem tailTrace_3859025 : CollatzResearch.WordTrace tailWord_3859025 prefixEnd_3859025 1321023121811246187093449 := by
  unfold tailWord_3859025
  simp only [CollatzResearch.WordTrace]
  refine ⟨140750204844418968843946529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93833469896279312562631019 140750204844418968843946529)
  ·
    refine ⟨105562653633314226632959897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140750204844418968843946529 105562653633314226632959897)
    ·
      refine ⟨79171990224985669974719923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105562653633314226632959897 79171990224985669974719923)
      ·
        refine ⟨118757985337478504962079885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79171990224985669974719923 118757985337478504962079885)
        ·
          refine ⟨44534244501554439360779957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118757985337478504962079885 44534244501554439360779957)
          ·
            refine ⟨4175085422020728690073121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44534244501554439360779957 4175085422020728690073121)
            ·
              refine ⟨3131314066515546517554841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4175085422020728690073121 3131314066515546517554841)
              ·
                refine ⟨2348485549886659888166131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131314066515546517554841 2348485549886659888166131)
                ·
                  refine ⟨3522728324829989832249197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348485549886659888166131 3522728324829989832249197)
                  ·
                    refine ⟨1321023121811246187093449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522728324829989832249197 1321023121811246187093449)
                    ·
                      rfl

theorem cell22_3859025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_3859025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859025 prefixEnd_3859025 := by exact prefixLift 3859025
  have htrace : WordTrace (prefixWord ++ tailWord_3859025) baseStart_3859025 baseEnd_3859025 := by
    simpa [prefixWord, tailWord_3859025, baseEnd_3859025] using wordTrace_append hprefix tailTrace_3859025
  have hstable : (prefixWord ++ tailWord_3859025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859025).length < 2 ^ (prefixWord ++ tailWord_3859025).sum := by decide
  have hdescent : baseEnd_3859025 < baseStart_3859025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859036 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3859036 : Nat := 118140960795 + 3859036 * 2 ^ 59
def prefixEnd_3859036 : Nat := 4983230072969 + 3 ^ 40 * 3859036 * 2
def baseEnd_3859036 : Nat := 1321026887336045825068415

theorem tailTrace_3859036 : CollatzResearch.WordTrace tailWord_3859036 prefixEnd_3859036 1321026887336045825068415 := by
  unfold tailWord_3859036
  simp only [CollatzResearch.WordTrace]
  refine ⟨70375303023689558861298481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93833737364919411815064641 70375303023689558861298481)
  ·
    refine ⟨52781477267767169145973861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70375303023689558861298481 52781477267767169145973861)
    ·
      refine ⟨9896526987706344214870099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52781477267767169145973861 9896526987706344214870099)
      ·
        refine ⟨14844790481559516322305149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896526987706344214870099 14844790481559516322305149)
        ·
          refine ⟨5566796430584818620864431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14844790481559516322305149 5566796430584818620864431)
          ·
            refine ⟨8350194645877227931296647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566796430584818620864431 8350194645877227931296647)
            ·
              refine ⟨12525291968815841896944971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350194645877227931296647 12525291968815841896944971)
              ·
                refine ⟨18787937953223762845417457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525291968815841896944971 18787937953223762845417457)
                ·
                  refine ⟨14090953464917822134063093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18787937953223762845417457 14090953464917822134063093)
                  ·
                    refine ⟨1321026887336045825068415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14090953464917822134063093 1321026887336045825068415)
                    ·
                      rfl

theorem cell22_3859036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3859036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859036 prefixEnd_3859036 := by exact prefixLift 3859036
  have htrace : WordTrace (prefixWord ++ tailWord_3859036) baseStart_3859036 baseEnd_3859036 := by
    simpa [prefixWord, tailWord_3859036, baseEnd_3859036] using wordTrace_append hprefix tailTrace_3859036
  have hstable : (prefixWord ++ tailWord_3859036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859036).length < 2 ^ (prefixWord ++ tailWord_3859036).sum := by decide
  have hdescent : baseEnd_3859036 < baseStart_3859036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859064 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_3859064 : Nat := 118140960795 + 3859064 * 2 ^ 59
def prefixEnd_3859064 : Nat := 4983230072969 + 3 ^ 40 * 3859064 * 2
def baseEnd_3859064 : Nat := 1321036472308263085368329

theorem tailTrace_3859064 : CollatzResearch.WordTrace tailWord_3859064 prefixEnd_3859064 1321036472308263085368329 := by
  unfold tailWord_3859064
  simp only [CollatzResearch.WordTrace]
  refine ⟨70375813645638839252308123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93834418194185119003077497 70375813645638839252308123)
  ·
    refine ⟨105563720468458258878462185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70375813645638839252308123 105563720468458258878462185)
    ·
      refine ⟨79172790351343694158846639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105563720468458258878462185 79172790351343694158846639)
      ·
        refine ⟨118759185527015541238269959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79172790351343694158846639 118759185527015541238269959)
        ·
          refine ⟨178138778290523311857404939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118759185527015541238269959 178138778290523311857404939)
          ·
            refine ⟨267208167435784967786107409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178138778290523311857404939 267208167435784967786107409)
            ·
              refine ⟨200406125576838725839580557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267208167435784967786107409 200406125576838725839580557)
              ·
                refine ⟨75152297091314522189842709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200406125576838725839580557 75152297091314522189842709)
                ·
                  refine ⟨3522763926155368227648877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75152297091314522189842709 3522763926155368227648877)
                  ·
                    refine ⟨1321036472308263085368329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522763926155368227648877 1321036472308263085368329)
                    ·
                      rfl

theorem cell22_3859064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_3859064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859064 prefixEnd_3859064 := by exact prefixLift 3859064
  have htrace : WordTrace (prefixWord ++ tailWord_3859064) baseStart_3859064 baseEnd_3859064 := by
    simpa [prefixWord, tailWord_3859064, baseEnd_3859064] using wordTrace_append hprefix tailTrace_3859064
  have hstable : (prefixWord ++ tailWord_3859064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859064).length < 2 ^ (prefixWord ++ tailWord_3859064).sum := by decide
  have hdescent : baseEnd_3859064 < baseStart_3859064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859079 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3859079 : Nat := 118140960795 + 3859079 * 2 ^ 59
def prefixEnd_3859079 : Nat := 4983230072969 + 3 ^ 40 * 3859079 * 2
def baseEnd_3859079 : Nat := 1321041607114808046243283

theorem tailTrace_3859079 : CollatzResearch.WordTrace tailWord_3859079 prefixEnd_3859079 1321041607114808046243283 := by
  unfold tailWord_3859079
  simp only [CollatzResearch.WordTrace]
  refine ⟨140752174386223336066412291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93834782924148890710941527 140752174386223336066412291)
  ·
    refine ⟨211128261579335004099618437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140752174386223336066412291 211128261579335004099618437)
    ·
      refine ⟨39586549046125313268678457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211128261579335004099618437 39586549046125313268678457)
      ·
        refine ⟨29689911784593984951508843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39586549046125313268678457 29689911784593984951508843)
        ·
          refine ⟨44534867676890977427263265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29689911784593984951508843 44534867676890977427263265)
          ·
            refine ⟨33401150757668233070447449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44534867676890977427263265 33401150757668233070447449)
            ·
              refine ⟨25050863068251174802835587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33401150757668233070447449 25050863068251174802835587)
              ·
                refine ⟨37576294602376762204253381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25050863068251174802835587 37576294602376762204253381)
                ·
                  refine ⟨7045555237945642913297509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37576294602376762204253381 7045555237945642913297509)
                  ·
                    refine ⟨1321041607114808046243283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045555237945642913297509 1321041607114808046243283)
                    ·
                      rfl

theorem cell22_3859079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3859079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859079 prefixEnd_3859079 := by exact prefixLift 3859079
  have htrace : WordTrace (prefixWord ++ tailWord_3859079) baseStart_3859079 baseEnd_3859079 := by
    simpa [prefixWord, tailWord_3859079, baseEnd_3859079] using wordTrace_append hprefix tailTrace_3859079
  have hstable : (prefixWord ++ tailWord_3859079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859079).length < 2 ^ (prefixWord ++ tailWord_3859079).sum := by decide
  have hdescent : baseEnd_3859079 < baseStart_3859079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859149 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3859149 : Nat := 118140960795 + 3859149 * 2 ^ 59
def prefixEnd_3859149 : Nat := 4983230072969 + 3 ^ 40 * 3859149 * 2
def baseEnd_3859149 : Nat := 1321065569545351196993069

theorem tailTrace_3859149 : CollatzResearch.WordTrace tailWord_3859149 prefixEnd_3859149 1321065569545351196993069 := by
  unfold tailWord_3859149
  simp only [CollatzResearch.WordTrace]
  refine ⟨140754727495969738021460501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93836484997313158680973667 140754727495969738021460501)
  ·
    refine ⟨6597877851373581469755961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140754727495969738021460501 6597877851373581469755961)
    ·
      refine ⟨4948408388530186102316971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6597877851373581469755961 4948408388530186102316971)
      ·
        refine ⟨7422612582795279153475457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948408388530186102316971 7422612582795279153475457)
        ·
          refine ⟨5566959437096459365106593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7422612582795279153475457 5566959437096459365106593)
          ·
            refine ⟨4175219577822344523829945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566959437096459365106593 4175219577822344523829945)
            ·
              refine ⟨3131414683366758392872459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4175219577822344523829945 3131414683366758392872459)
              ·
                refine ⟨4697122025050137589308689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131414683366758392872459 4697122025050137589308689)
                ·
                  refine ⟨3522841518787603191981517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697122025050137589308689 3522841518787603191981517)
                  ·
                    refine ⟨1321065569545351196993069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522841518787603191981517 1321065569545351196993069)
                    ·
                      rfl

theorem cell22_3859149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3859149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859149 prefixEnd_3859149 := by exact prefixLift 3859149
  have htrace : WordTrace (prefixWord ++ tailWord_3859149) baseStart_3859149 baseEnd_3859149 := by
    simpa [prefixWord, tailWord_3859149, baseEnd_3859149] using wordTrace_append hprefix tailTrace_3859149
  have hstable : (prefixWord ++ tailWord_3859149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859149).length < 2 ^ (prefixWord ++ tailWord_3859149).sum := by decide
  have hdescent : baseEnd_3859149 < baseStart_3859149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859199 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_3859199 : Nat := 118140960795 + 3859199 * 2 ^ 59
def prefixEnd_3859199 : Nat := 4983230072969 + 3 ^ 40 * 3859199 * 2
def baseEnd_3859199 : Nat := 1321082685567167733242915

theorem tailTrace_3859199 : CollatzResearch.WordTrace tailWord_3859199 prefixEnd_3859199 1321082685567167733242915 := by
  unfold tailWord_3859199
  simp only [CollatzResearch.WordTrace]
  refine ⟨140756551145788596560780651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93837700763859064373853767 140756551145788596560780651)
  ·
    refine ⟨211134826718682894841170977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140756551145788596560780651 211134826718682894841170977)
    ·
      refine ⟨158351120039012171130878233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211134826718682894841170977 158351120039012171130878233)
      ·
        refine ⟨118763340029259128348158675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158351120039012171130878233 118763340029259128348158675)
        ·
          refine ⟨178145010043888692522238013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118763340029259128348158675 178145010043888692522238013)
          ·
            refine ⟨66804378766458259695839255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178145010043888692522238013 66804378766458259695839255)
            ·
              refine ⟨100206568149687389543758883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66804378766458259695839255 100206568149687389543758883)
              ·
                refine ⟨150309852224531084315638325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100206568149687389543758883 150309852224531084315638325)
                ·
                  refine ⟨14091548646049789154591093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150309852224531084315638325 14091548646049789154591093)
                  ·
                    refine ⟨1321082685567167733242915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14091548646049789154591093 1321082685567167733242915)
                    ·
                      rfl

theorem cell22_3859199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_3859199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859199 prefixEnd_3859199 := by exact prefixLift 3859199
  have htrace : WordTrace (prefixWord ++ tailWord_3859199) baseStart_3859199 baseEnd_3859199 := by
    simpa [prefixWord, tailWord_3859199, baseEnd_3859199] using wordTrace_append hprefix tailTrace_3859199
  have hstable : (prefixWord ++ tailWord_3859199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859199).length < 2 ^ (prefixWord ++ tailWord_3859199).sum := by decide
  have hdescent : baseEnd_3859199 < baseStart_3859199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859231 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 1, 6]
def baseStart_3859231 : Nat := 118140960795 + 3859231 * 2 ^ 59
def prefixEnd_3859231 : Nat := 4983230072969 + 3 ^ 40 * 3859231 * 2
def baseEnd_3859231 : Nat := 1321093639821130316442817

theorem tailTrace_3859231 : CollatzResearch.WordTrace tailWord_3859231 prefixEnd_3859231 1321093639821130316442817 := by
  unfold tailWord_3859231
  simp only [CollatzResearch.WordTrace]
  refine ⟨140757718281672666025945547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93838478854448444017297031 140757718281672666025945547)
  ·
    refine ⟨211136577422508999038918321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140757718281672666025945547 211136577422508999038918321)
    ·
      refine ⟨158352433066881749279188741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211136577422508999038918321 158352433066881749279188741)
      ·
        refine ⟨29691081200040327989847889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158352433066881749279188741 29691081200040327989847889)
        ·
          refine ⟨22268310900030245992385917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29691081200040327989847889 22268310900030245992385917)
          ·
            refine ⟨8350616587511342247144719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22268310900030245992385917 8350616587511342247144719)
            ·
              refine ⟨12525924881267013370717079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350616587511342247144719 12525924881267013370717079)
              ·
                refine ⟨18788887321900520056075619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525924881267013370717079 18788887321900520056075619)
                ·
                  refine ⟨28183330982850780084113429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18788887321900520056075619 28183330982850780084113429)
                  ·
                    refine ⟨1321093639821130316442817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28183330982850780084113429 1321093639821130316442817)
                    ·
                      rfl

theorem cell22_3859231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_3859231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859231 prefixEnd_3859231 := by exact prefixLift 3859231
  have htrace : WordTrace (prefixWord ++ tailWord_3859231) baseStart_3859231 baseEnd_3859231 := by
    simpa [prefixWord, tailWord_3859231, baseEnd_3859231] using wordTrace_append hprefix tailTrace_3859231
  have hstable : (prefixWord ++ tailWord_3859231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859231).length < 2 ^ (prefixWord ++ tailWord_3859231).sum := by decide
  have hdescent : baseEnd_3859231 < baseStart_3859231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859353 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 4]
def baseStart_3859353 : Nat := 118140960795 + 3859353 * 2 ^ 59
def prefixEnd_3859353 : Nat := 4983230072969 + 3 ^ 40 * 3859353 * 2
def baseEnd_3859353 : Nat := 440378467638120888297481

theorem tailTrace_3859353 : CollatzResearch.WordTrace tailWord_3859353 prefixEnd_3859353 440378467638120888297481 := by
  unfold tailWord_3859353
  simp only [CollatzResearch.WordTrace]
  refine ⟨140762167987230680861886713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93841445324820453907924475 140762167987230680861886713)
  ·
    refine ⟨105571625990423010646415035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140762167987230680861886713 105571625990423010646415035)
    ·
      refine ⟨158357438985634515969622553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105571625990423010646415035 158357438985634515969622553)
      ·
        refine ⟨118768079239225886977216915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158357438985634515969622553 118768079239225886977216915)
        ·
          refine ⟨178152118858838830465825373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118768079239225886977216915 178152118858838830465825373)
          ·
            refine ⟨66807044572064561424684515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178152118858838830465825373 66807044572064561424684515)
            ·
              refine ⟨100210566858096842137026773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66807044572064561424684515 100210566858096842137026773)
              ·
                refine ⟨2348685160736644737586565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100210566858096842137026773 2348685160736644737586565)
                ·
                  refine ⟨440378467638120888297481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348685160736644737586565 440378467638120888297481)
                  ·
                    rfl

theorem cell22_3859353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_3859353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859353 prefixEnd_3859353 := by exact prefixLift 3859353
  have htrace : WordTrace (prefixWord ++ tailWord_3859353) baseStart_3859353 baseEnd_3859353 := by
    simpa [prefixWord, tailWord_3859353, baseEnd_3859353] using wordTrace_append hprefix tailTrace_3859353
  have hstable : (prefixWord ++ tailWord_3859353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859353).length < 2 ^ (prefixWord ++ tailWord_3859353).sum := by decide
  have hdescent : baseEnd_3859353 < baseStart_3859353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859385 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_3859385 : Nat := 118140960795 + 3859385 * 2 ^ 59
def prefixEnd_3859385 : Nat := 4983230072969 + 3 ^ 40 * 3859385 * 2
def baseEnd_3859385 : Nat := 1321146357168325248092345

theorem tailTrace_3859385 : CollatzResearch.WordTrace tailWord_3859385 prefixEnd_3859385 1321146357168325248092345 := by
  unfold tailWord_3859385
  simp only [CollatzResearch.WordTrace]
  refine ⟨140763335123114750327051609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93842223415409833551367739 140763335123114750327051609)
  ·
    refine ⟨105572501342336062745288707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140763335123114750327051609 105572501342336062745288707)
    ·
      refine ⟨158358752013504094117933061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105572501342336062745288707 158358752013504094117933061)
      ·
        refine ⟨29692266002532017647112449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158358752013504094117933061 29692266002532017647112449)
        ·
          refine ⟨22269199501899013235334337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29692266002532017647112449 22269199501899013235334337)
          ·
            refine ⟨16701899626424259926500753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22269199501899013235334337 16701899626424259926500753)
            ·
              refine ⟨12526424719818194944875565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16701899626424259926500753 12526424719818194944875565)
              ·
                refine ⟨4697409269931823104328337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12526424719818194944875565 4697409269931823104328337)
                ·
                  refine ⟨3523056952448867328246253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697409269931823104328337 3523056952448867328246253)
                  ·
                    refine ⟨1321146357168325248092345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523056952448867328246253 1321146357168325248092345)
                    ·
                      rfl

theorem cell22_3859385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_3859385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859385 prefixEnd_3859385 := by exact prefixLift 3859385
  have htrace : WordTrace (prefixWord ++ tailWord_3859385) baseStart_3859385 baseEnd_3859385 := by
    simpa [prefixWord, tailWord_3859385, baseEnd_3859385] using wordTrace_append hprefix tailTrace_3859385
  have hstable : (prefixWord ++ tailWord_3859385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859385).length < 2 ^ (prefixWord ++ tailWord_3859385).sum := by decide
  have hdescent : baseEnd_3859385 < baseStart_3859385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859464 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 1, 3]
def baseStart_3859464 : Nat := 118140960795 + 3859464 * 2 ^ 59
def prefixEnd_3859464 : Nat := 4983230072969 + 3 ^ 40 * 3859464 * 2
def baseEnd_3859464 : Nat := 1321173400482795375367103

theorem tailTrace_3859464 : CollatzResearch.WordTrace tailWord_3859464 prefixEnd_3859464 1321173400482795375367103 := by
  unfold tailWord_3859464
  simp only [CollatzResearch.WordTrace]
  refine ⟨70383108244914273409588723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93844144326552364546118297 70383108244914273409588723)
  ·
    refine ⟨105574662367371410114383085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70383108244914273409588723 105574662367371410114383085)
    ·
      refine ⟨39590498387764278792893657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105574662367371410114383085 39590498387764278792893657)
      ·
        refine ⟨29692873790823209094670243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39590498387764278792893657 29692873790823209094670243)
        ·
          refine ⟨44539310686234813642005365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29692873790823209094670243 44539310686234813642005365)
          ·
            refine ⟨4175560376834513778938003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44539310686234813642005365 4175560376834513778938003)
            ·
              refine ⟨6263340565251770668407005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175560376834513778938003 6263340565251770668407005)
              ·
                refine ⟨2348752711969414000652627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6263340565251770668407005 2348752711969414000652627)
                ·
                  refine ⟨3523129067954121000978941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348752711969414000652627 3523129067954121000978941)
                  ·
                    refine ⟨1321173400482795375367103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523129067954121000978941 1321173400482795375367103)
                    ·
                      rfl

theorem cell22_3859464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_3859464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859464 prefixEnd_3859464 := by exact prefixLift 3859464
  have htrace : WordTrace (prefixWord ++ tailWord_3859464) baseStart_3859464 baseEnd_3859464 := by
    simpa [prefixWord, tailWord_3859464, baseEnd_3859464] using wordTrace_append hprefix tailTrace_3859464
  have hstable : (prefixWord ++ tailWord_3859464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859464).length < 2 ^ (prefixWord ++ tailWord_3859464).sum := by decide
  have hdescent : baseEnd_3859464 < baseStart_3859464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859554 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3859554 : Nat := 118140960795 + 3859554 * 2 ^ 59
def prefixEnd_3859554 : Nat := 4983230072969 + 3 ^ 40 * 3859554 * 2
def baseEnd_3859554 : Nat := 1321204209322065140616827

theorem tailTrace_3859554 : CollatzResearch.WordTrace tailWord_3859554 prefixEnd_3859554 1321204209322065140616827 := by
  unfold tailWord_3859554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35192374764875623047488429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93846332706334994793302477 35192374764875623047488429)
  ·
    refine ⟨13197140536828358642808161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35192374764875623047488429 13197140536828358642808161)
    ·
      refine ⟨9897855402621268982106121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13197140536828358642808161 9897855402621268982106121)
      ·
        refine ⟨7423391551965951736579591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9897855402621268982106121 7423391551965951736579591)
        ·
          refine ⟨11135087327948927604869387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423391551965951736579591 11135087327948927604869387)
          ·
            refine ⟨16702630991923391407304081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135087327948927604869387 16702630991923391407304081)
            ·
              refine ⟨12526973243942543555478061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702630991923391407304081 12526973243942543555478061)
              ·
                refine ⟨4697614966478453833304273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12526973243942543555478061 4697614966478453833304273)
                ·
                  refine ⟨3523211224858840374978205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697614966478453833304273 3523211224858840374978205)
                  ·
                    refine ⟨1321204209322065140616827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523211224858840374978205 1321204209322065140616827)
                    ·
                      rfl

theorem cell22_3859554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3859554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859554 prefixEnd_3859554 := by exact prefixLift 3859554
  have htrace : WordTrace (prefixWord ++ tailWord_3859554) baseStart_3859554 baseEnd_3859554 := by
    simpa [prefixWord, tailWord_3859554, baseEnd_3859554] using wordTrace_append hprefix tailTrace_3859554
  have hstable : (prefixWord ++ tailWord_3859554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859554).length < 2 ^ (prefixWord ++ tailWord_3859554).sum := by decide
  have hdescent : baseEnd_3859554 < baseStart_3859554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859650 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3859650 : Nat := 118140960795 + 3859650 * 2 ^ 59
def prefixEnd_3859650 : Nat := 4983230072969 + 3 ^ 40 * 3859650 * 2
def baseEnd_3859650 : Nat := 1321237072083952890216533

theorem tailTrace_3859650 : CollatzResearch.WordTrace tailWord_3859650 prefixEnd_3859650 1321237072083952890216533 := by
  unfold tailWord_3859650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35193250116788675146362101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93848666978103133723632269 35193250116788675146362101)
  ·
    refine ⟨3299367198448938294971447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35193250116788675146362101 3299367198448938294971447)
    ·
      refine ⟨4949050797673407442457171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299367198448938294971447 4949050797673407442457171)
      ·
        refine ⟨7423576196510111163685757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4949050797673407442457171 7423576196510111163685757)
        ·
          refine ⟨2783841073691291686382159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7423576196510111163685757 2783841073691291686382159)
          ·
            refine ⟨4175761610536937529573239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783841073691291686382159 4175761610536937529573239)
            ·
              refine ⟨6263642415805406294359859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175761610536937529573239 6263642415805406294359859)
              ·
                refine ⟨9395463623708109441539789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263642415805406294359859 9395463623708109441539789)
                ·
                  refine ⟨3523298858890541040577421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9395463623708109441539789 3523298858890541040577421)
                  ·
                    refine ⟨1321237072083952890216533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523298858890541040577421 1321237072083952890216533)
                    ·
                      rfl

theorem cell22_3859650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3859650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859650 prefixEnd_3859650 := by exact prefixLift 3859650
  have htrace : WordTrace (prefixWord ++ tailWord_3859650) baseStart_3859650 baseEnd_3859650 := by
    simpa [prefixWord, tailWord_3859650, baseEnd_3859650] using wordTrace_append hprefix tailTrace_3859650
  have hstable : (prefixWord ++ tailWord_3859650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859650).length < 2 ^ (prefixWord ++ tailWord_3859650).sum := by decide
  have hdescent : baseEnd_3859650 < baseStart_3859650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
