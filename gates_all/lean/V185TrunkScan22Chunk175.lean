import V185TrunkScan22Chunk174

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1561696 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_1561696 : Nat := 118140960795 + 1561696 * 2 ^ 59
def prefixEnd_1561696 : Nat := 4983230072969 + 3 ^ 40 * 1561696 * 2
def baseEnd_1561696 : Nat := 534600456136018060611931

theorem tailTrace_1561696 : CollatzResearch.WordTrace tailWord_1561696 prefixEnd_1561696 534600456136018060611931 := by
  unfold tailWord_1561696
  simp only [CollatzResearch.WordTrace]
  refine ⟨28479866275124791643764471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37973155033499722191685961 28479866275124791643764471)
  ·
    refine ⟨42719799412687187465646707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28479866275124791643764471 42719799412687187465646707)
    ·
      refine ⟨64079699119030781198470061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42719799412687187465646707 64079699119030781198470061)
      ·
        refine ⟨24029887169636542949426273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64079699119030781198470061 24029887169636542949426273)
        ·
          refine ⟨18022415377227407212069705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24029887169636542949426273 18022415377227407212069705)
          ·
            refine ⟨13516811532920555409052279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18022415377227407212069705 13516811532920555409052279)
            ·
              refine ⟨20275217299380833113578419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13516811532920555409052279 20275217299380833113578419)
              ·
                refine ⟨30412825949071249670367629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20275217299380833113578419 30412825949071249670367629)
                ·
                  refine ⟨11404809730901718626387861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30412825949071249670367629 11404809730901718626387861)
                  ·
                    refine ⟨534600456136018060611931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11404809730901718626387861 534600456136018060611931)
                    ·
                      rfl

theorem cell22_1561696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_1561696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561696 prefixEnd_1561696 := by exact prefixLift 1561696
  have htrace : WordTrace (prefixWord ++ tailWord_1561696) baseStart_1561696 baseEnd_1561696 := by
    simpa [prefixWord, tailWord_1561696, baseEnd_1561696] using wordTrace_append hprefix tailTrace_1561696
  have hstable : (prefixWord ++ tailWord_1561696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561696).length < 2 ^ (prefixWord ++ tailWord_1561696).sum := by decide
  have hdescent : baseEnd_1561696 < baseStart_1561696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561711 : List Nat := [1, 1, 2, 1, 3, 3, 3, 8]
def baseStart_1561711 : Nat := 118140960795 + 1561711 * 2 ^ 59
def prefixEnd_1561711 : Nat := 4983230072969 + 3 ^ 40 * 1561711 * 2
def baseEnd_1561711 : Nat := 59400621215840335720765

theorem tailTrace_1561711 : CollatzResearch.WordTrace tailWord_1561711 prefixEnd_1561711 59400621215840335720765 := by
  unfold tailWord_1561711
  simp only [CollatzResearch.WordTrace]
  refine ⟨56960279645195240849324987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37973519763463493899549991 56960279645195240849324987)
  ·
    refine ⟨85440419467792861273987481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56960279645195240849324987 85440419467792861273987481)
    ·
      refine ⟨64080314600844645955490611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85440419467792861273987481 64080314600844645955490611)
      ·
        refine ⟨96120471901266968933235917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64080314600844645955490611 96120471901266968933235917)
        ·
          refine ⟨36045176962975113349963469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96120471901266968933235917 36045176962975113349963469)
          ·
            refine ⟨13516941361115667506236301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36045176962975113349963469 13516941361115667506236301)
            ·
              refine ⟨5068853010418375314838613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13516941361115667506236301 5068853010418375314838613)
              ·
                refine ⟨59400621215840335720765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5068853010418375314838613 59400621215840335720765)
                ·
                  rfl

theorem cell22_1561711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 8].length) (baseStart_1561711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561711 prefixEnd_1561711 := by exact prefixLift 1561711
  have htrace : WordTrace (prefixWord ++ tailWord_1561711) baseStart_1561711 baseEnd_1561711 := by
    simpa [prefixWord, tailWord_1561711, baseEnd_1561711] using wordTrace_append hprefix tailTrace_1561711
  have hstable : (prefixWord ++ tailWord_1561711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561711).length < 2 ^ (prefixWord ++ tailWord_1561711).sum := by decide
  have hdescent : baseEnd_1561711 < baseStart_1561711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561790 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1561790 : Nat := 118140960795 + 1561790 * 2 ^ 59
def prefixEnd_1561790 : Nat := 4983230072969 + 3 ^ 40 * 1561790 * 2
def baseEnd_1561790 : Nat := 178210878085677716253881

theorem tailTrace_1561790 : CollatzResearch.WordTrace tailWord_1561790 prefixEnd_1561790 178210878085677716253881 := by
  unfold tailWord_1561790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120395126488629667681353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37975440674606024894300549 7120395126488629667681353)
  ·
    refine ⟨5340296344866472250761015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7120395126488629667681353 5340296344866472250761015)
    ·
      refine ⟨8010444517299708376141523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340296344866472250761015 8010444517299708376141523)
      ·
        refine ⟨12015666775949562564212285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010444517299708376141523 12015666775949562564212285)
        ·
          refine ⟨4505875040981085961579607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12015666775949562564212285 4505875040981085961579607)
          ·
            refine ⟨6758812561471628942369411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505875040981085961579607 6758812561471628942369411)
            ·
              refine ⟨10138218842207443413554117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758812561471628942369411 10138218842207443413554117)
              ·
                refine ⟨1900916032913895640041397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10138218842207443413554117 1900916032913895640041397)
                ·
                  refine ⟨178210878085677716253881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900916032913895640041397 178210878085677716253881)
                  ·
                    rfl

theorem cell22_1561790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1561790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561790 prefixEnd_1561790 := by exact prefixLift 1561790
  have htrace : WordTrace (prefixWord ++ tailWord_1561790) baseStart_1561790 baseEnd_1561790 := by
    simpa [prefixWord, tailWord_1561790, baseEnd_1561790] using wordTrace_append hprefix tailTrace_1561790
  have hstable : (prefixWord ++ tailWord_1561790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561790).length < 2 ^ (prefixWord ++ tailWord_1561790).sum := by decide
  have hdescent : baseEnd_1561790 < baseStart_1561790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561835 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 4]
def baseStart_1561835 : Nat := 118140960795 + 1561835 * 2 ^ 59
def prefixEnd_1561835 : Nat := 4983230072969 + 3 ^ 40 * 1561835 * 2
def baseEnd_1561835 : Nat := 178216012892222677128835

theorem tailTrace_1561835 : CollatzResearch.WordTrace tailWord_1561835 prefixEnd_1561835 178216012892222677128835 := by
  unfold tailWord_1561835
  simp only [CollatzResearch.WordTrace]
  refine ⟨56964802296746010026838959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37976534864497340017892639 56964802296746010026838959)
  ·
    refine ⟨85447203445119015040258439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56964802296746010026838959 85447203445119015040258439)
    ·
      refine ⟨128170805167678522560387659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85447203445119015040258439 128170805167678522560387659)
      ·
        refine ⟨192256207751517783840581489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128170805167678522560387659 192256207751517783840581489)
        ·
          refine ⟨144192155813638337880436117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192256207751517783840581489 144192155813638337880436117)
          ·
            refine ⟨6759007303764297088145443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144192155813638337880436117 6759007303764297088145443)
            ·
              refine ⟨10138510955646445632218165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759007303764297088145443 10138510955646445632218165)
              ·
                refine ⟨950485402091854278020453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10138510955646445632218165 950485402091854278020453)
                ·
                  refine ⟨178216012892222677128835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950485402091854278020453 178216012892222677128835)
                  ·
                    rfl

theorem cell22_1561835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 4].length) (baseStart_1561835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561835 prefixEnd_1561835 := by exact prefixLift 1561835
  have htrace : WordTrace (prefixWord ++ tailWord_1561835) baseStart_1561835 baseEnd_1561835 := by
    simpa [prefixWord, tailWord_1561835, baseEnd_1561835] using wordTrace_append hprefix tailTrace_1561835
  have hstable : (prefixWord ++ tailWord_1561835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561835).length < 2 ^ (prefixWord ++ tailWord_1561835).sum := by decide
  have hdescent : baseEnd_1561835 < baseStart_1561835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561837 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1561837 : Nat := 118140960795 + 1561837 * 2 ^ 59
def prefixEnd_1561837 : Nat := 4983230072969 + 3 ^ 40 * 1561837 * 2
def baseEnd_1561837 : Nat := 534648723317540692836499

theorem tailTrace_1561837 : CollatzResearch.WordTrace tailWord_1561837 prefixEnd_1561837 534648723317540692836499 := by
  unfold tailWord_1561837
  simp only [CollatzResearch.WordTrace]
  refine ⟨56964875242738764368411765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37976583495159176245607843 56964875242738764368411765)
  ·
    refine ⟨5340457054006759159538603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56964875242738764368411765 5340457054006759159538603)
    ·
      refine ⟨8010685581010138739307905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340457054006759159538603 8010685581010138739307905)
      ·
        refine ⟨6008014185757604054480929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8010685581010138739307905 6008014185757604054480929)
        ·
          refine ⟨4506010639318203040860697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6008014185757604054480929 4506010639318203040860697)
          ·
            refine ⟨3379507979488652280645523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4506010639318203040860697 3379507979488652280645523)
            ·
              refine ⟨5069261969232978420968285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379507979488652280645523 5069261969232978420968285)
              ·
                refine ⟨1900973238462366907863107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069261969232978420968285 1900973238462366907863107)
                ·
                  refine ⟨2851459857693550361794661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900973238462366907863107 2851459857693550361794661)
                  ·
                    refine ⟨534648723317540692836499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2851459857693550361794661 534648723317540692836499)
                    ·
                      rfl

theorem cell22_1561837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1561837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561837 prefixEnd_1561837 := by exact prefixLift 1561837
  have htrace : WordTrace (prefixWord ++ tailWord_1561837) baseStart_1561837 baseEnd_1561837 := by
    simpa [prefixWord, tailWord_1561837, baseEnd_1561837] using wordTrace_append hprefix tailTrace_1561837
  have hstable : (prefixWord ++ tailWord_1561837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561837).length < 2 ^ (prefixWord ++ tailWord_1561837).sum := by decide
  have hdescent : baseEnd_1561837 < baseStart_1561837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561850 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_1561850 : Nat := 118140960795 + 1561850 * 2 ^ 59
def prefixEnd_1561850 : Nat := 4983230072969 + 3 ^ 40 * 1561850 * 2
def baseEnd_1561850 : Nat := 534653173483212992261459

theorem tailTrace_1561850 : CollatzResearch.WordTrace tailWord_1561850 prefixEnd_1561850 534653173483212992261459 := by
  unfold tailWord_1561850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241337347922916897158751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37976899594461111725756669 14241337347922916897158751)
  ·
    refine ⟨21362006021884375345738127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14241337347922916897158751 21362006021884375345738127)
    ·
      refine ⟨32043009032826563018607191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21362006021884375345738127 32043009032826563018607191)
      ·
        refine ⟨48064513549239844527910787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32043009032826563018607191 48064513549239844527910787)
        ·
          refine ⟨72096770323859766791866181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48064513549239844527910787 72096770323859766791866181)
          ·
            refine ⟨13518144435723706273474909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72096770323859766791866181 13518144435723706273474909)
            ·
              refine ⟨5069304163396389852553091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13518144435723706273474909 5069304163396389852553091)
              ·
                refine ⟨7603956245094584778829637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069304163396389852553091 7603956245094584778829637)
                ·
                  refine ⟨1425741795955234646030557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7603956245094584778829637 1425741795955234646030557)
                  ·
                    refine ⟨534653173483212992261459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425741795955234646030557 534653173483212992261459)
                    ·
                      rfl

theorem cell22_1561850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_1561850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561850 prefixEnd_1561850 := by exact prefixLift 1561850
  have htrace : WordTrace (prefixWord ++ tailWord_1561850) baseStart_1561850 baseEnd_1561850 := by
    simpa [prefixWord, tailWord_1561850, baseEnd_1561850] using wordTrace_append hprefix tailTrace_1561850
  have hstable : (prefixWord ++ tailWord_1561850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561850).length < 2 ^ (prefixWord ++ tailWord_1561850).sum := by decide
  have hdescent : baseEnd_1561850 < baseStart_1561850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561880 : List Nat := [2, 1, 2, 3, 1, 3, 4, 6]
def baseStart_1561880 : Nat := 118140960795 + 1561880 * 2 ^ 59
def prefixEnd_1561880 : Nat := 4983230072969 + 3 ^ 40 * 1561880 * 2
def baseEnd_1561880 : Nat := 59407049232922546001263

theorem tailTrace_1561880 : CollatzResearch.WordTrace tailWord_1561880 prefixEnd_1561880 59407049232922546001263 := by
  unfold tailWord_1561880
  simp only [CollatzResearch.WordTrace]
  refine ⟨28483221790791491356113547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37977629054388655141484729 28483221790791491356113547)
  ·
    refine ⟨42724832686187237034170321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28483221790791491356113547 42724832686187237034170321)
    ·
      refine ⟨32043624514640427775627741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42724832686187237034170321 32043624514640427775627741)
      ·
        refine ⟨12016359192990160415860403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32043624514640427775627741 12016359192990160415860403)
        ·
          refine ⟨18024538789485240623790605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016359192990160415860403 18024538789485240623790605)
          ·
            refine ⟨6759202046056965233921477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18024538789485240623790605 6759202046056965233921477)
            ·
              refine ⟨1267350383635680981360277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6759202046056965233921477 1267350383635680981360277)
              ·
                refine ⟨59407049232922546001263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1267350383635680981360277 59407049232922546001263)
                ·
                  rfl

theorem cell22_1561880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_1561880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561880 prefixEnd_1561880 := by exact prefixLift 1561880
  have htrace : WordTrace (prefixWord ++ tailWord_1561880) baseStart_1561880 baseEnd_1561880 := by
    simpa [prefixWord, tailWord_1561880, baseEnd_1561880] using wordTrace_append hprefix tailTrace_1561880
  have hstable : (prefixWord ++ tailWord_1561880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561880).length < 2 ^ (prefixWord ++ tailWord_1561880).sum := by decide
  have hdescent : baseEnd_1561880 < baseStart_1561880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561923 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_1561923 : Nat := 118140960795 + 1561923 * 2 ^ 59
def prefixEnd_1561923 : Nat := 4983230072969 + 3 ^ 40 * 1561923 * 2
def baseEnd_1561923 : Nat := 534678162875065135186235

theorem tailTrace_1561923 : CollatzResearch.WordTrace tailWord_1561923 prefixEnd_1561923 534678162875065135186235 := by
  unfold tailWord_1561923
  simp only [CollatzResearch.WordTrace]
  refine ⟨56968011920427201056042423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37978674613618134037361615 56968011920427201056042423)
  ·
    refine ⟨85452017880640801584063635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56968011920427201056042423 85452017880640801584063635)
    ·
      refine ⟨128178026820961202376095453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85452017880640801584063635 128178026820961202376095453)
      ·
        refine ⟨48066760057860450891035795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128178026820961202376095453 48066760057860450891035795)
        ·
          refine ⟨72100140086790676336553693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48066760057860450891035795 72100140086790676336553693)
          ·
            refine ⟨27037552532546503626207635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72100140086790676336553693 27037552532546503626207635)
            ·
              refine ⟨40556328798819755439311453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27037552532546503626207635 40556328798819755439311453)
              ·
                refine ⟨15208623299557408289741795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40556328798819755439311453 15208623299557408289741795)
                ·
                  refine ⟨22812934949336112434612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15208623299557408289741795 22812934949336112434612693)
                  ·
                    refine ⟨534678162875065135186235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22812934949336112434612693 534678162875065135186235)
                    ·
                      rfl

theorem cell22_1561923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_1561923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561923 prefixEnd_1561923 := by exact prefixLift 1561923
  have htrace : WordTrace (prefixWord ++ tailWord_1561923) baseStart_1561923 baseEnd_1561923 := by
    simpa [prefixWord, tailWord_1561923, baseEnd_1561923] using wordTrace_append hprefix tailTrace_1561923
  have hstable : (prefixWord ++ tailWord_1561923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561923).length < 2 ^ (prefixWord ++ tailWord_1561923).sum := by decide
  have hdescent : baseEnd_1561923 < baseStart_1561923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561970 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1561970 : Nat := 118140960795 + 1561970 * 2 ^ 59
def prefixEnd_1561970 : Nat := 4983230072969 + 3 ^ 40 * 1561970 * 2
def baseEnd_1561970 : Nat := 178231417311857559753697

theorem tailTrace_1561970 : CollatzResearch.WordTrace tailWord_1561970 prefixEnd_1561970 178231417311857559753697 := by
  unfold tailWord_1561970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14242431537814232020750841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37979817434171285388668909 14242431537814232020750841)
  ·
    refine ⟨10681823653360674015563131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14242431537814232020750841 10681823653360674015563131)
    ·
      refine ⟨16022735480041011023344697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10681823653360674015563131 16022735480041011023344697)
      ·
        refine ⟨12017051610030758267508523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16022735480041011023344697 12017051610030758267508523)
        ·
          refine ⟨18025577415046137401262785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12017051610030758267508523 18025577415046137401262785)
          ·
            refine ⟨13519183061284603050947089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18025577415046137401262785 13519183061284603050947089)
            ·
              refine ⟨10139387295963452288210317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13519183061284603050947089 10139387295963452288210317)
              ·
                refine ⟨3802270235986294608078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10139387295963452288210317 3802270235986294608078869)
                ·
                  refine ⟨178231417311857559753697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3802270235986294608078869 178231417311857559753697)
                  ·
                    rfl

theorem cell22_1561970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1561970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1561970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1561970 prefixEnd_1561970 := by exact prefixLift 1561970
  have htrace : WordTrace (prefixWord ++ tailWord_1561970) baseStart_1561970 baseEnd_1561970 := by
    simpa [prefixWord, tailWord_1561970, baseEnd_1561970] using wordTrace_append hprefix tailTrace_1561970
  have hstable : (prefixWord ++ tailWord_1561970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561970).length < 2 ^ (prefixWord ++ tailWord_1561970).sum := by decide
  have hdescent : baseEnd_1561970 < baseStart_1561970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562004 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1562004 : Nat := 118140960795 + 1562004 * 2 ^ 59
def prefixEnd_1562004 : Nat := 4983230072969 + 3 ^ 40 * 1562004 * 2
def baseEnd_1562004 : Nat := 178235296943469307970329

theorem tailTrace_1562004 : CollatzResearch.WordTrace tailWord_1562004 prefixEnd_1562004 178235296943469307970329 := by
  unfold tailWord_1562004
  simp only [CollatzResearch.WordTrace]
  refine ⟨28485483116566875944870533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37980644155422501259827377 28485483116566875944870533)
  ·
    refine ⟨5341028084356289239663225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28485483116566875944870533 5341028084356289239663225)
    ·
      refine ⟨4005771063267216929747419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5341028084356289239663225 4005771063267216929747419)
      ·
        refine ⟨6008656594900825394621129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005771063267216929747419 6008656594900825394621129)
        ·
          refine ⟨4506492446175619045965847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6008656594900825394621129 4506492446175619045965847)
          ·
            refine ⟨6759738669263428568948771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506492446175619045965847 6759738669263428568948771)
            ·
              refine ⟨10139608003895142853423157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759738669263428568948771 10139608003895142853423157)
              ·
                refine ⟨950588250365169642508421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10139608003895142853423157 950588250365169642508421)
                ·
                  refine ⟨178235296943469307970329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950588250365169642508421 178235296943469307970329)
                  ·
                    rfl

theorem cell22_1562004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1562004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562004 prefixEnd_1562004 := by exact prefixLift 1562004
  have htrace : WordTrace (prefixWord ++ tailWord_1562004) baseStart_1562004 baseEnd_1562004 := by
    simpa [prefixWord, tailWord_1562004, baseEnd_1562004] using wordTrace_append hprefix tailTrace_1562004
  have hstable : (prefixWord ++ tailWord_1562004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562004).length < 2 ^ (prefixWord ++ tailWord_1562004).sum := by decide
  have hdescent : baseEnd_1562004 < baseStart_1562004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562015 : List Nat := [1, 1, 2, 5, 1, 3, 9]
def baseStart_1562015 : Nat := 118140960795 + 1562015 * 2 ^ 59
def prefixEnd_1562015 : Nat := 4983230072969 + 3 ^ 40 * 1562015 * 2
def baseEnd_1562015 : Nat := 19804061346489168958739

theorem tailTrace_1562015 : CollatzResearch.WordTrace tailWord_1562015 prefixEnd_1562015 19804061346489168958739 := by
  unfold tailWord_1562015
  simp only [CollatzResearch.WordTrace]
  refine ⟨56971367436093900768391499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37980911624062600512260999 56971367436093900768391499)
  ·
    refine ⟨85457051154140851152587249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56971367436093900768391499 85457051154140851152587249)
    ·
      refine ⟨64092788365605638364440437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85457051154140851152587249 64092788365605638364440437)
      ·
        refine ⟨6008698909275528596666291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64092788365605638364440437 6008698909275528596666291)
        ·
          refine ⟨9013048363913292894999437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008698909275528596666291 9013048363913292894999437)
          ·
            refine ⟨3379893136467484835624789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9013048363913292894999437 3379893136467484835624789)
            ·
              refine ⟨19804061346489168958739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3379893136467484835624789 19804061346489168958739)
              ·
                rfl

theorem cell22_1562015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 9].length) (baseStart_1562015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562015 prefixEnd_1562015 := by exact prefixLift 1562015
  have htrace : WordTrace (prefixWord ++ tailWord_1562015) baseStart_1562015 baseEnd_1562015 := by
    simpa [prefixWord, tailWord_1562015, baseEnd_1562015] using wordTrace_append hprefix tailTrace_1562015
  have hstable : (prefixWord ++ tailWord_1562015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562015).length < 2 ^ (prefixWord ++ tailWord_1562015).sum := by decide
  have hdescent : baseEnd_1562015 < baseStart_1562015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562077 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 7]
def baseStart_1562077 : Nat := 118140960795 + 1562077 * 2 ^ 59
def prefixEnd_1562077 : Nat := 4983230072969 + 3 ^ 40 * 1562077 * 2
def baseEnd_1562077 : Nat := 178243626740753355611921

theorem tailTrace_1562077 : CollatzResearch.WordTrace tailWord_1562077 prefixEnd_1562077 178243626740753355611921 := by
  unfold tailWord_1562077
  simp only [CollatzResearch.WordTrace]
  refine ⟨56973628761869285357148485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37982419174579523571432323 56973628761869285357148485)
  ·
    refine ⟨10682555392850491004465341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56973628761869285357148485 10682555392850491004465341)
    ·
      refine ⟨4005958272318934126674503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10682555392850491004465341 4005958272318934126674503)
      ·
        refine ⟨6008937408478401190011755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005958272318934126674503 6008937408478401190011755)
        ·
          refine ⟨9013406112717601785017633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008937408478401190011755 9013406112717601785017633)
          ·
            refine ⟨6760054584538201338763225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013406112717601785017633 6760054584538201338763225)
            ·
              refine ⟨5070040938403651004072419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6760054584538201338763225 5070040938403651004072419)
              ·
                refine ⟨7605061407605476506108629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070040938403651004072419 7605061407605476506108629)
                ·
                  refine ⟨178243626740753355611921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7605061407605476506108629 178243626740753355611921)
                  ·
                    rfl

theorem cell22_1562077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_1562077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562077 prefixEnd_1562077 := by exact prefixLift 1562077
  have htrace : WordTrace (prefixWord ++ tailWord_1562077) baseStart_1562077 baseEnd_1562077 := by
    simpa [prefixWord, tailWord_1562077, baseEnd_1562077] using wordTrace_append hprefix tailTrace_1562077
  have hstable : (prefixWord ++ tailWord_1562077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562077).length < 2 ^ (prefixWord ++ tailWord_1562077).sum := by decide
  have hdescent : baseEnd_1562077 < baseStart_1562077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562105 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 8]
def baseStart_1562105 : Nat := 118140960795 + 1562105 * 2 ^ 59
def prefixEnd_1562105 : Nat := 4983230072969 + 3 ^ 40 * 1562105 * 2
def baseEnd_1562105 : Nat := 178246821731492442378559

theorem tailTrace_1562105 : CollatzResearch.WordTrace tailWord_1562105 prefixEnd_1562105 178246821731492442378559 := by
  unfold tailWord_1562105
  simp only [CollatzResearch.WordTrace]
  refine ⟨56974650005767846139167769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37983100003845230759445179 56974650005767846139167769)
  ·
    refine ⟨42730987504325884604375827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56974650005767846139167769 42730987504325884604375827)
    ·
      refine ⟨64096481256488826906563741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42730987504325884604375827 64096481256488826906563741)
      ·
        refine ⟨24036180471183310089961403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64096481256488826906563741 24036180471183310089961403)
        ·
          refine ⟨36054270706774965134942105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24036180471183310089961403 36054270706774965134942105)
          ·
            refine ⟨27040703030081223851206579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36054270706774965134942105 27040703030081223851206579)
            ·
              refine ⟨40561054545121835776809869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27040703030081223851206579 40561054545121835776809869)
              ·
                refine ⟨15210395454420688416303701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40561054545121835776809869 15210395454420688416303701)
                ·
                  refine ⟨178246821731492442378559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15210395454420688416303701 178246821731492442378559)
                  ·
                    rfl

theorem cell22_1562105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_1562105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562105 prefixEnd_1562105 := by exact prefixLift 1562105
  have htrace : WordTrace (prefixWord ++ tailWord_1562105) baseStart_1562105 baseEnd_1562105 := by
    simpa [prefixWord, tailWord_1562105, baseEnd_1562105] using wordTrace_append hprefix tailTrace_1562105
  have hstable : (prefixWord ++ tailWord_1562105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562105).length < 2 ^ (prefixWord ++ tailWord_1562105).sum := by decide
  have hdescent : baseEnd_1562105 < baseStart_1562105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562132 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1562132 : Nat := 118140960795 + 1562132 * 2 ^ 59
def prefixEnd_1562132 : Nat := 4983230072969 + 3 ^ 40 * 1562132 * 2
def baseEnd_1562132 : Nat := 534749707846258256710595

theorem tailTrace_1562132 : CollatzResearch.WordTrace tailWord_1562132 prefixEnd_1562132 534749707846258256710595 := by
  unfold tailWord_1562132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28487817388335014875200325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37983756517780019833600433 28487817388335014875200325)
  ·
    refine ⟨5341465760312815289100061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28487817388335014875200325 5341465760312815289100061)
    ·
      refine ⟨2003049660117305733412523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5341465760312815289100061 2003049660117305733412523)
      ·
        refine ⟨3004574490175958600118785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003049660117305733412523 3004574490175958600118785)
        ·
          refine ⟨2253430867631968950089089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3004574490175958600118785 2253430867631968950089089)
          ·
            refine ⟨1690073150723976712566817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253430867631968950089089 1690073150723976712566817)
            ·
              refine ⟨1267554863042982534425113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690073150723976712566817 1267554863042982534425113)
              ·
                refine ⟨950666147282236900818835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267554863042982534425113 950666147282236900818835)
                ·
                  refine ⟨1425999220923355351228253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950666147282236900818835 1425999220923355351228253)
                  ·
                    refine ⟨534749707846258256710595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425999220923355351228253 534749707846258256710595)
                    ·
                      rfl

theorem cell22_1562132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1562132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562132 prefixEnd_1562132 := by exact prefixLift 1562132
  have htrace : WordTrace (prefixWord ++ tailWord_1562132) baseStart_1562132 baseEnd_1562132 := by
    simpa [prefixWord, tailWord_1562132, baseEnd_1562132] using wordTrace_append hprefix tailTrace_1562132
  have hstable : (prefixWord ++ tailWord_1562132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562132).length < 2 ^ (prefixWord ++ tailWord_1562132).sum := by decide
  have hdescent : baseEnd_1562132 < baseStart_1562132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562154 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1562154 : Nat := 118140960795 + 1562154 * 2 ^ 59
def prefixEnd_1562154 : Nat := 4983230072969 + 3 ^ 40 * 1562154 * 2
def baseEnd_1562154 : Nat := 534757238895857532660527

theorem tailTrace_1562154 : CollatzResearch.WordTrace tailWord_1562154 prefixEnd_1562154 534757238895857532660527 := by
  unfold tailWord_1562154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14244109295647581876925379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37984291455060218338467677 14244109295647581876925379)
  ·
    refine ⟨21366163943471372815388069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14244109295647581876925379 21366163943471372815388069)
    ·
      refine ⟨4006155739400882402885263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21366163943471372815388069 4006155739400882402885263)
      ·
        refine ⟨6009233609101323604327895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006155739400882402885263 6009233609101323604327895)
        ·
          refine ⟨9013850413651985406491843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009233609101323604327895 9013850413651985406491843)
          ·
            refine ⟨13520775620477978109737765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9013850413651985406491843 13520775620477978109737765)
            ·
              refine ⟨2535145428839620895575831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13520775620477978109737765 2535145428839620895575831)
              ·
                refine ⟨3802718143259431343363747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535145428839620895575831 3802718143259431343363747)
                ·
                  refine ⟨5704077214889147015045621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802718143259431343363747 5704077214889147015045621)
                  ·
                    refine ⟨534757238895857532660527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5704077214889147015045621 534757238895857532660527)
                    ·
                      rfl

theorem cell22_1562154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1562154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562154 prefixEnd_1562154 := by exact prefixLift 1562154
  have htrace : WordTrace (prefixWord ++ tailWord_1562154) baseStart_1562154 baseEnd_1562154 := by
    simpa [prefixWord, tailWord_1562154, baseEnd_1562154] using wordTrace_append hprefix tailTrace_1562154
  have hstable : (prefixWord ++ tailWord_1562154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562154).length < 2 ^ (prefixWord ++ tailWord_1562154).sum := by decide
  have hdescent : baseEnd_1562154 < baseStart_1562154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562169 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_1562169 : Nat := 118140960795 + 1562169 * 2 ^ 59
def prefixEnd_1562169 : Nat := 4983230072969 + 3 ^ 40 * 1562169 * 2
def baseEnd_1562169 : Nat := 534762373702402493535481

theorem tailTrace_1562169 : CollatzResearch.WordTrace tailWord_1562169 prefixEnd_1562169 534762373702402493535481 := by
  unfold tailWord_1562169
  simp only [CollatzResearch.WordTrace]
  refine ⟨56976984277535985069497561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37984656185023990046331707 56976984277535985069497561)
  ·
    refine ⟨42732738208151988802123171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56976984277535985069497561 42732738208151988802123171)
    ·
      refine ⟨64099107312227983203184757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42732738208151988802123171 64099107312227983203184757)
      ·
        refine ⟨6009291310521373425298571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64099107312227983203184757 6009291310521373425298571)
        ·
          refine ⟨9013936965782060137947857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009291310521373425298571 9013936965782060137947857)
          ·
            refine ⟨6760452724336545103460893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013936965782060137947857 6760452724336545103460893)
            ·
              refine ⟨2535169771626204413797835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760452724336545103460893 2535169771626204413797835)
              ·
                refine ⟨3802754657439306620696753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535169771626204413797835 3802754657439306620696753)
                ·
                  refine ⟨2852065993079479965522565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802754657439306620696753 2852065993079479965522565)
                  ·
                    refine ⟨534762373702402493535481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852065993079479965522565 534762373702402493535481)
                    ·
                      rfl

theorem cell22_1562169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_1562169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562169 prefixEnd_1562169 := by exact prefixLift 1562169
  have htrace : WordTrace (prefixWord ++ tailWord_1562169) baseStart_1562169 baseEnd_1562169 := by
    simpa [prefixWord, tailWord_1562169, baseEnd_1562169] using wordTrace_append hprefix tailTrace_1562169
  have hstable : (prefixWord ++ tailWord_1562169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562169).length < 2 ^ (prefixWord ++ tailWord_1562169).sum := by decide
  have hdescent : baseEnd_1562169 < baseStart_1562169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562199 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 3, 3]
def baseStart_1562199 : Nat := 118140960795 + 1562199 * 2 ^ 59
def prefixEnd_1562199 : Nat := 4983230072969 + 3 ^ 40 * 1562199 * 2
def baseEnd_1562199 : Nat := 534772643315492415285389

theorem tailTrace_1562199 : CollatzResearch.WordTrace tailWord_1562199 prefixEnd_1562199 534772643315492415285389 := by
  unfold tailWord_1562199
  simp only [CollatzResearch.WordTrace]
  refine ⟨56978078467427300193089651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37985385644951533462059767 56978078467427300193089651)
  ·
    refine ⟨85467117701140950289634477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56978078467427300193089651 85467117701140950289634477)
    ·
      refine ⟨32050169137927856358612929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85467117701140950289634477 32050169137927856358612929)
      ·
        refine ⟨24037626853445892268959697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32050169137927856358612929 24037626853445892268959697)
        ·
          refine ⟨18028220140084419201719773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24037626853445892268959697 18028220140084419201719773)
          ·
            refine ⟨6760582552531657200644915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18028220140084419201719773 6760582552531657200644915)
            ·
              refine ⟨10140873828797485800967373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760582552531657200644915 10140873828797485800967373)
              ·
                refine ⟨3802827685799057175362765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10140873828797485800967373 3802827685799057175362765)
                ·
                  refine ⟨1426060382174646440761037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3802827685799057175362765 1426060382174646440761037)
                  ·
                    refine ⟨534772643315492415285389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426060382174646440761037 534772643315492415285389)
                    ·
                      rfl

theorem cell22_1562199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_1562199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562199 prefixEnd_1562199 := by exact prefixLift 1562199
  have htrace : WordTrace (prefixWord ++ tailWord_1562199) baseStart_1562199 baseEnd_1562199 := by
    simpa [prefixWord, tailWord_1562199, baseEnd_1562199] using wordTrace_append hprefix tailTrace_1562199
  have hstable : (prefixWord ++ tailWord_1562199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562199).length < 2 ^ (prefixWord ++ tailWord_1562199).sum := by decide
  have hdescent : baseEnd_1562199 < baseStart_1562199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562205 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1562205 : Nat := 118140960795 + 1562205 * 2 ^ 59
def prefixEnd_1562205 : Nat := 4983230072969 + 3 ^ 40 * 1562205 * 2
def baseEnd_1562205 : Nat := 534774697238110399635371

theorem tailTrace_1562205 : CollatzResearch.WordTrace tailWord_1562205 prefixEnd_1562205 534774697238110399635371 := by
  unfold tailWord_1562205
  simp only [CollatzResearch.WordTrace]
  refine ⟨56978297305405563217808069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37985531536937042145205379 56978297305405563217808069)
  ·
    refine ⟨10683430744763543103339013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56978297305405563217808069 10683430744763543103339013)
    ·
      refine ⟨2003143264643164331876065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10683430744763543103339013 2003143264643164331876065)
      ·
        refine ⟨1502357448482373248907049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2003143264643164331876065 1502357448482373248907049)
        ·
          refine ⟨1126768086361779936680287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502357448482373248907049 1126768086361779936680287)
          ·
            refine ⟨1690152129542669905020431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126768086361779936680287 1690152129542669905020431)
            ·
              refine ⟨2535228194314004857530647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690152129542669905020431 2535228194314004857530647)
              ·
                refine ⟨3802842291471007286295971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535228194314004857530647 3802842291471007286295971)
                ·
                  refine ⟨5704263437206510929443957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802842291471007286295971 5704263437206510929443957)
                  ·
                    refine ⟨534774697238110399635371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5704263437206510929443957 534774697238110399635371)
                    ·
                      rfl

theorem cell22_1562205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1562205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562205 prefixEnd_1562205 := by exact prefixLift 1562205
  have htrace : WordTrace (prefixWord ++ tailWord_1562205) baseStart_1562205 baseEnd_1562205 := by
    simpa [prefixWord, tailWord_1562205, baseEnd_1562205] using wordTrace_append hprefix tailTrace_1562205
  have hstable : (prefixWord ++ tailWord_1562205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562205).length < 2 ^ (prefixWord ++ tailWord_1562205).sum := by decide
  have hdescent : baseEnd_1562205 < baseStart_1562205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562216 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1562216 : Nat := 118140960795 + 1562216 * 2 ^ 59
def prefixEnd_1562216 : Nat := 4983230072969 + 3 ^ 40 * 1562216 * 2
def baseEnd_1562216 : Nat := 534778462762910037610337

theorem tailTrace_1562216 : CollatzResearch.WordTrace tailWord_1562216 prefixEnd_1562216 534778462762910037610337 := by
  unfold tailWord_1562216
  simp only [CollatzResearch.WordTrace]
  refine ⟨28489349254182856048229251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37985799005577141397639001 28489349254182856048229251)
  ·
    refine ⟨42734023881274284072343877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28489349254182856048229251 42734023881274284072343877)
    ·
      refine ⟨8012629477738928263564477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42734023881274284072343877 8012629477738928263564477)
      ·
        refine ⟨3004736054152098098836679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8012629477738928263564477 3004736054152098098836679)
        ·
          refine ⟨4507104081228147148255019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004736054152098098836679 4507104081228147148255019)
          ·
            refine ⟨6760656121842220722382529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507104081228147148255019 6760656121842220722382529)
            ·
              refine ⟨5070492091381665541786897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6760656121842220722382529 5070492091381665541786897)
              ·
                refine ⟨3802869068536249156340173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5070492091381665541786897 3802869068536249156340173)
                ·
                  refine ⟨1426075900701093433627565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3802869068536249156340173 1426075900701093433627565)
                  ·
                    refine ⟨534778462762910037610337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426075900701093433627565 534778462762910037610337)
                    ·
                      rfl

theorem cell22_1562216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1562216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562216 prefixEnd_1562216 := by exact prefixLift 1562216
  have htrace : WordTrace (prefixWord ++ tailWord_1562216) baseStart_1562216 baseEnd_1562216 := by
    simpa [prefixWord, tailWord_1562216, baseEnd_1562216] using wordTrace_append hprefix tailTrace_1562216
  have hstable : (prefixWord ++ tailWord_1562216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562216).length < 2 ^ (prefixWord ++ tailWord_1562216).sum := by decide
  have hdescent : baseEnd_1562216 < baseStart_1562216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562229 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 7]
def baseStart_1562229 : Nat := 118140960795 + 1562229 * 2 ^ 59
def prefixEnd_1562229 : Nat := 4983230072969 + 3 ^ 40 * 1562229 * 2
def baseEnd_1562229 : Nat := 178260970976194112345099

theorem tailTrace_1562229 : CollatzResearch.WordTrace tailWord_1562229 prefixEnd_1562229 178260970976194112345099 := by
  unfold tailWord_1562229
  simp only [CollatzResearch.WordTrace]
  refine ⟨56979172657318615316681741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37986115104879076877787827 56979172657318615316681741)
  ·
    refine ⟨21367189746494480743755653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56979172657318615316681741 21367189746494480743755653)
    ·
      refine ⟨4006348077467715139454185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21367189746494480743755653 4006348077467715139454185)
      ·
        refine ⟨3004761058100786354590639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4006348077467715139454185 3004761058100786354590639)
        ·
          refine ⟨4507141587151179531885959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004761058100786354590639 4507141587151179531885959)
          ·
            refine ⟨6760712380726769297828939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507141587151179531885959 6760712380726769297828939)
            ·
              refine ⟨10141068571090153946743409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760712380726769297828939 10141068571090153946743409)
              ·
                refine ⟨7605801428317615460057557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10141068571090153946743409 7605801428317615460057557)
                ·
                  refine ⟨178260970976194112345099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7605801428317615460057557 178260970976194112345099)
                  ·
                    rfl

theorem cell22_1562229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_1562229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562229 prefixEnd_1562229 := by exact prefixLift 1562229
  have htrace : WordTrace (prefixWord ++ tailWord_1562229) baseStart_1562229 baseEnd_1562229 := by
    simpa [prefixWord, tailWord_1562229, baseEnd_1562229] using wordTrace_append hprefix tailTrace_1562229
  have hstable : (prefixWord ++ tailWord_1562229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562229).length < 2 ^ (prefixWord ++ tailWord_1562229).sum := by decide
  have hdescent : baseEnd_1562229 < baseStart_1562229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562250 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1562250 : Nat := 118140960795 + 1562250 * 2 ^ 59
def prefixEnd_1562250 : Nat := 4983230072969 + 3 ^ 40 * 1562250 * 2
def baseEnd_1562250 : Nat := 534790101657745282260233

theorem tailTrace_1562250 : CollatzResearch.WordTrace tailWord_1562250 prefixEnd_1562250 534790101657745282260233 := by
  unfold tailWord_1562250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14244984647560633975799051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37986625726828357268797469 14244984647560633975799051)
  ·
    refine ⟨21367476971340950963698577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14244984647560633975799051 21367476971340950963698577)
    ·
      refine ⟨16025607728505713222773933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21367476971340950963698577 16025607728505713222773933)
      ·
        refine ⟨6009602898189642458540225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16025607728505713222773933 6009602898189642458540225)
        ·
          refine ⟨4507202173642231843905169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6009602898189642458540225 4507202173642231843905169)
          ·
            refine ⟨3380401630231673882928877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4507202173642231843905169 3380401630231673882928877)
            ·
              refine ⟨1267650611336877706098329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3380401630231673882928877 1267650611336877706098329)
              ·
                refine ⟨950737958502658279573747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267650611336877706098329 950737958502658279573747)
                ·
                  refine ⟨1426106937753987419360621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950737958502658279573747 1426106937753987419360621)
                  ·
                    refine ⟨534790101657745282260233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426106937753987419360621 534790101657745282260233)
                    ·
                      rfl

theorem cell22_1562250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1562250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562250 prefixEnd_1562250 := by exact prefixLift 1562250
  have htrace : WordTrace (prefixWord ++ tailWord_1562250) baseStart_1562250 baseEnd_1562250 := by
    simpa [prefixWord, tailWord_1562250, baseEnd_1562250] using wordTrace_append hprefix tailTrace_1562250
  have hstable : (prefixWord ++ tailWord_1562250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562250).length < 2 ^ (prefixWord ++ tailWord_1562250).sum := by decide
  have hdescent : baseEnd_1562250 < baseStart_1562250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562257 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 6]
def baseStart_1562257 : Nat := 118140960795 + 1562257 * 2 ^ 59
def prefixEnd_1562257 : Nat := 4983230072969 + 3 ^ 40 * 1562257 * 2
def baseEnd_1562257 : Nat := 178264165966933199111737

theorem tailTrace_1562257 : CollatzResearch.WordTrace tailWord_1562257 prefixEnd_1562257 178264165966933199111737 := by
  unfold tailWord_1562257
  simp only [CollatzResearch.WordTrace]
  refine ⟨56980193901217176098701025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37986795934144784065800683 56980193901217176098701025)
  ·
    refine ⟨42735145425912882074025769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56980193901217176098701025 42735145425912882074025769)
    ·
      refine ⟨32051359069434661555519327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42735145425912882074025769 32051359069434661555519327)
      ·
        refine ⟨48077038604151992333278991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32051359069434661555519327 48077038604151992333278991)
        ·
          refine ⟨72115557906227988499918487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48077038604151992333278991 72115557906227988499918487)
          ·
            refine ⟨108173336859341982749877731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72115557906227988499918487 108173336859341982749877731)
            ·
              refine ⟨162260005289012974124816597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108173336859341982749877731 162260005289012974124816597)
              ·
                refine ⟨3802968873961241581050389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 162260005289012974124816597 3802968873961241581050389)
                ·
                  refine ⟨178264165966933199111737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3802968873961241581050389 178264165966933199111737)
                  ·
                    rfl

theorem cell22_1562257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_1562257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562257 prefixEnd_1562257 := by exact prefixLift 1562257
  have htrace : WordTrace (prefixWord ++ tailWord_1562257) baseStart_1562257 baseEnd_1562257 := by
    simpa [prefixWord, tailWord_1562257, baseEnd_1562257] using wordTrace_append hprefix tailTrace_1562257
  have hstable : (prefixWord ++ tailWord_1562257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562257).length < 2 ^ (prefixWord ++ tailWord_1562257).sum := by decide
  have hdescent : baseEnd_1562257 < baseStart_1562257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562276 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1562276 : Nat := 118140960795 + 1562276 * 2 ^ 59
def prefixEnd_1562276 : Nat := 4983230072969 + 3 ^ 40 * 1562276 * 2
def baseEnd_1562276 : Nat := 534799001989089881110153

theorem tailTrace_1562276 : CollatzResearch.WordTrace tailWord_1562276 prefixEnd_1562276 534799001989089881110153 := by
  unfold tailWord_1562276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490443444074171171821341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37987257925432228229095121 28490443444074171171821341)
  ·
    refine ⟨10683916291527814189433003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28490443444074171171821341 10683916291527814189433003)
    ·
      refine ⟨16025874437291721284149505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683916291527814189433003 16025874437291721284149505)
      ·
        refine ⟨12019405827968790963112129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16025874437291721284149505 12019405827968790963112129)
        ·
          refine ⟨9014554370976593222334097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12019405827968790963112129 9014554370976593222334097)
          ·
            refine ⟨6760915778232444916750573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014554370976593222334097 6760915778232444916750573)
            ·
              refine ⟨2535343416837166843781465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760915778232444916750573 2535343416837166843781465)
              ·
                refine ⟨1901507562627875132836099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535343416837166843781465 1901507562627875132836099)
                ·
                  refine ⟨2852261343941812699254149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901507562627875132836099 2852261343941812699254149)
                  ·
                    refine ⟨534799001989089881110153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852261343941812699254149 534799001989089881110153)
                    ·
                      rfl

theorem cell22_1562276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1562276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562276 prefixEnd_1562276 := by exact prefixLift 1562276
  have htrace : WordTrace (prefixWord ++ tailWord_1562276) baseStart_1562276 baseEnd_1562276 := by
    simpa [prefixWord, tailWord_1562276, baseEnd_1562276] using wordTrace_append hprefix tailTrace_1562276
  have hstable : (prefixWord ++ tailWord_1562276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562276).length < 2 ^ (prefixWord ++ tailWord_1562276).sum := by decide
  have hdescent : baseEnd_1562276 < baseStart_1562276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562304 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_1562304 : Nat := 118140960795 + 1562304 * 2 ^ 59
def prefixEnd_1562304 : Nat := 4983230072969 + 3 ^ 40 * 1562304 * 2
def baseEnd_1562304 : Nat := 534808586961307141410067

theorem tailTrace_1562304 : CollatzResearch.WordTrace tailWord_1562304 prefixEnd_1562304 534808586961307141410067 := by
  unfold tailWord_1562304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490954066023451562830983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37987938754697935417107977 28490954066023451562830983)
  ·
    refine ⟨42736431099035177344246475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28490954066023451562830983 42736431099035177344246475)
    ·
      refine ⟨64104646648552766016369713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42736431099035177344246475 64104646648552766016369713)
      ·
        refine ⟨48078484986414574512277285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64104646648552766016369713 48078484986414574512277285)
        ·
          refine ⟨9014715934952732721051991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48078484986414574512277285 9014715934952732721051991)
          ·
            refine ⟨13522073902429099081577987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9014715934952732721051991 13522073902429099081577987)
            ·
              refine ⟨20283110853643648622366981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13522073902429099081577987 20283110853643648622366981)
              ·
                refine ⟨3803083285058184116693809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20283110853643648622366981 3803083285058184116693809)
                ·
                  refine ⟨2852312463793638087520357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803083285058184116693809 2852312463793638087520357)
                  ·
                    refine ⟨534808586961307141410067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852312463793638087520357 534808586961307141410067)
                    ·
                      rfl

theorem cell22_1562304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_1562304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562304 prefixEnd_1562304 := by exact prefixLift 1562304
  have htrace : WordTrace (prefixWord ++ tailWord_1562304) baseStart_1562304 baseEnd_1562304 := by
    simpa [prefixWord, tailWord_1562304, baseEnd_1562304] using wordTrace_append hprefix tailTrace_1562304
  have hstable : (prefixWord ++ tailWord_1562304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562304).length < 2 ^ (prefixWord ++ tailWord_1562304).sum := by decide
  have hdescent : baseEnd_1562304 < baseStart_1562304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562364 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_1562364 : Nat := 118140960795 + 1562364 * 2 ^ 59
def prefixEnd_1562364 : Nat := 4983230072969 + 3 ^ 40 * 1562364 * 2
def baseEnd_1562364 : Nat := 178276375395828994969961

theorem tailTrace_1562364 : CollatzResearch.WordTrace tailWord_1562364 prefixEnd_1562364 178276375395828994969961 := by
  unfold tailWord_1562364
  simp only [CollatzResearch.WordTrace]
  refine ⟨28492048255914766686423073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37989397674553022248564097 28492048255914766686423073)
  ·
    refine ⟨21369036191936075014817305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28492048255914766686423073 21369036191936075014817305)
    ·
      refine ⟨16026777143952056261112979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21369036191936075014817305 16026777143952056261112979)
      ·
        refine ⟨24040165715928084391669469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16026777143952056261112979 24040165715928084391669469)
        ·
          refine ⟨9015062143473031646876051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24040165715928084391669469 9015062143473031646876051)
          ·
            refine ⟨13522593215209547470314077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015062143473031646876051 13522593215209547470314077)
            ·
              refine ⟨5070972455703580301367779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13522593215209547470314077 5070972455703580301367779)
              ·
                refine ⟨7606458683555370452051669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070972455703580301367779 7606458683555370452051669)
                ·
                  refine ⟨178276375395828994969961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7606458683555370452051669 178276375395828994969961)
                  ·
                    rfl

theorem cell22_1562364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_1562364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562364 prefixEnd_1562364 := by exact prefixLift 1562364
  have htrace : WordTrace (prefixWord ++ tailWord_1562364) baseStart_1562364 baseEnd_1562364 := by
    simpa [prefixWord, tailWord_1562364, baseEnd_1562364] using wordTrace_append hprefix tailTrace_1562364
  have hstable : (prefixWord ++ tailWord_1562364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562364).length < 2 ^ (prefixWord ++ tailWord_1562364).sum := by decide
  have hdescent : baseEnd_1562364 < baseStart_1562364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562379 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 2, 5]
def baseStart_1562379 : Nat := 118140960795 + 1562379 * 2 ^ 59
def prefixEnd_1562379 : Nat := 4983230072969 + 3 ^ 40 * 1562379 * 2
def baseEnd_1562379 : Nat := 534834260994031945784837

theorem tailTrace_1562379 : CollatzResearch.WordTrace tailWord_1562379 prefixEnd_1562379 534834260994031945784837 := by
  unfold tailWord_1562379
  simp only [CollatzResearch.WordTrace]
  refine ⟨56984643606775190934642191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37989762404516793956428127 56984643606775190934642191)
  ·
    refine ⟨85476965410162786401963287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56984643606775190934642191 85476965410162786401963287)
    ·
      refine ⟨128215448115244179602944931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85476965410162786401963287 128215448115244179602944931)
      ·
        refine ⟨192323172172866269404417397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128215448115244179602944931 192323172172866269404417397)
        ·
          refine ⟨18030297391206212756664131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192323172172866269404417397 18030297391206212756664131)
          ·
            refine ⟨27045446086809319134996197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18030297391206212756664131 27045446086809319134996197)
            ·
              refine ⟨5071021141276747337811787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27045446086809319134996197 5071021141276747337811787)
              ·
                refine ⟨7606531711915121006717681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071021141276747337811787 7606531711915121006717681)
                ·
                  refine ⟨5704898783936340755038261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606531711915121006717681 5704898783936340755038261)
                  ·
                    refine ⟨534834260994031945784837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5704898783936340755038261 534834260994031945784837)
                    ·
                      rfl

theorem cell22_1562379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_1562379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562379 prefixEnd_1562379 := by exact prefixLift 1562379
  have htrace : WordTrace (prefixWord ++ tailWord_1562379) baseStart_1562379 baseEnd_1562379 := by
    simpa [prefixWord, tailWord_1562379, baseEnd_1562379] using wordTrace_append hprefix tailTrace_1562379
  have hstable : (prefixWord ++ tailWord_1562379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562379).length < 2 ^ (prefixWord ++ tailWord_1562379).sum := by decide
  have hdescent : baseEnd_1562379 < baseStart_1562379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562426 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_1562426 : Nat := 118140960795 + 1562426 * 2 ^ 59
def prefixEnd_1562426 : Nat := 4983230072969 + 3 ^ 40 * 1562426 * 2
def baseEnd_1562426 : Nat := 178283450018179829953231

theorem tailTrace_1562426 : CollatzResearch.WordTrace tailWord_1562426 prefixEnd_1562426 178283450018179829953231 := by
  unfold tailWord_1562426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246589459401229490400783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37990905225069945307735421 14246589459401229490400783)
  ·
    refine ⟨21369884189101844235601175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14246589459401229490400783 21369884189101844235601175)
    ·
      refine ⟨32054826283652766353401763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21369884189101844235601175 32054826283652766353401763)
      ·
        refine ⟨48082239425479149530102645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32054826283652766353401763 48082239425479149530102645)
        ·
          refine ⟨4507709946138670268447123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48082239425479149530102645 4507709946138670268447123)
          ·
            refine ⟨6761564919208005402670685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507709946138670268447123 6761564919208005402670685)
            ·
              refine ⟨2535586844703002026001507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6761564919208005402670685 2535586844703002026001507)
              ·
                refine ⟨3803380267054503039002261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535586844703002026001507 3803380267054503039002261)
                ·
                  refine ⟨178283450018179829953231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3803380267054503039002261 178283450018179829953231)
                  ·
                    rfl

theorem cell22_1562426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_1562426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562426 prefixEnd_1562426 := by exact prefixLift 1562426
  have htrace : WordTrace (prefixWord ++ tailWord_1562426) baseStart_1562426 baseEnd_1562426 := by
    simpa [prefixWord, tailWord_1562426, baseEnd_1562426] using wordTrace_append hprefix tailTrace_1562426
  have hstable : (prefixWord ++ tailWord_1562426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562426).length < 2 ^ (prefixWord ++ tailWord_1562426).sum := by decide
  have hdescent : baseEnd_1562426 < baseStart_1562426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562439 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1562439 : Nat := 118140960795 + 1562439 * 2 ^ 59
def prefixEnd_1562439 : Nat := 4983230072969 + 3 ^ 40 * 1562439 * 2
def baseEnd_1562439 : Nat := 534854800220211789284653

theorem tailTrace_1562439 : CollatzResearch.WordTrace tailWord_1562439 prefixEnd_1562439 534854800220211789284653 := by
  unfold tailWord_1562439
  simp only [CollatzResearch.WordTrace]
  refine ⟨56986831986557821181826371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37991221324371880787884247 56986831986557821181826371)
  ·
    refine ⟨85480247979836731772739557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56986831986557821181826371 85480247979836731772739557)
    ·
      refine ⟨16027546496219387207388667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85480247979836731772739557 16027546496219387207388667)
      ·
        refine ⟨24041319744329080811083001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16027546496219387207388667 24041319744329080811083001)
        ·
          refine ⟨18030989808246810608312251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24041319744329080811083001 18030989808246810608312251)
          ·
            refine ⟨27046484712370215912468377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18030989808246810608312251 27046484712370215912468377)
            ·
              refine ⟨20284863534277661934351283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27046484712370215912468377 20284863534277661934351283)
              ·
                refine ⟨30427295301416492901526925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20284863534277661934351283 30427295301416492901526925)
                ·
                  refine ⟨11410235738031184838072597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30427295301416492901526925 11410235738031184838072597)
                  ·
                    refine ⟨534854800220211789284653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11410235738031184838072597 534854800220211789284653)
                    ·
                      rfl

theorem cell22_1562439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1562439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562439 prefixEnd_1562439 := by exact prefixLift 1562439
  have htrace : WordTrace (prefixWord ++ tailWord_1562439) baseStart_1562439 baseEnd_1562439 := by
    simpa [prefixWord, tailWord_1562439, baseEnd_1562439] using wordTrace_append hprefix tailTrace_1562439
  have hstable : (prefixWord ++ tailWord_1562439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562439).length < 2 ^ (prefixWord ++ tailWord_1562439).sum := by decide
  have hdescent : baseEnd_1562439 < baseStart_1562439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562445 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1562445 : Nat := 118140960795 + 1562445 * 2 ^ 59
def prefixEnd_1562445 : Nat := 4983230072969 + 3 ^ 40 * 1562445 * 2
def baseEnd_1562445 : Nat := 534856854142829773634635

theorem tailTrace_1562445 : CollatzResearch.WordTrace tailWord_1562445 prefixEnd_1562445 534856854142829773634635 := by
  unfold tailWord_1562445
  simp only [CollatzResearch.WordTrace]
  refine ⟨56987050824536084206544789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37991367216357389471029859 56987050824536084206544789)
  ·
    refine ⟨2671268007400128947181787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56987050824536084206544789 2671268007400128947181787)
    ·
      refine ⟨4006902011100193420772681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671268007400128947181787 4006902011100193420772681)
      ·
        refine ⟨3005176508325145065579511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4006902011100193420772681 3005176508325145065579511)
        ·
          refine ⟨4507764762487717598369267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005176508325145065579511 4507764762487717598369267)
          ·
            refine ⟨6761647143731576397553901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507764762487717598369267 6761647143731576397553901)
            ·
              refine ⟨2535617678899341149082713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6761647143731576397553901 2535617678899341149082713)
              ·
                refine ⟨1901713259174505861812035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535617678899341149082713 1901713259174505861812035)
                ·
                  refine ⟨2852569888761758792718053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901713259174505861812035 2852569888761758792718053)
                  ·
                    refine ⟨534856854142829773634635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852569888761758792718053 534856854142829773634635)
                    ·
                      rfl

theorem cell22_1562445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1562445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562445 prefixEnd_1562445 := by exact prefixLift 1562445
  have htrace : WordTrace (prefixWord ++ tailWord_1562445) baseStart_1562445 baseEnd_1562445 := by
    simpa [prefixWord, tailWord_1562445, baseEnd_1562445] using wordTrace_append hprefix tailTrace_1562445
  have hstable : (prefixWord ++ tailWord_1562445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562445).length < 2 ^ (prefixWord ++ tailWord_1562445).sum := by decide
  have hdescent : baseEnd_1562445 < baseStart_1562445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562526 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1562526 : Nat := 118140960795 + 1562526 * 2 ^ 59
def prefixEnd_1562526 : Nat := 4983230072969 + 3 ^ 40 * 1562526 * 2
def baseEnd_1562526 : Nat := 534884582098172562359387

theorem tailTrace_1562526 : CollatzResearch.WordTrace tailWord_1562526 prefixEnd_1562526 534884582098172562359387 := by
  unfold tailWord_1562526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123750642155329380030429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37993336758161756693495621 7123750642155329380030429)
  ·
    refine ⟨2671406490808248517511411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7123750642155329380030429 2671406490808248517511411)
    ·
      refine ⟨4007109736212372776267117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671406490808248517511411 4007109736212372776267117)
      ·
        refine ⟨1502666151079639791100169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4007109736212372776267117 1502666151079639791100169)
        ·
          refine ⟨1126999613309729843325127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502666151079639791100169 1126999613309729843325127)
          ·
            refine ⟨1690499419964594764987691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126999613309729843325127 1690499419964594764987691)
            ·
              refine ⟨2535749129946892147481537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690499419964594764987691 2535749129946892147481537)
              ·
                refine ⟨1901811847460169110611153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535749129946892147481537 1901811847460169110611153)
                ·
                  refine ⟨1426358885595126832958365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901811847460169110611153 1426358885595126832958365)
                  ·
                    refine ⟨534884582098172562359387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426358885595126832958365 534884582098172562359387)
                    ·
                      rfl

theorem cell22_1562526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1562526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562526 prefixEnd_1562526 := by exact prefixLift 1562526
  have htrace : WordTrace (prefixWord ++ tailWord_1562526) baseStart_1562526 baseEnd_1562526 := by
    simpa [prefixWord, tailWord_1562526, baseEnd_1562526] using wordTrace_append hprefix tailTrace_1562526
  have hstable : (prefixWord ++ tailWord_1562526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562526).length < 2 ^ (prefixWord ++ tailWord_1562526).sum := by decide
  have hdescent : baseEnd_1562526 < baseStart_1562526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562546 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1562546 : Nat := 118140960795 + 1562546 * 2 ^ 59
def prefixEnd_1562546 : Nat := 4983230072969 + 3 ^ 40 * 1562546 * 2
def baseEnd_1562546 : Nat := 534891428506899176859325

theorem tailTrace_1562546 : CollatzResearch.WordTrace tailWord_1562546 prefixEnd_1562546 534891428506899176859325 := by
  unfold tailWord_1562546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14247683649292544613992873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37993823064780118970647661 14247683649292544613992873)
  ·
    refine ⟨10685762736969408460494655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14247683649292544613992873 10685762736969408460494655)
    ·
      refine ⟨16028644105454112690741983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10685762736969408460494655 16028644105454112690741983)
      ·
        refine ⟨24042966158181169036112975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16028644105454112690741983 24042966158181169036112975)
        ·
          refine ⟨36064449237271753554169463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24042966158181169036112975 36064449237271753554169463)
          ·
            refine ⟨54096673855907630331254195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36064449237271753554169463 54096673855907630331254195)
            ·
              refine ⟨81145010783861445496881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54096673855907630331254195 81145010783861445496881293)
              ·
                refine ⟨30429379043948042061330485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81145010783861445496881293 30429379043948042061330485)
                ·
                  refine ⟨2852754285370128943249733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30429379043948042061330485 2852754285370128943249733)
                  ·
                    refine ⟨534891428506899176859325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852754285370128943249733 534891428506899176859325)
                    ·
                      rfl

theorem cell22_1562546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1562546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562546 prefixEnd_1562546 := by exact prefixLift 1562546
  have htrace : WordTrace (prefixWord ++ tailWord_1562546) baseStart_1562546 baseEnd_1562546 := by
    simpa [prefixWord, tailWord_1562546, baseEnd_1562546] using wordTrace_append hprefix tailTrace_1562546
  have hstable : (prefixWord ++ tailWord_1562546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562546).length < 2 ^ (prefixWord ++ tailWord_1562546).sum := by decide
  have hdescent : baseEnd_1562546 < baseStart_1562546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562576 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_1562576 : Nat := 118140960795 + 1562576 * 2 ^ 59
def prefixEnd_1562576 : Nat := 4983230072969 + 3 ^ 40 * 1562576 * 2
def baseEnd_1562576 : Nat := 534901698119989098609233

theorem tailTrace_1562576 : CollatzResearch.WordTrace tailWord_1562576 prefixEnd_1562576 534901698119989098609233 := by
  unfold tailWord_1562576
  simp only [CollatzResearch.WordTrace]
  refine ⟨28495914393530746789781791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37994552524707662386375721 28495914393530746789781791)
  ·
    refine ⟨42743871590296120184672687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28495914393530746789781791 42743871590296120184672687)
    ·
      refine ⟨64115807385444180277009031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42743871590296120184672687 64115807385444180277009031)
      ·
        refine ⟨96173711078166270415513547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64115807385444180277009031 96173711078166270415513547)
        ·
          refine ⟨144260566617249405623270321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96173711078166270415513547 144260566617249405623270321)
          ·
            refine ⟨108195424962937054217452741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144260566617249405623270321 108195424962937054217452741)
            ·
              refine ⟨20286642180550697665772389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108195424962937054217452741 20286642180550697665772389)
              ·
                refine ⟨3803745408853255812332323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20286642180550697665772389 3803745408853255812332323)
                ·
                  refine ⟨5705618113279883718498485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803745408853255812332323 5705618113279883718498485)
                  ·
                    refine ⟨534901698119989098609233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5705618113279883718498485 534901698119989098609233)
                    ·
                      rfl

theorem cell22_1562576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_1562576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562576 prefixEnd_1562576 := by exact prefixLift 1562576
  have htrace : WordTrace (prefixWord ++ tailWord_1562576) baseStart_1562576 baseEnd_1562576 := by
    simpa [prefixWord, tailWord_1562576, baseEnd_1562576] using wordTrace_append hprefix tailTrace_1562576
  have hstable : (prefixWord ++ tailWord_1562576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562576).length < 2 ^ (prefixWord ++ tailWord_1562576).sum := by decide
  have hdescent : baseEnd_1562576 < baseStart_1562576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562588 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1562588 : Nat := 118140960795 + 1562588 * 2 ^ 59
def prefixEnd_1562588 : Nat := 4983230072969 + 3 ^ 40 * 1562588 * 2
def baseEnd_1562588 : Nat := 534905805965225067309197

theorem tailTrace_1562588 : CollatzResearch.WordTrace tailWord_1562588 prefixEnd_1562588 534905805965225067309197 := by
  unfold tailWord_1562588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28496133231509009814500209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37994844308678679752666945 28496133231509009814500209)
  ·
    refine ⟨21372099923631757360875157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28496133231509009814500209 21372099923631757360875157)
    ·
      refine ⟨1001817183920238626291023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21372099923631757360875157 1001817183920238626291023)
      ·
        refine ⟨1502725775880357939436535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001817183920238626291023 1502725775880357939436535)
        ·
          refine ⟨2254088663820536909154803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502725775880357939436535 2254088663820536909154803)
          ·
            refine ⟨3381132995730805363732205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254088663820536909154803 3381132995730805363732205)
            ·
              refine ⟨1267924873399052011399577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3381132995730805363732205 1267924873399052011399577)
              ·
                refine ⟨950943655049289008549683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267924873399052011399577 950943655049289008549683)
                ·
                  refine ⟨1426415482573933512824525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950943655049289008549683 1426415482573933512824525)
                  ·
                    refine ⟨534905805965225067309197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426415482573933512824525 534905805965225067309197)
                    ·
                      rfl

theorem cell22_1562588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1562588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562588 prefixEnd_1562588 := by exact prefixLift 1562588
  have htrace : WordTrace (prefixWord ++ tailWord_1562588) baseStart_1562588 baseEnd_1562588 := by
    simpa [prefixWord, tailWord_1562588, baseEnd_1562588] using wordTrace_append hprefix tailTrace_1562588
  have hstable : (prefixWord ++ tailWord_1562588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562588).length < 2 ^ (prefixWord ++ tailWord_1562588).sum := by decide
  have hdescent : baseEnd_1562588 < baseStart_1562588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562593 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_1562593 : Nat := 118140960795 + 1562593 * 2 ^ 59
def prefixEnd_1562593 : Nat := 4983230072969 + 3 ^ 40 * 1562593 * 2
def baseEnd_1562593 : Nat := 534907517567406720934181

theorem tailTrace_1562593 : CollatzResearch.WordTrace tailWord_1562593 prefixEnd_1562593 534907517567406720934181 := by
  unfold tailWord_1562593
  simp only [CollatzResearch.WordTrace]
  refine ⟨56992448827999905482932433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37994965885333270321954955 56992448827999905482932433)
  ·
    refine ⟨42744336620999929112199325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56992448827999905482932433 42744336620999929112199325)
    ·
      refine ⟨16029126232874973417074747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42744336620999929112199325 16029126232874973417074747)
      ·
        refine ⟨24043689349312460125612121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16029126232874973417074747 24043689349312460125612121)
        ·
          refine ⟨18032767011984345094209091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24043689349312460125612121 18032767011984345094209091)
          ·
            refine ⟨27049150517976517641313637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18032767011984345094209091 27049150517976517641313637)
            ·
              refine ⟨5071715722120597057746307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27049150517976517641313637 5071715722120597057746307)
              ·
                refine ⟨7607573583180895586619461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071715722120597057746307 7607573583180895586619461)
                ·
                  refine ⟨1426420046846417922491149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7607573583180895586619461 1426420046846417922491149)
                  ·
                    refine ⟨534907517567406720934181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426420046846417922491149 534907517567406720934181)
                    ·
                      rfl

theorem cell22_1562593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_1562593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562593 prefixEnd_1562593 := by exact prefixLift 1562593
  have htrace : WordTrace (prefixWord ++ tailWord_1562593) baseStart_1562593 baseEnd_1562593 := by
    simpa [prefixWord, tailWord_1562593, baseEnd_1562593] using wordTrace_append hprefix tailTrace_1562593
  have hstable : (prefixWord ++ tailWord_1562593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562593).length < 2 ^ (prefixWord ++ tailWord_1562593).sum := by decide
  have hdescent : baseEnd_1562593 < baseStart_1562593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562614 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1562614 : Nat := 118140960795 + 1562614 * 2 ^ 59
def prefixEnd_1562614 : Nat := 4983230072969 + 3 ^ 40 * 1562614 * 2
def baseEnd_1562614 : Nat := 534914706296569666159117

theorem tailTrace_1562614 : CollatzResearch.WordTrace tailWord_1562614 prefixEnd_1562614 534914706296569666159117 := by
  unfold tailWord_1562614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562075922557739129340431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37995476507282550712964597 3562075922557739129340431)
  ·
    refine ⟨5343113883836608694010647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562075922557739129340431 5343113883836608694010647)
    ·
      refine ⟨8014670825754913041015971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5343113883836608694010647 8014670825754913041015971)
      ·
        refine ⟨12022006238632369561523957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014670825754913041015971 12022006238632369561523957)
        ·
          refine ⟨1127063084871784646392871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12022006238632369561523957 1127063084871784646392871)
          ·
            refine ⟨1690594627307676969589307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127063084871784646392871 1690594627307676969589307)
            ·
              refine ⟨2535891940961515454383961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690594627307676969589307 2535891940961515454383961)
              ·
                refine ⟨1901918955721136590787971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535891940961515454383961 1901918955721136590787971)
                ·
                  refine ⟨2852878433581704886181957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901918955721136590787971 2852878433581704886181957)
                  ·
                    refine ⟨534914706296569666159117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852878433581704886181957 534914706296569666159117)
                    ·
                      rfl

theorem cell22_1562614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1562614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562614 prefixEnd_1562614 := by exact prefixLift 1562614
  have htrace : WordTrace (prefixWord ++ tailWord_1562614) baseStart_1562614 baseEnd_1562614 := by
    simpa [prefixWord, tailWord_1562614, baseEnd_1562614] using wordTrace_append hprefix tailTrace_1562614
  have hstable : (prefixWord ++ tailWord_1562614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562614).length < 2 ^ (prefixWord ++ tailWord_1562614).sum := by decide
  have hdescent : baseEnd_1562614 < baseStart_1562614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562621 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1562621 : Nat := 118140960795 + 1562621 * 2 ^ 59
def prefixEnd_1562621 : Nat := 4983230072969 + 3 ^ 40 * 1562621 * 2
def baseEnd_1562621 : Nat := 534917102539623981234095

theorem tailTrace_1562621 : CollatzResearch.WordTrace tailWord_1562621 prefixEnd_1562621 534917102539623981234095 := by
  unfold tailWord_1562621
  simp only [CollatzResearch.WordTrace]
  refine ⟨56993470071898466264951717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37995646714598977509967811 56993470071898466264951717)
  ·
    refine ⟨10686275638480962424678447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56993470071898466264951717 10686275638480962424678447)
    ·
      refine ⟨16029413457721443637017671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10686275638480962424678447 16029413457721443637017671)
      ·
        refine ⟨24044120186582165455526507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16029413457721443637017671 24044120186582165455526507)
        ·
          refine ⟨36066180279873248183289761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24044120186582165455526507 36066180279873248183289761)
          ·
            refine ⟨27049635209904936137467321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36066180279873248183289761 27049635209904936137467321)
            ·
              refine ⟨20287226407428702103100491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27049635209904936137467321 20287226407428702103100491)
              ·
                refine ⟨30430839611143053154650737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20287226407428702103100491 30430839611143053154650737)
                ·
                  refine ⟨22823129708357289865988053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30430839611143053154650737 22823129708357289865988053)
                  ·
                    refine ⟨534917102539623981234095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22823129708357289865988053 534917102539623981234095)
                    ·
                      rfl

theorem cell22_1562621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1562621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562621 prefixEnd_1562621 := by exact prefixLift 1562621
  have htrace : WordTrace (prefixWord ++ tailWord_1562621) baseStart_1562621 baseEnd_1562621 := by
    simpa [prefixWord, tailWord_1562621, baseEnd_1562621] using wordTrace_append hprefix tailTrace_1562621
  have hstable : (prefixWord ++ tailWord_1562621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562621).length < 2 ^ (prefixWord ++ tailWord_1562621).sum := by decide
  have hdescent : baseEnd_1562621 < baseStart_1562621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562653 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1562653 : Nat := 118140960795 + 1562653 * 2 ^ 59
def prefixEnd_1562653 : Nat := 4983230072969 + 3 ^ 40 * 1562653 * 2
def baseEnd_1562653 : Nat := 534928056793586564433997

theorem tailTrace_1562653 : CollatzResearch.WordTrace tailWord_1562653 prefixEnd_1562653 534928056793586564433997 := by
  unfold tailWord_1562653
  simp only [CollatzResearch.WordTrace]
  refine ⟨56994637207782535730116613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37996424805188357153411075 56994637207782535730116613)
  ·
    refine ⟨10686494476459225449396865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56994637207782535730116613 10686494476459225449396865)
    ·
      refine ⟨8014870857344419087047649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10686494476459225449396865 8014870857344419087047649)
      ·
        refine ⟨6011153143008314315285737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8014870857344419087047649 6011153143008314315285737)
        ·
          refine ⟨4508364857256235736464303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6011153143008314315285737 4508364857256235736464303)
          ·
            refine ⟨6762547285884353604696455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508364857256235736464303 6762547285884353604696455)
            ·
              refine ⟨10143820928826530407044683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762547285884353604696455 10143820928826530407044683)
              ·
                refine ⟨15215731393239795610567025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143820928826530407044683 15215731393239795610567025)
                ·
                  refine ⟨11411798544929846707925269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15215731393239795610567025 11411798544929846707925269)
                  ·
                    refine ⟨534928056793586564433997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11411798544929846707925269 534928056793586564433997)
                    ·
                      rfl

theorem cell22_1562653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1562653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562653 prefixEnd_1562653 := by exact prefixLift 1562653
  have htrace : WordTrace (prefixWord ++ tailWord_1562653) baseStart_1562653 baseEnd_1562653 := by
    simpa [prefixWord, tailWord_1562653, baseEnd_1562653] using wordTrace_append hprefix tailTrace_1562653
  have hstable : (prefixWord ++ tailWord_1562653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562653).length < 2 ^ (prefixWord ++ tailWord_1562653).sum := by decide
  have hdescent : baseEnd_1562653 < baseStart_1562653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562689 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1562689 : Nat := 118140960795 + 1562689 * 2 ^ 59
def prefixEnd_1562689 : Nat := 4983230072969 + 3 ^ 40 * 1562689 * 2
def baseEnd_1562689 : Nat := 534940380329294470533887

theorem tailTrace_1562689 : CollatzResearch.WordTrace tailWord_1562689 prefixEnd_1562689 534940380329294470533887 := by
  unfold tailWord_1562689
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995950235652113878427121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37997300157101409252284747 56995950235652113878427121)
  ·
    refine ⟨42746962676739085408820341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56995950235652113878427121 42746962676739085408820341)
    ·
      refine ⟨4007527750944289257076907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42746962676739085408820341 4007527750944289257076907)
      ·
        refine ⟨6011291626416433885615361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007527750944289257076907 6011291626416433885615361)
        ·
          refine ⟨4508468719812325414211521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6011291626416433885615361 4508468719812325414211521)
          ·
            refine ⟨3381351539859244060658641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4508468719812325414211521 3381351539859244060658641)
            ·
              refine ⟨2536013654894433045493981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381351539859244060658641 2536013654894433045493981)
              ·
                refine ⟨951005120585412392060243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2536013654894433045493981 951005120585412392060243)
                ·
                  refine ⟨1426507680878118588090365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951005120585412392060243 1426507680878118588090365)
                  ·
                    refine ⟨534940380329294470533887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426507680878118588090365 534940380329294470533887)
                    ·
                      rfl

theorem cell22_1562689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1562689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562689 prefixEnd_1562689 := by exact prefixLift 1562689
  have htrace : WordTrace (prefixWord ++ tailWord_1562689) baseStart_1562689 baseEnd_1562689 := by
    simpa [prefixWord, tailWord_1562689, baseEnd_1562689] using wordTrace_append hprefix tailTrace_1562689
  have hstable : (prefixWord ++ tailWord_1562689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562689).length < 2 ^ (prefixWord ++ tailWord_1562689).sum := by decide
  have hdescent : baseEnd_1562689 < baseStart_1562689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562713 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 6]
def baseStart_1562713 : Nat := 118140960795 + 1562713 * 2 ^ 59
def prefixEnd_1562713 : Nat := 4983230072969 + 3 ^ 40 * 1562713 * 2
def baseEnd_1562713 : Nat := 178316198673255469311271

theorem tailTrace_1562713 : CollatzResearch.WordTrace tailWord_1562713 prefixEnd_1562713 178316198673255469311271 := by
  unfold tailWord_1562713
  simp only [CollatzResearch.WordTrace]
  refine ⟨56996825587565165977300793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37997883725043443984867195 56996825587565165977300793)
  ·
    refine ⟨42747619190673874482975595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56996825587565165977300793 42747619190673874482975595)
    ·
      refine ⟨64121428786010811724463393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42747619190673874482975595 64121428786010811724463393)
      ·
        refine ⟨48091071589508108793347545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64121428786010811724463393 48091071589508108793347545)
        ·
          refine ⟨36068303692131081595010659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48091071589508108793347545 36068303692131081595010659)
          ·
            refine ⟨54102455538196622392515989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36068303692131081595010659 54102455538196622392515989)
            ·
              refine ⟨2536052603352966674649187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54102455538196622392515989 2536052603352966674649187)
              ·
                refine ⟨3804078905029450011973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536052603352966674649187 3804078905029450011973781)
                ·
                  refine ⟨178316198673255469311271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3804078905029450011973781 178316198673255469311271)
                  ·
                    rfl

theorem cell22_1562713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_1562713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562713 prefixEnd_1562713 := by exact prefixLift 1562713
  have htrace : WordTrace (prefixWord ++ tailWord_1562713) baseStart_1562713 baseEnd_1562713 := by
    simpa [prefixWord, tailWord_1562713, baseEnd_1562713] using wordTrace_append hprefix tailTrace_1562713
  have hstable : (prefixWord ++ tailWord_1562713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562713).length < 2 ^ (prefixWord ++ tailWord_1562713).sum := by decide
  have hdescent : baseEnd_1562713 < baseStart_1562713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562743 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1562743 : Nat := 118140960795 + 1562743 * 2 ^ 59
def prefixEnd_1562743 : Nat := 4983230072969 + 3 ^ 40 * 1562743 * 2
def baseEnd_1562743 : Nat := 534958865632856329683721

theorem tailTrace_1562743 : CollatzResearch.WordTrace tailWord_1562743 prefixEnd_1562743 534958865632856329683721 := by
  unfold tailWord_1562743
  simp only [CollatzResearch.WordTrace]
  refine ⟨56997919777456481100892883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37998613184970987400595255 56997919777456481100892883)
  ·
    refine ⟨85496879666184721651339325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56997919777456481100892883 85496879666184721651339325)
    ·
      refine ⟨32061329874819270619252247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85496879666184721651339325 32061329874819270619252247)
      ·
        refine ⟨48091994812228905928878371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32061329874819270619252247 48091994812228905928878371)
        ·
          refine ⟨72137992218343358893317557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48091994812228905928878371 72137992218343358893317557)
          ·
            refine ⟨6762936770469689896248521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72137992218343358893317557 6762936770469689896248521)
            ·
              refine ⟨5072202577852267422186391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6762936770469689896248521 5072202577852267422186391)
              ·
                refine ⟨7608303866778401133279587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072202577852267422186391 7608303866778401133279587)
                ·
                  refine ⟨11412455800167601699919381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7608303866778401133279587 11412455800167601699919381)
                  ·
                    refine ⟨534958865632856329683721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11412455800167601699919381 534958865632856329683721)
                    ·
                      rfl

theorem cell22_1562743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1562743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562743 prefixEnd_1562743 := by exact prefixLift 1562743
  have htrace : WordTrace (prefixWord ++ tailWord_1562743) baseStart_1562743 baseEnd_1562743 := by
    simpa [prefixWord, tailWord_1562743, baseEnd_1562743] using wordTrace_append hprefix tailTrace_1562743
  have hstable : (prefixWord ++ tailWord_1562743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562743).length < 2 ^ (prefixWord ++ tailWord_1562743).sum := by decide
  have hdescent : baseEnd_1562743 < baseStart_1562743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562745 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_1562745 : Nat := 118140960795 + 1562745 * 2 ^ 59
def prefixEnd_1562745 : Nat := 4983230072969 + 3 ^ 40 * 1562745 * 2
def baseEnd_1562745 : Nat := 534959550273728991133715

theorem tailTrace_1562745 : CollatzResearch.WordTrace tailWord_1562745 prefixEnd_1562745 534959550273728991133715 := by
  unfold tailWord_1562745
  simp only [CollatzResearch.WordTrace]
  refine ⟨56997992723449235442465689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37998661815632823628310459 56997992723449235442465689)
  ·
    refine ⟨42748494542586926581849267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56997992723449235442465689 42748494542586926581849267)
    ·
      refine ⟨64122741813880389872773901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42748494542586926581849267 64122741813880389872773901)
      ·
        refine ⟨24046028180205146202290213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64122741813880389872773901 24046028180205146202290213)
        ·
          refine ⟨4508630283788464912929415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24046028180205146202290213 4508630283788464912929415)
          ·
            refine ⟨6762945425682697369394123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508630283788464912929415 6762945425682697369394123)
            ·
              refine ⟨10144418138524046054091185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762945425682697369394123 10144418138524046054091185)
              ·
                refine ⟨7608313603893034540568389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10144418138524046054091185 7608313603893034540568389)
                ·
                  refine ⟨1426558800729943976356573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7608313603893034540568389 1426558800729943976356573)
                  ·
                    refine ⟨534959550273728991133715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426558800729943976356573 534959550273728991133715)
                    ·
                      rfl

theorem cell22_1562745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_1562745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562745 prefixEnd_1562745 := by exact prefixLift 1562745
  have htrace : WordTrace (prefixWord ++ tailWord_1562745) baseStart_1562745 baseEnd_1562745 := by
    simpa [prefixWord, tailWord_1562745, baseEnd_1562745] using wordTrace_append hprefix tailTrace_1562745
  have hstable : (prefixWord ++ tailWord_1562745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562745).length < 2 ^ (prefixWord ++ tailWord_1562745).sum := by decide
  have hdescent : baseEnd_1562745 < baseStart_1562745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562760 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1562760 : Nat := 118140960795 + 1562760 * 2 ^ 59
def prefixEnd_1562760 : Nat := 4983230072969 + 3 ^ 40 * 1562760 * 2
def baseEnd_1562760 : Nat := 534964685080273952008669

theorem tailTrace_1562760 : CollatzResearch.WordTrace tailWord_1562760 prefixEnd_1562760 534964685080273952008669 := by
  unfold tailWord_1562760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28499269909197446502130867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37999026545596595336174489 28499269909197446502130867)
  ·
    refine ⟨42748904863796169753196301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28499269909197446502130867 42748904863796169753196301)
    ·
      refine ⟨16030839323923563657448613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42748904863796169753196301 16030839323923563657448613)
      ·
        refine ⟨3005782373235668185771615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16030839323923563657448613 3005782373235668185771615)
        ·
          refine ⟨4508673559853502278657423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005782373235668185771615 4508673559853502278657423)
          ·
            refine ⟨6763010339780253417986135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508673559853502278657423 6763010339780253417986135)
            ·
              refine ⟨10144515509670380126979203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763010339780253417986135 10144515509670380126979203)
              ·
                refine ⟨15216773264505570190468805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144515509670380126979203 15216773264505570190468805)
                ·
                  refine ⟨2853144987094794410712901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15216773264505570190468805 2853144987094794410712901)
                  ·
                    refine ⟨534964685080273952008669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2853144987094794410712901 534964685080273952008669)
                    ·
                      rfl

theorem cell22_1562760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1562760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562760 prefixEnd_1562760 := by exact prefixLift 1562760
  have htrace : WordTrace (prefixWord ++ tailWord_1562760) baseStart_1562760 baseEnd_1562760 := by
    simpa [prefixWord, tailWord_1562760, baseEnd_1562760] using wordTrace_append hprefix tailTrace_1562760
  have hstable : (prefixWord ++ tailWord_1562760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562760).length < 2 ^ (prefixWord ++ tailWord_1562760).sum := by decide
  have hdescent : baseEnd_1562760 < baseStart_1562760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562775 : List Nat := [1, 1, 3, 3, 4, 1, 2, 7]
def baseStart_1562775 : Nat := 118140960795 + 1562775 * 2 ^ 59
def prefixEnd_1562775 : Nat := 4983230072969 + 3 ^ 40 * 1562775 * 2
def baseEnd_1562775 : Nat := 59441091098535434764847

theorem tailTrace_1562775 : CollatzResearch.WordTrace tailWord_1562775 prefixEnd_1562775 59441091098535434764847 := by
  unfold tailWord_1562775
  simp only [CollatzResearch.WordTrace]
  refine ⟨56999086913340550566057779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37999391275560367044038519 56999086913340550566057779)
  ·
    refine ⟨85498630370010825849086669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56999086913340550566057779 85498630370010825849086669)
    ·
      refine ⟨32061986388754059693407501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85498630370010825849086669 32061986388754059693407501)
      ·
        refine ⟨12023244895782772385027813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32061986388754059693407501 12023244895782772385027813)
        ·
          refine ⟨2254358417959269822192715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12023244895782772385027813 2254358417959269822192715)
          ·
            refine ⟨3381537626938904733289073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254358417959269822192715 3381537626938904733289073)
            ·
              refine ⟨2536153220204178549966805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381537626938904733289073 2536153220204178549966805)
              ·
                refine ⟨59441091098535434764847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2536153220204178549966805 59441091098535434764847)
                ·
                  rfl

theorem cell22_1562775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 7].length) (baseStart_1562775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562775 prefixEnd_1562775 := by exact prefixLift 1562775
  have htrace : WordTrace (prefixWord ++ tailWord_1562775) baseStart_1562775 baseEnd_1562775 := by
    simpa [prefixWord, tailWord_1562775, baseEnd_1562775] using wordTrace_append hprefix tailTrace_1562775
  have hstable : (prefixWord ++ tailWord_1562775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562775).length < 2 ^ (prefixWord ++ tailWord_1562775).sum := by decide
  have hdescent : baseEnd_1562775 < baseStart_1562775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562794 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1562794 : Nat := 118140960795 + 1562794 * 2 ^ 59
def prefixEnd_1562794 : Nat := 4983230072969 + 3 ^ 40 * 1562794 * 2
def baseEnd_1562794 : Nat := 534976323975109196658565

theorem tailTrace_1562794 : CollatzResearch.WordTrace tailWord_1562794 prefixEnd_1562794 534976323975109196658565 := by
  unfold tailWord_1562794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14249944975067929202749859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37999853266847811207332957 14249944975067929202749859)
  ·
    refine ⟨21374917462601893804124789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14249944975067929202749859 21374917462601893804124789)
    ·
      refine ⟨2003898512118927544136699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21374917462601893804124789 2003898512118927544136699)
      ·
        refine ⟨3005847768178391316205049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003898512118927544136699 3005847768178391316205049)
        ·
          refine ⟨2254385826133793487153787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005847768178391316205049 2254385826133793487153787)
          ·
            refine ⟨3381578739200690230730681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254385826133793487153787 3381578739200690230730681)
            ·
              refine ⟨2536184054400517673048011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381578739200690230730681 2536184054400517673048011)
              ·
                refine ⟨3804276081600776509572017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536184054400517673048011 3804276081600776509572017)
                ·
                  refine ⟨2853207061200582382179013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3804276081600776509572017 2853207061200582382179013)
                  ·
                    refine ⟨534976323975109196658565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2853207061200582382179013 534976323975109196658565)
                    ·
                      rfl

theorem cell22_1562794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1562794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562794 prefixEnd_1562794 := by exact prefixLift 1562794
  have htrace : WordTrace (prefixWord ++ tailWord_1562794) baseStart_1562794 baseEnd_1562794 := by
    simpa [prefixWord, tailWord_1562794, baseEnd_1562794] using wordTrace_append hprefix tailTrace_1562794
  have hstable : (prefixWord ++ tailWord_1562794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562794).length < 2 ^ (prefixWord ++ tailWord_1562794).sum := by decide
  have hdescent : baseEnd_1562794 < baseStart_1562794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562882 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1562882 : Nat := 118140960795 + 1562882 * 2 ^ 59
def prefixEnd_1562882 : Nat := 4983230072969 + 3 ^ 40 * 1562882 * 2
def baseEnd_1562882 : Nat := 178335482724502100152765

theorem tailTrace_1562882 : CollatzResearch.WordTrace tailWord_1562882 prefixEnd_1562882 178335482724502100152765 := by
  unfold tailWord_1562882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14250747380988226960050725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38001993015968605226801933 14250747380988226960050725)
  ·
    refine ⟨2672015133935292555009511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14250747380988226960050725 2672015133935292555009511)
    ·
      refine ⟨4008022700902938832514267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2672015133935292555009511 4008022700902938832514267)
      ·
        refine ⟨6012034051354408248771401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008022700902938832514267 6012034051354408248771401)
        ·
          refine ⟨4509025538515806186578551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6012034051354408248771401 4509025538515806186578551)
          ·
            refine ⟨6763538307773709279867827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509025538515806186578551 6763538307773709279867827)
            ·
              refine ⟨10145307461660563919801741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763538307773709279867827 10145307461660563919801741)
              ·
                refine ⟨3804490298122711469925653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10145307461660563919801741 3804490298122711469925653)
                ·
                  refine ⟨178335482724502100152765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3804490298122711469925653 178335482724502100152765)
                  ·
                    rfl

theorem cell22_1562882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1562882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562882 prefixEnd_1562882 := by exact prefixLift 1562882
  have htrace : WordTrace (prefixWord ++ tailWord_1562882) baseStart_1562882 baseEnd_1562882 := by
    simpa [prefixWord, tailWord_1562882, baseEnd_1562882] using wordTrace_append hprefix tailTrace_1562882
  have hstable : (prefixWord ++ tailWord_1562882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562882).length < 2 ^ (prefixWord ++ tailWord_1562882).sum := by decide
  have hdescent : baseEnd_1562882 < baseStart_1562882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562897 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_1562897 : Nat := 118140960795 + 1562897 * 2 ^ 59
def prefixEnd_1562897 : Nat := 4983230072969 + 3 ^ 40 * 1562897 * 2
def baseEnd_1562897 : Nat := 535011582980051261333249

theorem tailTrace_1562897 : CollatzResearch.WordTrace tailWord_1562897 prefixEnd_1562897 535011582980051261333249 := by
  unfold tailWord_1562897
  simp only [CollatzResearch.WordTrace]
  refine ⟨57003536618898565401998945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38002357745932376934665963 57003536618898565401998945)
  ·
    refine ⟨42752652464173924051499209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57003536618898565401998945 42752652464173924051499209)
    ·
      refine ⟨32064489348130443038624407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42752652464173924051499209 32064489348130443038624407)
      ·
        refine ⟨48096734022195664557936611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32064489348130443038624407 48096734022195664557936611)
        ·
          refine ⟨72145101033293496836904917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48096734022195664557936611 72145101033293496836904917)
          ·
            refine ⟨1690900805467816332114959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 72145101033293496836904917 1690900805467816332114959)
            ·
              refine ⟨2536351208201724498172439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690900805467816332114959 2536351208201724498172439)
              ·
                refine ⟨3804526812302586747258659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536351208201724498172439 3804526812302586747258659)
                ·
                  refine ⟨5706790218453880120887989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804526812302586747258659 5706790218453880120887989)
                  ·
                    refine ⟨535011582980051261333249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5706790218453880120887989 535011582980051261333249)
                    ·
                      rfl

theorem cell22_1562897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_1562897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562897 prefixEnd_1562897 := by exact prefixLift 1562897
  have htrace : WordTrace (prefixWord ++ tailWord_1562897) baseStart_1562897 baseEnd_1562897 := by
    simpa [prefixWord, tailWord_1562897, baseEnd_1562897] using wordTrace_append hprefix tailTrace_1562897
  have hstable : (prefixWord ++ tailWord_1562897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562897).length < 2 ^ (prefixWord ++ tailWord_1562897).sum := by decide
  have hdescent : baseEnd_1562897 < baseStart_1562897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562940 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1562940 : Nat := 118140960795 + 1562940 * 2 ^ 59
def prefixEnd_1562940 : Nat := 4983230072969 + 3 ^ 40 * 1562940 * 2
def baseEnd_1562940 : Nat := 535026302758813482508117

theorem tailTrace_1562940 : CollatzResearch.WordTrace tailWord_1562940 prefixEnd_1562940 535026302758813482508117 := by
  unfold tailWord_1562940
  simp only [CollatzResearch.WordTrace]
  refine ⟨28502552478871391872907137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38003403305161855830542849 28502552478871391872907137)
  ·
    refine ⟨21376914359153543904680353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28502552478871391872907137 21376914359153543904680353)
    ·
      refine ⟨16032685769365157928510265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21376914359153543904680353 16032685769365157928510265)
      ·
        refine ⟨12024514327023868446382699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16032685769365157928510265 12024514327023868446382699)
        ·
          refine ⟨18036771490535802669574049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12024514327023868446382699 18036771490535802669574049)
          ·
            refine ⟨13527578617901852002180537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18036771490535802669574049 13527578617901852002180537)
            ·
              refine ⟨10145683963426389001635403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13527578617901852002180537 10145683963426389001635403)
              ·
                refine ⟨15218525945139583502453105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145683963426389001635403 15218525945139583502453105)
                ·
                  refine ⟨11413894458854687626839829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15218525945139583502453105 11413894458854687626839829)
                  ·
                    refine ⟨535026302758813482508117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11413894458854687626839829 535026302758813482508117)
                    ·
                      rfl

theorem cell22_1562940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1562940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562940 prefixEnd_1562940 := by exact prefixLift 1562940
  have htrace : WordTrace (prefixWord ++ tailWord_1562940) baseStart_1562940 baseEnd_1562940 := by
    simpa [prefixWord, tailWord_1562940, baseEnd_1562940] using wordTrace_append hprefix tailTrace_1562940
  have hstable : (prefixWord ++ tailWord_1562940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562940).length < 2 ^ (prefixWord ++ tailWord_1562940).sum := by decide
  have hdescent : baseEnd_1562940 < baseStart_1562940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562970 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1562970 : Nat := 118140960795 + 1562970 * 2 ^ 59
def prefixEnd_1562970 : Nat := 4983230072969 + 3 ^ 40 * 1562970 * 2
def baseEnd_1562970 : Nat := 535036572371903404258025

theorem tailTrace_1562970 : CollatzResearch.WordTrace tailWord_1562970 prefixEnd_1562970 535036572371903404258025 := by
  unfold tailWord_1562970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14251549786908524717351591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38004132765089399246270909 14251549786908524717351591)
  ·
    refine ⟨21377324680362787076027387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14251549786908524717351591 21377324680362787076027387)
    ·
      refine ⟨32065987020544180614041081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21377324680362787076027387 32065987020544180614041081)
      ·
        refine ⟨24049490265408135460530811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32065987020544180614041081 24049490265408135460530811)
        ·
          refine ⟨36074235398112203190796217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24049490265408135460530811 36074235398112203190796217)
          ·
            refine ⟨27055676548584152393097163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36074235398112203190796217 27055676548584152393097163)
            ·
              refine ⟨40583514822876228589645745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27055676548584152393097163 40583514822876228589645745)
              ·
                refine ⟨30437636117157171442234309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40583514822876228589645745 30437636117157171442234309)
                ·
                  refine ⟨5707056771966969645418933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30437636117157171442234309 5707056771966969645418933)
                  ·
                    refine ⟨535036572371903404258025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5707056771966969645418933 535036572371903404258025)
                    ·
                      rfl

theorem cell22_1562970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1562970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1562970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1562970 prefixEnd_1562970 := by exact prefixLift 1562970
  have htrace : WordTrace (prefixWord ++ tailWord_1562970) baseStart_1562970 baseEnd_1562970 := by
    simpa [prefixWord, tailWord_1562970, baseEnd_1562970] using wordTrace_append hprefix tailTrace_1562970
  have hstable : (prefixWord ++ tailWord_1562970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562970).length < 2 ^ (prefixWord ++ tailWord_1562970).sum := by decide
  have hdescent : baseEnd_1562970 < baseStart_1562970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563017 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 6]
def baseStart_1563017 : Nat := 118140960795 + 1563017 * 2 ^ 59
def prefixEnd_1563017 : Nat := 4983230072969 + 3 ^ 40 * 1563017 * 2
def baseEnd_1563017 : Nat := 178350887144136982777627

theorem tailTrace_1563017 : CollatzResearch.WordTrace tailWord_1563017 prefixEnd_1563017 178350887144136982777627 := by
  unfold tailWord_1563017
  simp only [CollatzResearch.WordTrace]
  refine ⟨57007913378463825896367305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38005275585642550597578203 57007913378463825896367305)
  ·
    refine ⟨42755935033847869422275479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57007913378463825896367305 42755935033847869422275479)
    ·
      refine ⟨64133902550771804133413219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42755935033847869422275479 64133902550771804133413219)
      ·
        refine ⟨96200853826157706200119829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64133902550771804133413219 96200853826157706200119829)
        ·
          refine ⟨4509415023101142478130617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96200853826157706200119829 4509415023101142478130617)
          ·
            refine ⟨3382061267325856858597963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4509415023101142478130617 3382061267325856858597963)
            ·
              refine ⟨5073091900988785287896945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382061267325856858597963 5073091900988785287896945)
              ·
                refine ⟨3804818925741588965922709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073091900988785287896945 3804818925741588965922709)
                ·
                  refine ⟨178350887144136982777627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3804818925741588965922709 178350887144136982777627)
                  ·
                    rfl

theorem cell22_1563017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_1563017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563017 prefixEnd_1563017 := by exact prefixLift 1563017
  have htrace : WordTrace (prefixWord ++ tailWord_1563017) baseStart_1563017 baseEnd_1563017 := by
    simpa [prefixWord, tailWord_1563017, baseEnd_1563017] using wordTrace_append hprefix tailTrace_1563017
  have hstable : (prefixWord ++ tailWord_1563017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563017).length < 2 ^ (prefixWord ++ tailWord_1563017).sum := by decide
  have hdescent : baseEnd_1563017 < baseStart_1563017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563034 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_1563034 : Nat := 118140960795 + 1563034 * 2 ^ 59
def prefixEnd_1563034 : Nat := 4983230072969 + 3 ^ 40 * 1563034 * 2
def baseEnd_1563034 : Nat := 178352826959942856885943

theorem tailTrace_1563034 : CollatzResearch.WordTrace tailWord_1563034 prefixEnd_1563034 178352826959942856885943 := by
  unfold tailWord_1563034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252133354850559449934039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38005688946268158533157437 14252133354850559449934039)
  ·
    refine ⟨21378200032275839174901059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14252133354850559449934039 21378200032275839174901059)
    ·
      refine ⟨32067300048413758762351589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21378200032275839174901059 32067300048413758762351589)
      ·
        refine ⟨6012618759077579767940923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32067300048413758762351589 6012618759077579767940923)
        ·
          refine ⟨9018928138616369651911385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6012618759077579767940923 9018928138616369651911385)
          ·
            refine ⟨6764196103962277238933539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9018928138616369651911385 6764196103962277238933539)
            ·
              refine ⟨10146294155943415858400309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6764196103962277238933539 10146294155943415858400309)
              ·
                refine ⟨951215077119695236725029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10146294155943415858400309 951215077119695236725029)
                ·
                  refine ⟨178352826959942856885943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951215077119695236725029 178352826959942856885943)
                  ·
                    rfl

theorem cell22_1563034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_1563034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563034 prefixEnd_1563034 := by exact prefixLift 1563034
  have htrace : WordTrace (prefixWord ++ tailWord_1563034) baseStart_1563034 baseEnd_1563034 := by
    simpa [prefixWord, tailWord_1563034, baseEnd_1563034] using wordTrace_append hprefix tailTrace_1563034
  have hstable : (prefixWord ++ tailWord_1563034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563034).length < 2 ^ (prefixWord ++ tailWord_1563034).sum := by decide
  have hdescent : baseEnd_1563034 < baseStart_1563034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563045 : List Nat := [1, 3, 1, 2, 1, 1, 13]
def baseStart_1563045 : Nat := 118140960795 + 1563045 * 2 ^ 59
def prefixEnd_1563045 : Nat := 4983230072969 + 3 ^ 40 * 1563045 * 2
def baseEnd_1563045 : Nat := 19817120237208452171585

theorem tailTrace_1563045 : CollatzResearch.WordTrace tailWord_1563045 prefixEnd_1563045 19817120237208452171585 := by
  unfold tailWord_1563045
  simp only [CollatzResearch.WordTrace]
  refine ⟨57008934622362386678386589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38005956414908257785591059 57008934622362386678386589)
  ·
    refine ⟨21378350483385895004394971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57008934622362386678386589 21378350483385895004394971)
    ·
      refine ⟨32067525725078842506592457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21378350483385895004394971 32067525725078842506592457)
      ·
        refine ⟨24050644293809131879944343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32067525725078842506592457 24050644293809131879944343)
        ·
          refine ⟨36075966440713697819916515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24050644293809131879944343 36075966440713697819916515)
          ·
            refine ⟨54113949661070546729874773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36075966440713697819916515 54113949661070546729874773)
            ·
              refine ⟨19817120237208452171585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 54113949661070546729874773 19817120237208452171585)
              ·
                rfl

theorem cell22_1563045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 13].length) (baseStart_1563045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563045 prefixEnd_1563045 := by exact prefixLift 1563045
  have htrace : WordTrace (prefixWord ++ tailWord_1563045) baseStart_1563045 baseEnd_1563045 := by
    simpa [prefixWord, tailWord_1563045, baseEnd_1563045] using wordTrace_append hprefix tailTrace_1563045
  have hstable : (prefixWord ++ tailWord_1563045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563045).length < 2 ^ (prefixWord ++ tailWord_1563045).sum := by decide
  have hdescent : baseEnd_1563045 < baseStart_1563045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563079 : List Nat := [1, 1, 4, 1, 1, 6, 2, 6]
def baseStart_1563079 : Nat := 118140960795 + 1563079 * 2 ^ 59
def prefixEnd_1563079 : Nat := 4983230072969 + 3 ^ 40 * 1563079 * 2
def baseEnd_1563079 : Nat := 59452653922162605920299

theorem tailTrace_1563079 : CollatzResearch.WordTrace tailWord_1563079 prefixEnd_1563079 59452653922162605920299 := by
  unfold tailWord_1563079
  simp only [CollatzResearch.WordTrace]
  refine ⟨57010174704239210485124291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38006783136159473656749527 57010174704239210485124291)
  ·
    refine ⟨85515262056358815727686437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57010174704239210485124291 85515262056358815727686437)
    ·
      refine ⟨16034111635567277948941207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85515262056358815727686437 16034111635567277948941207)
      ·
        refine ⟨24051167453350916923411811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16034111635567277948941207 24051167453350916923411811)
        ·
          refine ⟨36076751180026375385117717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24051167453350916923411811 36076751180026375385117717)
          ·
            refine ⟨1691097711563736346177393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36076751180026375385117717 1691097711563736346177393)
            ·
              refine ⟨1268323283672802259633045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691097711563736346177393 1268323283672802259633045)
              ·
                refine ⟨59452653922162605920299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1268323283672802259633045 59452653922162605920299)
                ·
                  rfl

theorem cell22_1563079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 6].length) (baseStart_1563079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563079 prefixEnd_1563079 := by exact prefixLift 1563079
  have htrace : WordTrace (prefixWord ++ tailWord_1563079) baseStart_1563079 baseEnd_1563079 := by
    simpa [prefixWord, tailWord_1563079, baseEnd_1563079] using wordTrace_append hprefix tailTrace_1563079
  have hstable : (prefixWord ++ tailWord_1563079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563079).length < 2 ^ (prefixWord ++ tailWord_1563079).sum := by decide
  have hdescent : baseEnd_1563079 < baseStart_1563079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563167 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_1563167 : Nat := 118140960795 + 1563167 * 2 ^ 59
def prefixEnd_1563167 : Nat := 4983230072969 + 3 ^ 40 * 1563167 * 2
def baseEnd_1563167 : Nat := 535104009497860557082421

theorem tailTrace_1563167 : CollatzResearch.WordTrace tailWord_1563167 prefixEnd_1563167 535104009497860557082421 := by
  unfold tailWord_1563167
  simp only [CollatzResearch.WordTrace]
  refine ⟨57013384327920401514327755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38008922885280267676218503 57013384327920401514327755)
  ·
    refine ⟨85520076491880602271491633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57013384327920401514327755 85520076491880602271491633)
    ·
      refine ⟨64140057368910451703618725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85520076491880602271491633 64140057368910451703618725)
      ·
        refine ⟨12026260756670709694428511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64140057368910451703618725 12026260756670709694428511)
        ·
          refine ⟨18039391135006064541642767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12026260756670709694428511 18039391135006064541642767)
          ·
            refine ⟨27059086702509096812464151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18039391135006064541642767 27059086702509096812464151)
            ·
              refine ⟨40588630053763645218696227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27059086702509096812464151 40588630053763645218696227)
              ·
                refine ⟨60882945080645467828044341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40588630053763645218696227 60882945080645467828044341)
                ·
                  refine ⟨5707776101310512608879157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60882945080645467828044341 5707776101310512608879157)
                  ·
                    refine ⟨535104009497860557082421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5707776101310512608879157 535104009497860557082421)
                    ·
                      rfl

theorem cell22_1563167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_1563167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563167 prefixEnd_1563167 := by exact prefixLift 1563167
  have htrace : WordTrace (prefixWord ++ tailWord_1563167) baseStart_1563167 baseEnd_1563167 := by
    simpa [prefixWord, tailWord_1563167, baseEnd_1563167] using wordTrace_append hprefix tailTrace_1563167
  have hstable : (prefixWord ++ tailWord_1563167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563167).length < 2 ^ (prefixWord ++ tailWord_1563167).sum := by decide
  have hdescent : baseEnd_1563167 < baseStart_1563167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563248 : List Nat := [2, 1, 1, 1, 8, 1, 2, 6]
def baseStart_1563248 : Nat := 118140960795 + 1563248 * 2 ^ 59
def prefixEnd_1563248 : Nat := 4983230072969 + 3 ^ 40 * 1563248 * 2
def baseEnd_1563248 : Nat := 59459081939244816200797

theorem tailTrace_1563248 : CollatzResearch.WordTrace tailWord_1563248 prefixEnd_1563248 59459081939244816200797 := by
  unfold tailWord_1563248
  simp only [CollatzResearch.WordTrace]
  refine ⟨28508169320313476174013199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38010892427084634898684265 28508169320313476174013199)
  ·
    refine ⟨42762253980470214261019799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28508169320313476174013199 42762253980470214261019799)
    ·
      refine ⟨64143380970705321391529699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42762253980470214261019799 64143380970705321391529699)
      ·
        refine ⟨96215071456057982087294549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64143380970705321391529699 96215071456057982087294549)
        ·
          refine ⟨1127520368625679477585483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 96215071456057982087294549 1127520368625679477585483)
          ·
            refine ⟨1691280552938519216378225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127520368625679477585483 1691280552938519216378225)
            ·
              refine ⟨1268460414703889412283669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691280552938519216378225 1268460414703889412283669)
              ·
                refine ⟨59459081939244816200797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1268460414703889412283669 59459081939244816200797)
                ·
                  rfl

theorem cell22_1563248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_1563248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563248 prefixEnd_1563248 := by exact prefixLift 1563248
  have htrace : WordTrace (prefixWord ++ tailWord_1563248) baseStart_1563248 baseEnd_1563248 := by
    simpa [prefixWord, tailWord_1563248, baseEnd_1563248] using wordTrace_append hprefix tailTrace_1563248
  have hstable : (prefixWord ++ tailWord_1563248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563248).length < 2 ^ (prefixWord ++ tailWord_1563248).sum := by decide
  have hdescent : baseEnd_1563248 < baseStart_1563248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563289 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_1563289 : Nat := 118140960795 + 1563289 * 2 ^ 59
def prefixEnd_1563289 : Nat := 4983230072969 + 3 ^ 40 * 1563289 * 2
def baseEnd_1563289 : Nat := 535145772591092905532047

theorem tailTrace_1563289 : CollatzResearch.WordTrace tailWord_1563289 prefixEnd_1563289 535145772591092905532047 := by
  unfold tailWord_1563289
  simp only [CollatzResearch.WordTrace]
  refine ⟨57017834033478416350268921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38011889355652277566845947 57017834033478416350268921)
  ·
    refine ⟨42763375525108812262701691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57017834033478416350268921 42763375525108812262701691)
    ·
      refine ⟨64145063287663218394052537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42763375525108812262701691 64145063287663218394052537)
      ·
        refine ⟨48108797465747413795539403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64145063287663218394052537 48108797465747413795539403)
        ·
          refine ⟨72163196198621120693309105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48108797465747413795539403 72163196198621120693309105)
          ·
            refine ⟨54122397148965840519981829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72163196198621120693309105 54122397148965840519981829)
            ·
              refine ⟨10147949465431095097496593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54122397148965840519981829 10147949465431095097496593)
              ·
                refine ⟨7610962099073321323122445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10147949465431095097496593 7610962099073321323122445)
                ·
                  refine ⟨2854110787152495496170917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7610962099073321323122445 2854110787152495496170917)
                  ·
                    refine ⟨535145772591092905532047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854110787152495496170917 535145772591092905532047)
                    ·
                      rfl

theorem cell22_1563289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_1563289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563289 prefixEnd_1563289 := by exact prefixLift 1563289
  have htrace : WordTrace (prefixWord ++ tailWord_1563289) baseStart_1563289 baseEnd_1563289 := by
    simpa [prefixWord, tailWord_1563289, baseEnd_1563289] using wordTrace_append hprefix tailTrace_1563289
  have hstable : (prefixWord ++ tailWord_1563289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563289).length < 2 ^ (prefixWord ++ tailWord_1563289).sum := by decide
  have hdescent : baseEnd_1563289 < baseStart_1563289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563321 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 4]
def baseStart_1563321 : Nat := 118140960795 + 1563321 * 2 ^ 59
def prefixEnd_1563321 : Nat := 4983230072969 + 3 ^ 40 * 1563321 * 2
def baseEnd_1563321 : Nat := 178385575615018496243983

theorem tailTrace_1563321 : CollatzResearch.WordTrace tailWord_1563321 prefixEnd_1563321 178385575615018496243983 := by
  unfold tailWord_1563321
  simp only [CollatzResearch.WordTrace]
  refine ⟨57019001169362485815433817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38012667446241657210289211 57019001169362485815433817)
  ·
    refine ⟨42764250877021864361575363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57019001169362485815433817 42764250877021864361575363)
    ·
      refine ⟨64146376315532796542363045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42764250877021864361575363 64146376315532796542363045)
      ·
        refine ⟨12027445559162399351693071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64146376315532796542363045 12027445559162399351693071)
        ·
          refine ⟨18041168338743599027539607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12027445559162399351693071 18041168338743599027539607)
          ·
            refine ⟨27061752508115398541309411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18041168338743599027539607 27061752508115398541309411)
            ·
              refine ⟨40592628762173097811964117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27061752508115398541309411 40592628762173097811964117)
              ·
                refine ⟨951389736613431979967909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40592628762173097811964117 951389736613431979967909)
                ·
                  refine ⟨178385575615018496243983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951389736613431979967909 178385575615018496243983)
                  ·
                    rfl

theorem cell22_1563321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_1563321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563321 prefixEnd_1563321 := by exact prefixLift 1563321
  have htrace : WordTrace (prefixWord ++ tailWord_1563321) baseStart_1563321 baseEnd_1563321 := by
    simpa [prefixWord, tailWord_1563321, baseEnd_1563321] using wordTrace_append hprefix tailTrace_1563321
  have hstable : (prefixWord ++ tailWord_1563321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563321).length < 2 ^ (prefixWord ++ tailWord_1563321).sum := by decide
  have hdescent : baseEnd_1563321 < baseStart_1563321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563338 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_1563338 : Nat := 118140960795 + 1563338 * 2 ^ 59
def prefixEnd_1563338 : Nat := 4983230072969 + 3 ^ 40 * 1563338 * 2
def baseEnd_1563338 : Nat := 178387515430824370352299

theorem tailTrace_1563338 : CollatzResearch.WordTrace tailWord_1563338 prefixEnd_1563338 178387515430824370352299 := by
  unfold tailWord_1563338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14254905302575224429700667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38013080806867265145868445 14254905302575224429700667)
  ·
    refine ⟨21382357953862836644551001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14254905302575224429700667 21382357953862836644551001)
    ·
      refine ⟨16036768465397127483413251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21382357953862836644551001 16036768465397127483413251)
      ·
        refine ⟨24055152698095691225119877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16036768465397127483413251 24055152698095691225119877)
        ·
          refine ⟨4510341130892942104709977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24055152698095691225119877 4510341130892942104709977)
          ·
            refine ⟨3382755848169706578532483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4510341130892942104709977 3382755848169706578532483)
            ·
              refine ⟨5074133772254559867798725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382755848169706578532483 5074133772254559867798725)
              ·
                refine ⟨951400082297729975212261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5074133772254559867798725 951400082297729975212261)
                ·
                  refine ⟨178387515430824370352299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951400082297729975212261 178387515430824370352299)
                  ·
                    rfl

theorem cell22_1563338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_1563338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563338 prefixEnd_1563338 := by exact prefixLift 1563338
  have htrace : WordTrace (prefixWord ++ tailWord_1563338) baseStart_1563338 baseEnd_1563338 := by
    simpa [prefixWord, tailWord_1563338, baseEnd_1563338] using wordTrace_append hprefix tailTrace_1563338
  have hstable : (prefixWord ++ tailWord_1563338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563338).length < 2 ^ (prefixWord ++ tailWord_1563338).sum := by decide
  have hdescent : baseEnd_1563338 < baseStart_1563338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563462 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1563462 : Nat := 118140960795 + 1563462 * 2 ^ 59
def prefixEnd_1563462 : Nat := 4983230072969 + 3 ^ 40 * 1563462 * 2
def baseEnd_1563462 : Nat := 178401664675526040318839

theorem tailTrace_1563462 : CollatzResearch.WordTrace tailWord_1563462 prefixEnd_1563462 178401664675526040318839 := by
  unfold tailWord_1563462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782004495682864590509895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38016095907901111264211093 1782004495682864590509895)
  ·
    refine ⟨2673006743524296885764843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1782004495682864590509895 2673006743524296885764843)
    ·
      refine ⟨4009510115286445328647265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673006743524296885764843 4009510115286445328647265)
      ·
        refine ⟨3007132586464833996485449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4009510115286445328647265 3007132586464833996485449)
        ·
          refine ⟨2255349439848625497364087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3007132586464833996485449 2255349439848625497364087)
          ·
            refine ⟨3383024159772938246046131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255349439848625497364087 3383024159772938246046131)
            ·
              refine ⟨5074536239659407369069197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383024159772938246046131 5074536239659407369069197)
              ·
                refine ⟨1902951089872277763400949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5074536239659407369069197 1902951089872277763400949)
                ·
                  refine ⟨178401664675526040318839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1902951089872277763400949 178401664675526040318839)
                  ·
                    rfl

theorem cell22_1563462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1563462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563462 prefixEnd_1563462 := by exact prefixLift 1563462
  have htrace : WordTrace (prefixWord ++ tailWord_1563462) baseStart_1563462 baseEnd_1563462 := by
    simpa [prefixWord, tailWord_1563462, baseEnd_1563462] using wordTrace_append hprefix tailTrace_1563462
  have hstable : (prefixWord ++ tailWord_1563462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563462).length < 2 ^ (prefixWord ++ tailWord_1563462).sum := by decide
  have hdescent : baseEnd_1563462 < baseStart_1563462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563505 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_1563505 : Nat := 118140960795 + 1563505 * 2 ^ 59
def prefixEnd_1563505 : Nat := 4983230072969 + 3 ^ 40 * 1563505 * 2
def baseEnd_1563505 : Nat := 535219713805340342131385

theorem tailTrace_1563505 : CollatzResearch.WordTrace tailWord_1563505 prefixEnd_1563505 535219713805340342131385 := by
  unfold tailWord_1563505
  simp only [CollatzResearch.WordTrace]
  refine ⟨57025712200695885240131969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38017141467130590160087979 57025712200695885240131969)
  ·
    refine ⟨42769284150521913930098977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57025712200695885240131969 42769284150521913930098977)
    ·
      refine ⟨32076963112891435447574233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42769284150521913930098977 32076963112891435447574233)
      ·
        refine ⟨24057722334668576585680675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32076963112891435447574233 24057722334668576585680675)
        ·
          refine ⟨36086583502002864878521013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24057722334668576585680675 36086583502002864878521013)
          ·
            refine ⟨3383117203312768582361345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36086583502002864878521013 3383117203312768582361345)
            ·
              refine ⟨2537337902484576436771009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383117203312768582361345 2537337902484576436771009)
              ·
                refine ⟨1903003426863432327578257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537337902484576436771009 1903003426863432327578257)
                ·
                  refine ⟨1427252570147574245683693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1903003426863432327578257 1427252570147574245683693)
                  ·
                    refine ⟨535219713805340342131385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427252570147574245683693 535219713805340342131385)
                    ·
                      rfl

theorem cell22_1563505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_1563505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563505 prefixEnd_1563505 := by exact prefixLift 1563505
  have htrace : WordTrace (prefixWord ++ tailWord_1563505) baseStart_1563505 baseEnd_1563505 := by
    simpa [prefixWord, tailWord_1563505, baseEnd_1563505] using wordTrace_append hprefix tailTrace_1563505
  have hstable : (prefixWord ++ tailWord_1563505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563505).length < 2 ^ (prefixWord ++ tailWord_1563505).sum := by decide
  have hdescent : baseEnd_1563505 < baseStart_1563505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563561 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_1563561 : Nat := 118140960795 + 1563561 * 2 ^ 59
def prefixEnd_1563561 : Nat := 4983230072969 + 3 ^ 40 * 1563561 * 2
def baseEnd_1563561 : Nat := 535238883749774862731213

theorem tailTrace_1563561 : CollatzResearch.WordTrace tailWord_1563561 prefixEnd_1563561 535238883749774862731213 := by
  unfold tailWord_1563561
  simp only [CollatzResearch.WordTrace]
  refine ⟨57027754688493006804170537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38018503125662004536113691 57027754688493006804170537)
  ·
    refine ⟨42770816016369755103127903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57027754688493006804170537 42770816016369755103127903)
    ·
      refine ⟨64156224024554632654691855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42770816016369755103127903 64156224024554632654691855)
      ·
        refine ⟨96234336036831948982037783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64156224024554632654691855 96234336036831948982037783)
        ·
          refine ⟨144351504055247923473056675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96234336036831948982037783 144351504055247923473056675)
          ·
            refine ⟨216527256082871885209585013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144351504055247923473056675 216527256082871885209585013)
            ·
              refine ⟨20299430257769239238398595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216527256082871885209585013 20299430257769239238398595)
              ·
                refine ⟨30449145386653858857597893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20299430257769239238398595 30449145386653858857597893)
                ·
                  refine ⟨5709214759997598535799605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30449145386653858857597893 5709214759997598535799605)
                  ·
                    refine ⟨535238883749774862731213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5709214759997598535799605 535238883749774862731213)
                    ·
                      rfl

theorem cell22_1563561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_1563561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563561 prefixEnd_1563561 := by exact prefixLift 1563561
  have htrace : WordTrace (prefixWord ++ tailWord_1563561) baseStart_1563561 baseEnd_1563561 := by
    simpa [prefixWord, tailWord_1563561, baseEnd_1563561] using wordTrace_append hprefix tailTrace_1563561
  have hstable : (prefixWord ++ tailWord_1563561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563561).length < 2 ^ (prefixWord ++ tailWord_1563561).sum := by decide
  have hdescent : baseEnd_1563561 < baseStart_1563561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563610 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_1563610 : Nat := 118140960795 + 1563610 * 2 ^ 59
def prefixEnd_1563610 : Nat := 4983230072969 + 3 ^ 40 * 1563610 * 2
def baseEnd_1563610 : Nat := 535255657451155068256063

theorem tailTrace_1563610 : CollatzResearch.WordTrace tailWord_1563610 prefixEnd_1563610 535255657451155068256063 := by
  unfold tailWord_1563610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257385466328872043176071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38019694576876992115136189 14257385466328872043176071)
  ·
    refine ⟨21386078199493308064764107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14257385466328872043176071 21386078199493308064764107)
    ·
      refine ⟨32079117299239962097146161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21386078199493308064764107 32079117299239962097146161)
      ·
        refine ⟨24059337974429971572859621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32079117299239962097146161 24059337974429971572859621)
        ·
          refine ⟨4511125870205619669911179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24059337974429971572859621 4511125870205619669911179)
          ·
            refine ⟨6766688805308429504866769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4511125870205619669911179 6766688805308429504866769)
            ·
              refine ⟨5075016603981322128650077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6766688805308429504866769 5075016603981322128650077)
              ·
                refine ⟨1903131226492995798243779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5075016603981322128650077 1903131226492995798243779)
                ·
                  refine ⟨2854696839739493697365669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903131226492995798243779 2854696839739493697365669)
                  ·
                    refine ⟨535255657451155068256063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854696839739493697365669 535255657451155068256063)
                    ·
                      rfl

theorem cell22_1563610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_1563610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563610 prefixEnd_1563610 := by exact prefixLift 1563610
  have htrace : WordTrace (prefixWord ++ tailWord_1563610) baseStart_1563610 baseEnd_1563610 := by
    simpa [prefixWord, tailWord_1563610, baseEnd_1563610] using wordTrace_append hprefix tailTrace_1563610
  have hstable : (prefixWord ++ tailWord_1563610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563610).length < 2 ^ (prefixWord ++ tailWord_1563610).sum := by decide
  have hdescent : baseEnd_1563610 < baseStart_1563610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563655 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1563655 : Nat := 118140960795 + 1563655 * 2 ^ 59
def prefixEnd_1563655 : Nat := 4983230072969 + 3 ^ 40 * 1563655 * 2
def baseEnd_1563655 : Nat := 535271061870789950880925

theorem tailTrace_1563655 : CollatzResearch.WordTrace tailWord_1563655 prefixEnd_1563655 535271061870789950880925 := by
  unfold tailWord_1563655
  simp only [CollatzResearch.WordTrace]
  refine ⟨57031183150152460858092419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38020788766768307238728279 57031183150152460858092419)
  ·
    refine ⟨85546774725228691287138629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57031183150152460858092419 85546774725228691287138629)
    ·
      refine ⟨16040020260980379616338493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85546774725228691287138629 16040020260980379616338493)
      ·
        refine ⟨6015007597867642356126935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16040020260980379616338493 6015007597867642356126935)
        ·
          refine ⟨9022511396801463534190403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015007597867642356126935 9022511396801463534190403)
          ·
            refine ⟨13533767095202195301285605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022511396801463534190403 13533767095202195301285605)
            ·
              refine ⟨2537581330350411618991051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13533767095202195301285605 2537581330350411618991051)
              ·
                refine ⟨3806371995525617428486577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537581330350411618991051 3806371995525617428486577)
                ·
                  refine ⟨2854778996644213071364933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806371995525617428486577 2854778996644213071364933)
                  ·
                    refine ⟨535271061870789950880925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854778996644213071364933 535271061870789950880925)
                    ·
                      rfl

theorem cell22_1563655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1563655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563655 prefixEnd_1563655 := by exact prefixLift 1563655
  have htrace : WordTrace (prefixWord ++ tailWord_1563655) baseStart_1563655 baseEnd_1563655 := by
    simpa [prefixWord, tailWord_1563655, baseEnd_1563655] using wordTrace_append hprefix tailTrace_1563655
  have hstable : (prefixWord ++ tailWord_1563655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563655).length < 2 ^ (prefixWord ++ tailWord_1563655).sum := by decide
  have hdescent : baseEnd_1563655 < baseStart_1563655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563676 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 4]
def baseStart_1563676 : Nat := 118140960795 + 1563676 * 2 ^ 59
def prefixEnd_1563676 : Nat := 4983230072969 + 3 ^ 40 * 1563676 * 2
def baseEnd_1563676 : Nat := 178426083533317632035287

theorem tailTrace_1563676 : CollatzResearch.WordTrace tailWord_1563676 prefixEnd_1563676 178426083533317632035287 := by
  unfold tailWord_1563676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28515974541538190722303441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38021299388717587629737921 28515974541538190722303441)
  ·
    refine ⟨21386980906153643041727581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28515974541538190722303441 21386980906153643041727581)
    ·
      refine ⟨8020117839807616140647843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21386980906153643041727581 8020117839807616140647843)
      ·
        refine ⟨12030176759711424210971765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8020117839807616140647843 12030176759711424210971765)
        ·
          refine ⟨1127829071222946019778603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12030176759711424210971765 1127829071222946019778603)
          ·
            refine ⟨1691743606834419029667905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127829071222946019778603 1691743606834419029667905)
            ·
              refine ⟨1268807705125814272250929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691743606834419029667905 1268807705125814272250929)
              ·
                refine ⟨951605778844360704188197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268807705125814272250929 951605778844360704188197)
                ·
                  refine ⟨178426083533317632035287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951605778844360704188197 178426083533317632035287)
                  ·
                    rfl

theorem cell22_1563676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_1563676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563676 prefixEnd_1563676 := by exact prefixLift 1563676
  have htrace : WordTrace (prefixWord ++ tailWord_1563676) baseStart_1563676 baseEnd_1563676 := by
    simpa [prefixWord, tailWord_1563676, baseEnd_1563676] using wordTrace_append hprefix tailTrace_1563676
  have hstable : (prefixWord ++ tailWord_1563676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563676).length < 2 ^ (prefixWord ++ tailWord_1563676).sum := by decide
  have hdescent : baseEnd_1563676 < baseStart_1563676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563683 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_1563683 : Nat := 118140960795 + 1563683 * 2 ^ 59
def prefixEnd_1563683 : Nat := 4983230072969 + 3 ^ 40 * 1563683 * 2
def baseEnd_1563683 : Nat := 535280646843007211180839

theorem tailTrace_1563683 : CollatzResearch.WordTrace tailWord_1563683 prefixEnd_1563683 535280646843007211180839 := by
  unfold tailWord_1563683
  simp only [CollatzResearch.WordTrace]
  refine ⟨57032204394051021640111703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38021469596034014426741135 57032204394051021640111703)
  ·
    refine ⟨85548306591076532460167555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57032204394051021640111703 85548306591076532460167555)
    ·
      refine ⟨128322459886614798690251333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85548306591076532460167555 128322459886614798690251333)
      ·
        refine ⟨24060461228740274754422125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128322459886614798690251333 24060461228740274754422125)
        ·
          refine ⟨9022672960777603032908297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24060461228740274754422125 9022672960777603032908297)
          ·
            refine ⟨6767004720583202274681223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9022672960777603032908297 6767004720583202274681223)
            ·
              refine ⟨10150507080874803412021835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767004720583202274681223 10150507080874803412021835)
              ·
                refine ⟨15225760621312205118032753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150507080874803412021835 15225760621312205118032753)
                ·
                  refine ⟨11419320465984153838524565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15225760621312205118032753 11419320465984153838524565)
                  ·
                    refine ⟨535280646843007211180839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11419320465984153838524565 535280646843007211180839)
                    ·
                      rfl

theorem cell22_1563683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_1563683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563683 prefixEnd_1563683 := by exact prefixLift 1563683
  have htrace : WordTrace (prefixWord ++ tailWord_1563683) baseStart_1563683 baseEnd_1563683 := by
    simpa [prefixWord, tailWord_1563683, baseEnd_1563683] using wordTrace_append hprefix tailTrace_1563683
  have hstable : (prefixWord ++ tailWord_1563683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563683).length < 2 ^ (prefixWord ++ tailWord_1563683).sum := by decide
  have hdescent : baseEnd_1563683 < baseStart_1563683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563685 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_1563685 : Nat := 118140960795 + 1563685 * 2 ^ 59
def prefixEnd_1563685 : Nat := 4983230072969 + 3 ^ 40 * 1563685 * 2
def baseEnd_1563685 : Nat := 535281331483879872630833

theorem tailTrace_1563685 : CollatzResearch.WordTrace tailWord_1563685 prefixEnd_1563685 535281331483879872630833 := by
  unfold tailWord_1563685
  simp only [CollatzResearch.WordTrace]
  refine ⟨57032277340043775981684509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38021518226695850654456339 57032277340043775981684509)
  ·
    refine ⟨21387104002516415993131691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57032277340043775981684509 21387104002516415993131691)
    ·
      refine ⟨32080656003774623989697537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21387104002516415993131691 32080656003774623989697537)
      ·
        refine ⟨24060492002830967992273153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32080656003774623989697537 24060492002830967992273153)
        ·
          refine ⟨18045369002123225994204865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24060492002830967992273153 18045369002123225994204865)
          ·
            refine ⟨13534026751592419495653649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18045369002123225994204865 13534026751592419495653649)
            ·
              refine ⟨10150520063694314621740237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13534026751592419495653649 10150520063694314621740237)
              ·
                refine ⟨3806445023885367983152589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10150520063694314621740237 3806445023885367983152589)
                ·
                  refine ⟨1427416883957012993682221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3806445023885367983152589 1427416883957012993682221)
                  ·
                    refine ⟨535281331483879872630833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427416883957012993682221 535281331483879872630833)
                    ·
                      rfl

theorem cell22_1563685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_1563685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563685 prefixEnd_1563685 := by exact prefixLift 1563685
  have htrace : WordTrace (prefixWord ++ tailWord_1563685) baseStart_1563685 baseEnd_1563685 := by
    simpa [prefixWord, tailWord_1563685, baseEnd_1563685] using wordTrace_append hprefix tailTrace_1563685
  have hstable : (prefixWord ++ tailWord_1563685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563685).length < 2 ^ (prefixWord ++ tailWord_1563685).sum := by decide
  have hdescent : baseEnd_1563685 < baseStart_1563685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563687 : List Nat := [1, 1, 7, 1, 1, 3, 1, 7]
def baseStart_1563687 : Nat := 118140960795 + 1563687 * 2 ^ 59
def prefixEnd_1563687 : Nat := 4983230072969 + 3 ^ 40 * 1563687 * 2
def baseEnd_1563687 : Nat := 59475779569416948231203

theorem tailTrace_1563687 : CollatzResearch.WordTrace tailWord_1563687 prefixEnd_1563687 59475779569416948231203 := by
  unfold tailWord_1563687
  simp only [CollatzResearch.WordTrace]
  refine ⟨57032350286036530323257315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38021566857357686882171543 57032350286036530323257315)
  ·
    refine ⟨85548525429054795484885973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57032350286036530323257315 85548525429054795484885973)
    ·
      refine ⟨2005043564743471769177015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85548525429054795484885973 2005043564743471769177015)
      ·
        refine ⟨3007565347115207653765523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005043564743471769177015 3007565347115207653765523)
        ·
          refine ⟨4511348020672811480648285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007565347115207653765523 4511348020672811480648285)
          ·
            refine ⟨1691755507752304305243107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4511348020672811480648285 1691755507752304305243107)
            ·
              refine ⟨2537633261628456457864661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691755507752304305243107 2537633261628456457864661)
              ·
                refine ⟨59475779569416948231203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2537633261628456457864661 59475779569416948231203)
                ·
                  rfl

theorem cell22_1563687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 7].length) (baseStart_1563687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563687 prefixEnd_1563687 := by exact prefixLift 1563687
  have htrace : WordTrace (prefixWord ++ tailWord_1563687) baseStart_1563687 baseEnd_1563687 := by
    simpa [prefixWord, tailWord_1563687, baseEnd_1563687] using wordTrace_append hprefix tailTrace_1563687
  have hstable : (prefixWord ++ tailWord_1563687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563687).length < 2 ^ (prefixWord ++ tailWord_1563687).sum := by decide
  have hdescent : baseEnd_1563687 < baseStart_1563687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563702 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1563702 : Nat := 118140960795 + 1563702 * 2 ^ 59
def prefixEnd_1563702 : Nat := 4983230072969 + 3 ^ 40 * 1563702 * 2
def baseEnd_1563702 : Nat := 535287150931297494955781

theorem tailTrace_1563702 : CollatzResearch.WordTrace tailWord_1563702 prefixEnd_1563702 535287150931297494955781 := by
  unfold tailWord_1563702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3564556086311386742815835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38021931587321458590035573 3564556086311386742815835)
  ·
    refine ⟨5346834129467080114223753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3564556086311386742815835 5346834129467080114223753)
    ·
      refine ⟨4010125597100310085667815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5346834129467080114223753 4010125597100310085667815)
      ·
        refine ⟨6015188395650465128501723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010125597100310085667815 6015188395650465128501723)
        ·
          refine ⟨9022782593475697692752585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015188395650465128501723 9022782593475697692752585)
          ·
            refine ⟨6767086945106773269564439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9022782593475697692752585 6767086945106773269564439)
            ·
              refine ⟨10150630417660159904346659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767086945106773269564439 10150630417660159904346659)
              ·
                refine ⟨15225945626490239856519989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150630417660159904346659 15225945626490239856519989)
                ·
                  refine ⟨1427432402483459986548749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15225945626490239856519989 1427432402483459986548749)
                  ·
                    refine ⟨535287150931297494955781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427432402483459986548749 535287150931297494955781)
                    ·
                      rfl

theorem cell22_1563702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1563702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563702 prefixEnd_1563702 := by exact prefixLift 1563702
  have htrace : WordTrace (prefixWord ++ tailWord_1563702) baseStart_1563702 baseEnd_1563702 := by
    simpa [prefixWord, tailWord_1563702, baseEnd_1563702] using wordTrace_append hprefix tailTrace_1563702
  have hstable : (prefixWord ++ tailWord_1563702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563702).length < 2 ^ (prefixWord ++ tailWord_1563702).sum := by decide
  have hdescent : baseEnd_1563702 < baseStart_1563702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563719 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 1, 3]
def baseStart_1563719 : Nat := 118140960795 + 1563719 * 2 ^ 59
def prefixEnd_1563719 : Nat := 4983230072969 + 3 ^ 40 * 1563719 * 2
def baseEnd_1563719 : Nat := 535292970378715117280729

theorem tailTrace_1563719 : CollatzResearch.WordTrace tailWord_1563719 prefixEnd_1563719 535292970378715117280729 := by
  unfold tailWord_1563719
  simp only [CollatzResearch.WordTrace]
  refine ⟨57033517421920599788422211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38022344947947066525614807 57033517421920599788422211)
  ·
    refine ⟨85550276132880899682633317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57033517421920599788422211 85550276132880899682633317)
    ·
      refine ⟨16040676774915168690493747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85550276132880899682633317 16040676774915168690493747)
      ·
        refine ⟨24061015162372753035740621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16040676774915168690493747 24061015162372753035740621)
        ·
          refine ⟨9022880685889782388402733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24061015162372753035740621 9022880685889782388402733)
          ·
            refine ⟨3383580257208668395651025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9022880685889782388402733 3383580257208668395651025)
            ·
              refine ⟨2537685192906501296738269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383580257208668395651025 2537685192906501296738269)
              ·
                refine ⟨951631947339937986276851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2537685192906501296738269 951631947339937986276851)
                ·
                  refine ⟨1427447921009906979415277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951631947339937986276851 1427447921009906979415277)
                  ·
                    refine ⟨535292970378715117280729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427447921009906979415277 535292970378715117280729)
                    ·
                      rfl

theorem cell22_1563719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_1563719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563719 prefixEnd_1563719 := by exact prefixLift 1563719
  have htrace : WordTrace (prefixWord ++ tailWord_1563719) baseStart_1563719 baseEnd_1563719 := by
    simpa [prefixWord, tailWord_1563719, baseEnd_1563719] using wordTrace_append hprefix tailTrace_1563719
  have hstable : (prefixWord ++ tailWord_1563719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563719).length < 2 ^ (prefixWord ++ tailWord_1563719).sum := by decide
  have hdescent : baseEnd_1563719 < baseStart_1563719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563730 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1563730 : Nat := 118140960795 + 1563730 * 2 ^ 59
def prefixEnd_1563730 : Nat := 4983230072969 + 3 ^ 40 * 1563730 * 2
def baseEnd_1563730 : Nat := 535296735903514755255695

theorem tailTrace_1563730 : CollatzResearch.WordTrace tailWord_1563730 prefixEnd_1563730 535296735903514755255695 := by
  unfold tailWord_1563730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14258479656220187166768161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38022612416587165778048429 14258479656220187166768161)
  ·
    refine ⟨10693859742165140375076121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14258479656220187166768161 10693859742165140375076121)
    ·
      refine ⟨8020394806623855281307091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10693859742165140375076121 8020394806623855281307091)
      ·
        refine ⟨12030592209935782921960637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8020394806623855281307091 12030592209935782921960637)
        ·
          refine ⟨4511472078725918595735239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12030592209935782921960637 4511472078725918595735239)
          ·
            refine ⟨6767208118088877893602859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4511472078725918595735239 6767208118088877893602859)
            ·
              refine ⟨10150812177133316840404289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767208118088877893602859 10150812177133316840404289)
              ·
                refine ⟨7613109132849987630303217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10150812177133316840404289 7613109132849987630303217)
                ·
                  refine ⟨5709831849637490722727413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613109132849987630303217 5709831849637490722727413)
                  ·
                    refine ⟨535296735903514755255695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5709831849637490722727413 535296735903514755255695)
                    ·
                      rfl

theorem cell22_1563730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1563730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563730 prefixEnd_1563730 := by exact prefixLift 1563730
  have htrace : WordTrace (prefixWord ++ tailWord_1563730) baseStart_1563730 baseEnd_1563730 := by
    simpa [prefixWord, tailWord_1563730, baseEnd_1563730] using wordTrace_append hprefix tailTrace_1563730
  have hstable : (prefixWord ++ tailWord_1563730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563730).length < 2 ^ (prefixWord ++ tailWord_1563730).sum := by decide
  have hdescent : baseEnd_1563730 < baseStart_1563730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563762 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1563762 : Nat := 118140960795 + 1563762 * 2 ^ 59
def prefixEnd_1563762 : Nat := 4983230072969 + 3 ^ 40 * 1563762 * 2
def baseEnd_1563762 : Nat := 535307690157477338455597

theorem tailTrace_1563762 : CollatzResearch.WordTrace tailWord_1563762 prefixEnd_1563762 535307690157477338455597 := by
  unfold tailWord_1563762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14258771440191204533059385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38023390507176545421491693 14258771440191204533059385)
  ·
    refine ⟨10694078580143403399794539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14258771440191204533059385 10694078580143403399794539)
    ·
      refine ⟨16041117870215105099691809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10694078580143403399794539 16041117870215105099691809)
      ·
        refine ⟨12030838402661328824768857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16041117870215105099691809 12030838402661328824768857)
        ·
          refine ⟨9023128801995996618576643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12030838402661328824768857 9023128801995996618576643)
          ·
            refine ⟨13534693202993994927864965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9023128801995996618576643 13534693202993994927864965)
            ·
              refine ⟨2537754975561374048974681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13534693202993994927864965 2537754975561374048974681)
              ·
                refine ⟨1903316231671030536731011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537754975561374048974681 1903316231671030536731011)
                ·
                  refine ⟨2854974347506545805096517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903316231671030536731011 2854974347506545805096517)
                  ·
                    refine ⟨535307690157477338455597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854974347506545805096517 535307690157477338455597)
                    ·
                      rfl

theorem cell22_1563762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1563762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563762 prefixEnd_1563762 := by exact prefixLift 1563762
  have htrace : WordTrace (prefixWord ++ tailWord_1563762) baseStart_1563762 baseEnd_1563762 := by
    simpa [prefixWord, tailWord_1563762, baseEnd_1563762] using wordTrace_append hprefix tailTrace_1563762
  have hstable : (prefixWord ++ tailWord_1563762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563762).length < 2 ^ (prefixWord ++ tailWord_1563762).sum := by decide
  have hdescent : baseEnd_1563762 < baseStart_1563762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_1563803 : Nat := 118140960795 + 1563803 * 2 ^ 59
def prefixEnd_1563803 : Nat := 4983230072969 + 3 ^ 40 * 1563803 * 2
def baseEnd_1563803 : Nat := 535321725295366898180471

theorem tailTrace_1563803 : CollatzResearch.WordTrace tailWord_1563803 prefixEnd_1563803 535321725295366898180471 := by
  unfold tailWord_1563803
  simp only [CollatzResearch.WordTrace]
  refine ⟨57036581153616282134480063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38024387435744188089653375 57036581153616282134480063)
  ·
    refine ⟨85554871730424423201720095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57036581153616282134480063 85554871730424423201720095)
    ·
      refine ⟨128332307595636634802580143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85554871730424423201720095 128332307595636634802580143)
      ·
        refine ⟨192498461393454952203870215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128332307595636634802580143 192498461393454952203870215)
        ·
          refine ⟨288747692090182428305805323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192498461393454952203870215 288747692090182428305805323)
          ·
            refine ⟨433121538135273642458707985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288747692090182428305805323 433121538135273642458707985)
            ·
              refine ⟨324841153601455231844030989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433121538135273642458707985 324841153601455231844030989)
              ·
                refine ⟨121815432600545711941511621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324841153601455231844030989 121815432600545711941511621)
                ·
                  refine ⟨22840393612602320989033429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121815432600545711941511621 22840393612602320989033429)
                  ·
                    refine ⟨535321725295366898180471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22840393612602320989033429 535321725295366898180471)
                    ·
                      rfl

theorem cell22_1563803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_1563803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563803 prefixEnd_1563803 := by exact prefixLift 1563803
  have htrace : WordTrace (prefixWord ++ tailWord_1563803) baseStart_1563803 baseEnd_1563803 := by
    simpa [prefixWord, tailWord_1563803, baseEnd_1563803] using wordTrace_append hprefix tailTrace_1563803
  have hstable : (prefixWord ++ tailWord_1563803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563803).length < 2 ^ (prefixWord ++ tailWord_1563803).sum := by decide
  have hdescent : baseEnd_1563803 < baseStart_1563803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563805 : List Nat := [1, 4, 2, 1, 1, 2, 4, 7]
def baseStart_1563805 : Nat := 118140960795 + 1563805 * 2 ^ 59
def prefixEnd_1563805 : Nat := 4983230072969 + 3 ^ 40 * 1563805 * 2
def baseEnd_1563805 : Nat := 59480267770693284403385

theorem tailTrace_1563805 : CollatzResearch.WordTrace tailWord_1563805 prefixEnd_1563805 59480267770693284403385 := by
  unfold tailWord_1563805
  simp only [CollatzResearch.WordTrace]
  refine ⟨57036654099609036476052869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38024436066406024317368579 57036654099609036476052869)
  ·
    refine ⟨10694372643676694339259913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57036654099609036476052869 10694372643676694339259913)
    ·
      refine ⟨8020779482757520754444935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10694372643676694339259913 8020779482757520754444935)
      ·
        refine ⟨12031169224136281131667403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8020779482757520754444935 12031169224136281131667403)
        ·
          refine ⟨18046753836204421697501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12031169224136281131667403 18046753836204421697501105)
          ·
            refine ⟨13535065377153316273125829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18046753836204421697501105 13535065377153316273125829)
            ·
              refine ⟨2537824758216246801211093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13535065377153316273125829 2537824758216246801211093)
              ·
                refine ⟨59480267770693284403385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2537824758216246801211093 59480267770693284403385)
                ·
                  rfl

theorem cell22_1563805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 7].length) (baseStart_1563805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563805 prefixEnd_1563805 := by exact prefixLift 1563805
  have htrace : WordTrace (prefixWord ++ tailWord_1563805) baseStart_1563805 baseEnd_1563805 := by
    simpa [prefixWord, tailWord_1563805, baseEnd_1563805] using wordTrace_append hprefix tailTrace_1563805
  have hstable : (prefixWord ++ tailWord_1563805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563805).length < 2 ^ (prefixWord ++ tailWord_1563805).sum := by decide
  have hdescent : baseEnd_1563805 < baseStart_1563805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563897 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_1563897 : Nat := 118140960795 + 1563897 * 2 ^ 59
def prefixEnd_1563897 : Nat := 4983230072969 + 3 ^ 40 * 1563897 * 2
def baseEnd_1563897 : Nat := 535353903416381986330183

theorem tailTrace_1563897 : CollatzResearch.WordTrace tailWord_1563897 prefixEnd_1563897 535353903416381986330183 := by
  unfold tailWord_1563897
  simp only [CollatzResearch.WordTrace]
  refine ⟨57040009615275736188401945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38026673076850490792267963 57040009615275736188401945)
  ·
    refine ⟨42780007211456802141301459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57040009615275736188401945 42780007211456802141301459)
    ·
      refine ⟨64170010817185203211952189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42780007211456802141301459 64170010817185203211952189)
      ·
        refine ⟨24063754056444451204482071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64170010817185203211952189 24063754056444451204482071)
        ·
          refine ⟨36095631084666676806723107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24063754056444451204482071 36095631084666676806723107)
          ·
            refine ⟨54143446627000015210084661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36095631084666676806723107 54143446627000015210084661)
            ·
              refine ⟨5075948121281251425945437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54143446627000015210084661 5075948121281251425945437)
              ·
                refine ⟨1903480545480469284729539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5075948121281251425945437 1903480545480469284729539)
                ·
                  refine ⟨2855220818220703927094309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903480545480469284729539 2855220818220703927094309)
                  ·
                    refine ⟨535353903416381986330183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2855220818220703927094309 535353903416381986330183)
                    ·
                      rfl

theorem cell22_1563897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_1563897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563897 prefixEnd_1563897 := by exact prefixLift 1563897
  have htrace : WordTrace (prefixWord ++ tailWord_1563897) baseStart_1563897 baseEnd_1563897 := by
    simpa [prefixWord, tailWord_1563897, baseEnd_1563897] using wordTrace_append hprefix tailTrace_1563897
  have hstable : (prefixWord ++ tailWord_1563897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563897).length < 2 ^ (prefixWord ++ tailWord_1563897).sum := by decide
  have hdescent : baseEnd_1563897 < baseStart_1563897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563944 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1563944 : Nat := 118140960795 + 1563944 * 2 ^ 59
def prefixEnd_1563944 : Nat := 4983230072969 + 3 ^ 40 * 1563944 * 2
def baseEnd_1563944 : Nat := 535369992476889530405039

theorem tailTrace_1563944 : CollatzResearch.WordTrace tailWord_1563944 prefixEnd_1563944 535369992476889530405039 := by
  unfold tailWord_1563944
  simp only [CollatzResearch.WordTrace]
  refine ⟨28520861923052731607681443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38027815897403642143575257 28520861923052731607681443)
  ·
    refine ⟨42781292884579097411522165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28520861923052731607681443 42781292884579097411522165)
    ·
      refine ⟨4010746207929290382330203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42781292884579097411522165 4010746207929290382330203)
      ·
        refine ⟨6016119311893935573495305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010746207929290382330203 6016119311893935573495305)
        ·
          refine ⟨4512089483920451680121479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6016119311893935573495305 4512089483920451680121479)
          ·
            refine ⟨6768134225880677520182219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512089483920451680121479 6768134225880677520182219)
            ·
              refine ⟨10152201338821016280273329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768134225880677520182219 10152201338821016280273329)
              ·
                refine ⟨7614151004115762210204997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10152201338821016280273329 7614151004115762210204997)
                ·
                  refine ⟨1427653313271705414413437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7614151004115762210204997 1427653313271705414413437)
                  ·
                    refine ⟨535369992476889530405039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427653313271705414413437 535369992476889530405039)
                    ·
                      rfl

theorem cell22_1563944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1563944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563944 prefixEnd_1563944 := by exact prefixLift 1563944
  have htrace : WordTrace (prefixWord ++ tailWord_1563944) baseStart_1563944 baseEnd_1563944 := by
    simpa [prefixWord, tailWord_1563944, baseEnd_1563944] using wordTrace_append hprefix tailTrace_1563944
  have hstable : (prefixWord ++ tailWord_1563944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563944).length < 2 ^ (prefixWord ++ tailWord_1563944).sum := by decide
  have hdescent : baseEnd_1563944 < baseStart_1563944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563946 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_1563946 : Nat := 118140960795 + 1563946 * 2 ^ 59
def prefixEnd_1563946 : Nat := 4983230072969 + 3 ^ 40 * 1563946 * 2
def baseEnd_1563946 : Nat := 178456892372587397285011

theorem tailTrace_1563946 : CollatzResearch.WordTrace tailWord_1563946 prefixEnd_1563946 178456892372587397285011 := by
  unfold tailWord_1563946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260449198024554389233923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38027864528065478371290461 14260449198024554389233923)
  ·
    refine ⟨21390673797036831583850885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14260449198024554389233923 21390673797036831583850885)
    ·
      refine ⟨4010751336944405921972041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21390673797036831583850885 4010751336944405921972041)
      ·
        refine ⟨3008063502708304441479031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4010751336944405921972041 3008063502708304441479031)
        ·
          refine ⟨4512095254062456662218547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008063502708304441479031 4512095254062456662218547)
          ·
            refine ⟨6768142881093684993327821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512095254062456662218547 6768142881093684993327821)
            ·
              refine ⟨2538053580410131872497933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6768142881093684993327821 2538053580410131872497933)
              ·
                refine ⟨951770092653799452186725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2538053580410131872497933 951770092653799452186725)
                ·
                  refine ⟨178456892372587397285011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951770092653799452186725 178456892372587397285011)
                  ·
                    rfl

theorem cell22_1563946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_1563946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563946 prefixEnd_1563946 := by exact prefixLift 1563946
  have htrace : WordTrace (prefixWord ++ tailWord_1563946) baseStart_1563946 baseEnd_1563946 := by
    simpa [prefixWord, tailWord_1563946, baseEnd_1563946] using wordTrace_append hprefix tailTrace_1563946
  have hstable : (prefixWord ++ tailWord_1563946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563946).length < 2 ^ (prefixWord ++ tailWord_1563946).sum := by decide
  have hdescent : baseEnd_1563946 < baseStart_1563946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563957 : List Nat := [1, 3, 3, 1, 2, 4, 8]
def baseStart_1563957 : Nat := 118140960795 + 1563957 * 2 ^ 59
def prefixEnd_1563957 : Nat := 4983230072969 + 3 ^ 40 * 1563957 * 2
def baseEnd_1563957 : Nat := 19828683060835623327037

theorem tailTrace_1563957 : CollatzResearch.WordTrace tailWord_1563957 prefixEnd_1563957 19828683060835623327037 := by
  unfold tailWord_1563957
  simp only [CollatzResearch.WordTrace]
  refine ⟨57042197995058366435586125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38028131996705577623724083 57042197995058366435586125)
  ·
    refine ⟨21390824248146887413344797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57042197995058366435586125 21390824248146887413344797)
    ·
      refine ⟨8021559093055082780004299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21390824248146887413344797 8021559093055082780004299)
      ·
        refine ⟨12032338639582624170006449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8021559093055082780004299 12032338639582624170006449)
        ·
          refine ⟨9024253979686968127504837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12032338639582624170006449 9024253979686968127504837)
          ·
            refine ⟨1692047621191306523907157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9024253979686968127504837 1692047621191306523907157)
            ·
              refine ⟨19828683060835623327037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1692047621191306523907157 19828683060835623327037)
              ·
                rfl

theorem cell22_1563957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 8].length) (baseStart_1563957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1563957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1563957 prefixEnd_1563957 := by exact prefixLift 1563957
  have htrace : WordTrace (prefixWord ++ tailWord_1563957) baseStart_1563957 baseEnd_1563957 := by
    simpa [prefixWord, tailWord_1563957, baseEnd_1563957] using wordTrace_append hprefix tailTrace_1563957
  have hstable : (prefixWord ++ tailWord_1563957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563957).length < 2 ^ (prefixWord ++ tailWord_1563957).sum := by decide
  have hdescent : baseEnd_1563957 < baseStart_1563957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564066 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1564066 : Nat := 118140960795 + 1564066 * 2 ^ 59
def prefixEnd_1564066 : Nat := 4983230072969 + 3 ^ 40 * 1564066 * 2
def baseEnd_1564066 : Nat := 535411755570121878854665

theorem tailTrace_1564066 : CollatzResearch.WordTrace tailWord_1564066 prefixEnd_1564066 535411755570121878854665 := by
  unfold tailWord_1564066
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261543387915869512826013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38030782367775652034202701 14261543387915869512826013)
  ·
    refine ⟨5348078770468451067309755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14261543387915869512826013 5348078770468451067309755)
    ·
      refine ⟨8022118155702676600964633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348078770468451067309755 8022118155702676600964633)
      ·
        refine ⟨6016588616777007450723475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8022118155702676600964633 6016588616777007450723475)
        ·
          refine ⟨9024882925165511176085213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016588616777007450723475 9024882925165511176085213)
          ·
            refine ⟨3384331096937066691031955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9024882925165511176085213 3384331096937066691031955)
            ·
              refine ⟨5076496645405600036547933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384331096937066691031955 5076496645405600036547933)
              ·
                refine ⟨1903686242027100013705475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5076496645405600036547933 1903686242027100013705475)
                ·
                  refine ⟨2855529363040650020558213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903686242027100013705475 2855529363040650020558213)
                  ·
                    refine ⟨535411755570121878854665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2855529363040650020558213 535411755570121878854665)
                    ·
                      rfl

theorem cell22_1564066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1564066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564066 prefixEnd_1564066 := by exact prefixLift 1564066
  have htrace : WordTrace (prefixWord ++ tailWord_1564066) baseStart_1564066 baseEnd_1564066 := by
    simpa [prefixWord, tailWord_1564066, baseEnd_1564066] using wordTrace_append hprefix tailTrace_1564066
  have hstable : (prefixWord ++ tailWord_1564066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564066).length < 2 ^ (prefixWord ++ tailWord_1564066).sum := by decide
  have hdescent : baseEnd_1564066 < baseStart_1564066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564154 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_1564154 : Nat := 118140960795 + 1564154 * 2 ^ 59
def prefixEnd_1564154 : Nat := 4983230072969 + 3 ^ 40 * 1564154 * 2
def baseEnd_1564154 : Nat := 178480626589506327551465

theorem tailTrace_1564154 : CollatzResearch.WordTrace tailWord_1564154 prefixEnd_1564154 178480626589506327551465 := by
  unfold tailWord_1564154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262345793836167270126879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38032922116896446053671677 14262345793836167270126879)
  ·
    refine ⟨21393518690754250905190319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14262345793836167270126879 21393518690754250905190319)
    ·
      refine ⟨32090278036131376357785479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21393518690754250905190319 32090278036131376357785479)
      ·
        refine ⟨48135417054197064536678219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32090278036131376357785479 48135417054197064536678219)
        ·
          refine ⟨72203125581295596805017329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48135417054197064536678219 72203125581295596805017329)
          ·
            refine ⟨54152344185971697603762997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72203125581295596805017329 54152344185971697603762997)
            ·
              refine ⟨5076782267434846650352781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54152344185971697603762997 5076782267434846650352781)
              ·
                refine ⟨1903793350288067493882293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5076782267434846650352781 1903793350288067493882293)
                ·
                  refine ⟨178480626589506327551465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1903793350288067493882293 178480626589506327551465)
                  ·
                    rfl

theorem cell22_1564154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_1564154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564154 prefixEnd_1564154 := by exact prefixLift 1564154
  have htrace : WordTrace (prefixWord ++ tailWord_1564154) baseStart_1564154 baseEnd_1564154 := by
    simpa [prefixWord, tailWord_1564154, baseEnd_1564154] using wordTrace_append hprefix tailTrace_1564154
  have hstable : (prefixWord ++ tailWord_1564154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564154).length < 2 ^ (prefixWord ++ tailWord_1564154).sum := by decide
  have hdescent : baseEnd_1564154 < baseStart_1564154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564192 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 1, 3]
def baseStart_1564192 : Nat := 118140960795 + 1564192 * 2 ^ 59
def prefixEnd_1564192 : Nat := 4983230072969 + 3 ^ 40 * 1564192 * 2
def baseEnd_1564192 : Nat := 535454887945099550204279

theorem tailTrace_1564192 : CollatzResearch.WordTrace tailWord_1564192 prefixEnd_1564192 535454887945099550204279 := by
  unfold tailWord_1564192
  simp only [CollatzResearch.WordTrace]
  refine ⟨28525384574603500785195415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38033846099471334380260553 28525384574603500785195415)
  ·
    refine ⟨42788076861905251177793123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28525384574603500785195415 42788076861905251177793123)
    ·
      refine ⟨64182115292857876766689685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42788076861905251177793123 64182115292857876766689685)
      ·
        refine ⟨3008536654352712973438579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64182115292857876766689685 3008536654352712973438579)
        ·
          refine ⟨4512804981529069460157869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008536654352712973438579 4512804981529069460157869)
          ·
            refine ⟨1692301868073401047559201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4512804981529069460157869 1692301868073401047559201)
            ·
              refine ⟨1269226401055050785669401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692301868073401047559201 1269226401055050785669401)
              ·
                refine ⟨951919800791288089252051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269226401055050785669401 951919800791288089252051)
                ·
                  refine ⟨1427879701186932133878077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951919800791288089252051 1427879701186932133878077)
                  ·
                    refine ⟨535454887945099550204279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427879701186932133878077 535454887945099550204279)
                    ·
                      rfl

theorem cell22_1564192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_1564192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564192 prefixEnd_1564192 := by exact prefixLift 1564192
  have htrace : WordTrace (prefixWord ++ tailWord_1564192) baseStart_1564192 baseEnd_1564192 := by
    simpa [prefixWord, tailWord_1564192, baseEnd_1564192] using wordTrace_append hprefix tailTrace_1564192
  have hstable : (prefixWord ++ tailWord_1564192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564192).length < 2 ^ (prefixWord ++ tailWord_1564192).sum := by decide
  have hdescent : baseEnd_1564192 < baseStart_1564192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564229 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_1564229 : Nat := 118140960795 + 1564229 * 2 ^ 59
def prefixEnd_1564229 : Nat := 4983230072969 + 3 ^ 40 * 1564229 * 2
def baseEnd_1564229 : Nat := 535467553801243787029165

theorem tailTrace_1564229 : CollatzResearch.WordTrace tailWord_1564229 prefixEnd_1564229 535467553801243787029165 := by
  unfold tailWord_1564229
  simp only [CollatzResearch.WordTrace]
  refine ⟨57052118650072956889487741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38034745766715304592991827 57052118650072956889487741)
  ·
    refine ⟨21394544493777358833557903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57052118650072956889487741 21394544493777358833557903)
    ·
      refine ⟨32091816740666038250336855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21394544493777358833557903 32091816740666038250336855)
      ·
        refine ⟨48137725110999057375505283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32091816740666038250336855 48137725110999057375505283)
        ·
          refine ⟨72206587666498586063257925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48137725110999057375505283 72206587666498586063257925)
          ·
            refine ⟨13538735187468484886860861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72206587666498586063257925 13538735187468484886860861)
            ·
              refine ⟨5077025695300681832572823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13538735187468484886860861 5077025695300681832572823)
              ·
                refine ⟨7615538542951022748859235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077025695300681832572823 7615538542951022748859235)
                ·
                  refine ⟨11423307814426534123288853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7615538542951022748859235 11423307814426534123288853)
                  ·
                    refine ⟨535467553801243787029165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11423307814426534123288853 535467553801243787029165)
                    ·
                      rfl

theorem cell22_1564229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_1564229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564229 prefixEnd_1564229 := by exact prefixLift 1564229
  have htrace : WordTrace (prefixWord ++ tailWord_1564229) baseStart_1564229 baseEnd_1564229 := by
    simpa [prefixWord, tailWord_1564229, baseEnd_1564229] using wordTrace_append hprefix tailTrace_1564229
  have hstable : (prefixWord ++ tailWord_1564229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564229).length < 2 ^ (prefixWord ++ tailWord_1564229).sum := by decide
  have hdescent : baseEnd_1564229 < baseStart_1564229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564244 : List Nat := [2, 4, 1, 1, 1, 2, 11]
def baseStart_1564244 : Nat := 118140960795 + 1564244 * 2 ^ 59
def prefixEnd_1564244 : Nat := 4983230072969 + 3 ^ 40 * 1564244 * 2
def baseEnd_1564244 : Nat := 19832321800288472144597

theorem tailTrace_1564244 : CollatzResearch.WordTrace tailWord_1564244 prefixEnd_1564244 19832321800288472144597 := by
  unfold tailWord_1564244
  simp only [CollatzResearch.WordTrace]
  refine ⟨28526332872509307225641893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38035110496679076300855857 28526332872509307225641893)
  ·
    refine ⟨5348687413595495104807855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28526332872509307225641893 5348687413595495104807855)
    ·
      refine ⟨8023031120393242657211783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348687413595495104807855 8023031120393242657211783)
      ·
        refine ⟨12034546680589863985817675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023031120393242657211783 12034546680589863985817675)
        ·
          refine ⟨18051820020884795978726513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12034546680589863985817675 18051820020884795978726513)
          ·
            refine ⟨13538865015663596984044885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18051820020884795978726513 13538865015663596984044885)
            ·
              refine ⟨19832321800288472144597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13538865015663596984044885 19832321800288472144597)
              ·
                rfl

theorem cell22_1564244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 11].length) (baseStart_1564244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564244 prefixEnd_1564244 := by exact prefixLift 1564244
  have htrace : WordTrace (prefixWord ++ tailWord_1564244) baseStart_1564244 baseEnd_1564244 := by
    simpa [prefixWord, tailWord_1564244, baseEnd_1564244] using wordTrace_append hprefix tailTrace_1564244
  have hstable : (prefixWord ++ tailWord_1564244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564244).length < 2 ^ (prefixWord ++ tailWord_1564244).sum := by decide
  have hdescent : baseEnd_1564244 < baseStart_1564244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564278 : List Nat := [5, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1564278 : Nat := 118140960795 + 1564278 * 2 ^ 59
def prefixEnd_1564278 : Nat := 4983230072969 + 3 ^ 40 * 1564278 * 2
def baseEnd_1564278 : Nat := 59498258611402665839335

theorem tailTrace_1564278 : CollatzResearch.WordTrace tailWord_1564278 prefixEnd_1564278 59498258611402665839335 := by
  unfold tailWord_1564278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565869114180964891126343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38035937217930292172014325 3565869114180964891126343)
  ·
    refine ⟨5348803671271447336689515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3565869114180964891126343 5348803671271447336689515)
    ·
      refine ⟨8023205506907171005034273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348803671271447336689515 8023205506907171005034273)
      ·
        refine ⟨6017404130180378253775705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8023205506907171005034273 6017404130180378253775705)
        ·
          refine ⟨4513053097635283690331779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6017404130180378253775705 4513053097635283690331779)
          ·
            refine ⟨6769579646452925535497669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513053097635283690331779 6769579646452925535497669)
            ·
              refine ⟨1269296183709923537905813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6769579646452925535497669 1269296183709923537905813)
              ·
                refine ⟨59498258611402665839335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1269296183709923537905813 59498258611402665839335)
                ·
                  rfl

theorem cell22_1564278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1564278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564278 prefixEnd_1564278 := by exact prefixLift 1564278
  have htrace : WordTrace (prefixWord ++ tailWord_1564278) baseStart_1564278 baseEnd_1564278 := by
    simpa [prefixWord, tailWord_1564278, baseEnd_1564278] using wordTrace_append hprefix tailTrace_1564278
  have hstable : (prefixWord ++ tailWord_1564278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564278).length < 2 ^ (prefixWord ++ tailWord_1564278).sum := by decide
  have hdescent : baseEnd_1564278 < baseStart_1564278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564304 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_1564304 : Nat := 118140960795 + 1564304 * 2 ^ 59
def prefixEnd_1564304 : Nat := 4983230072969 + 3 ^ 40 * 1564304 * 2
def baseEnd_1564304 : Nat := 535493227833968591403935

theorem tailTrace_1564304 : CollatzResearch.WordTrace tailWord_1564304 prefixEnd_1564304 535493227833968591403935 := by
  unfold tailWord_1564304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527427062400622349233983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38036569416534163132311977 28527427062400622349233983)
  ·
    refine ⟨42791140593600933523850975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28527427062400622349233983 42791140593600933523850975)
    ·
      refine ⟨64186710890401400285776463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42791140593600933523850975 64186710890401400285776463)
      ·
        refine ⟨96280066335602100428664695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64186710890401400285776463 96280066335602100428664695)
        ·
          refine ⟨144420099503403150642997043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96280066335602100428664695 144420099503403150642997043)
          ·
            refine ⟨216630149255104725964495565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144420099503403150642997043 216630149255104725964495565)
            ·
              refine ⟨81236305970664272236685837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216630149255104725964495565 81236305970664272236685837)
              ·
                refine ⟨30463614738999102088757189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81236305970664272236685837 30463614738999102088757189)
                ·
                  refine ⟨5711927763562331641641973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30463614738999102088757189 5711927763562331641641973)
                  ·
                    refine ⟨535493227833968591403935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5711927763562331641641973 535493227833968591403935)
                    ·
                      rfl

theorem cell22_1564304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_1564304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564304 prefixEnd_1564304 := by exact prefixLift 1564304
  have htrace : WordTrace (prefixWord ++ tailWord_1564304) baseStart_1564304 baseEnd_1564304 := by
    simpa [prefixWord, tailWord_1564304, baseEnd_1564304] using wordTrace_append hprefix tailTrace_1564304
  have hstable : (prefixWord ++ tailWord_1564304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564304).length < 2 ^ (prefixWord ++ tailWord_1564304).sum := by decide
  have hdescent : baseEnd_1564304 < baseStart_1564304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564366 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1564366 : Nat := 118140960795 + 1564366 * 2 ^ 59
def prefixEnd_1564366 : Nat := 4983230072969 + 3 ^ 40 * 1564366 * 2
def baseEnd_1564366 : Nat := 535514451701021096353745

theorem tailTrace_1564366 : CollatzResearch.WordTrace tailWord_1564366 prefixEnd_1564366 535514451701021096353745 := by
  unfold tailWord_1564366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7132139431322078660903119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38038076967051086191483301 7132139431322078660903119)
  ·
    refine ⟨10698209146983117991354679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7132139431322078660903119 10698209146983117991354679)
    ·
      refine ⟨16047313720474676987032019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10698209146983117991354679 16047313720474676987032019)
      ·
        refine ⟨24070970580712015480548029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16047313720474676987032019 24070970580712015480548029)
        ·
          refine ⟨9026613967767005805205511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24070970580712015480548029 9026613967767005805205511)
          ·
            refine ⟨13539920951650508707808267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026613967767005805205511 13539920951650508707808267)
            ·
              refine ⟨20309881427475763061712401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13539920951650508707808267 20309881427475763061712401)
              ·
                refine ⟨15232411070606822296284301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20309881427475763061712401 15232411070606822296284301)
                ·
                  refine ⟨5712154151477558361106613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15232411070606822296284301 5712154151477558361106613)
                  ·
                    refine ⟨535514451701021096353745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5712154151477558361106613 535514451701021096353745)
                    ·
                      rfl

theorem cell22_1564366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1564366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564366 prefixEnd_1564366 := by exact prefixLift 1564366
  have htrace : WordTrace (prefixWord ++ tailWord_1564366) baseStart_1564366 baseEnd_1564366 := by
    simpa [prefixWord, tailWord_1564366, baseEnd_1564366] using wordTrace_append hprefix tailTrace_1564366
  have hstable : (prefixWord ++ tailWord_1564366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564366).length < 2 ^ (prefixWord ++ tailWord_1564366).sum := by decide
  have hdescent : baseEnd_1564366 < baseStart_1564366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564383 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 2, 3]
def baseStart_1564383 : Nat := 118140960795 + 1564383 * 2 ^ 59
def prefixEnd_1564383 : Nat := 4983230072969 + 3 ^ 40 * 1564383 * 2
def baseEnd_1564383 : Nat := 535520271148438718678693

theorem tailTrace_1564383 : CollatzResearch.WordTrace tailWord_1564383 prefixEnd_1564383 535520271148438718678693 := by
  unfold tailWord_1564383
  simp only [CollatzResearch.WordTrace]
  refine ⟨57057735491515041190593803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38038490327676694127062535 57057735491515041190593803)
  ·
    refine ⟨85586603237272561785890705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57057735491515041190593803 85586603237272561785890705)
    ·
      refine ⟨64189952427954421339418029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85586603237272561785890705 64189952427954421339418029)
      ·
        refine ⟨24071232160482908002281761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64189952427954421339418029 24071232160482908002281761)
        ·
          refine ⟨18053424120362181001711321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24071232160482908002281761 18053424120362181001711321)
          ·
            refine ⟨13540068090271635751283491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18053424120362181001711321 13540068090271635751283491)
            ·
              refine ⟨20310102135407453626925237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13540068090271635751283491 20310102135407453626925237)
              ·
                refine ⟨1904072075194448777524241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20310102135407453626925237 1904072075194448777524241)
                ·
                  refine ⟨1428054056395836583143181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904072075194448777524241 1428054056395836583143181)
                  ·
                    refine ⟨535520271148438718678693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428054056395836583143181 535520271148438718678693)
                    ·
                      rfl

theorem cell22_1564383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_1564383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564383 prefixEnd_1564383 := by exact prefixLift 1564383
  have htrace : WordTrace (prefixWord ++ tailWord_1564383) baseStart_1564383 baseEnd_1564383 := by
    simpa [prefixWord, tailWord_1564383, baseEnd_1564383] using wordTrace_append hprefix tailTrace_1564383
  have hstable : (prefixWord ++ tailWord_1564383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564383).length < 2 ^ (prefixWord ++ tailWord_1564383).sum := by decide
  have hdescent : baseEnd_1564383 < baseStart_1564383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564404 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1564404 : Nat := 118140960795 + 1564404 * 2 ^ 59
def prefixEnd_1564404 : Nat := 4983230072969 + 3 ^ 40 * 1564404 * 2
def baseEnd_1564404 : Nat := 535527459877601663903629

theorem tailTrace_1564404 : CollatzResearch.WordTrace tailWord_1564404 prefixEnd_1564404 535527459877601663903629 := by
  unfold tailWord_1564404
  simp only [CollatzResearch.WordTrace]
  refine ⟨28529250712219480888554133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38039000949625974518072177 28529250712219480888554133)
  ·
    refine ⟨1337308627135288166650975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28529250712219480888554133 1337308627135288166650975)
    ·
      refine ⟨2005962940702932249976463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337308627135288166650975 2005962940702932249976463)
      ·
        refine ⟨3008944411054398374964695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005962940702932249976463 3008944411054398374964695)
        ·
          refine ⟨4513416616581597562447043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008944411054398374964695 4513416616581597562447043)
          ·
            refine ⟨6770124924872396343670565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513416616581597562447043 6770124924872396343670565)
            ·
              refine ⟨1269398423413574314438231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6770124924872396343670565 1269398423413574314438231)
              ·
                refine ⟨1904097635120361471657347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269398423413574314438231 1904097635120361471657347)
                ·
                  refine ⟨2856146452680542207486021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904097635120361471657347 2856146452680542207486021)
                  ·
                    refine ⟨535527459877601663903629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2856146452680542207486021 535527459877601663903629)
                    ·
                      rfl

theorem cell22_1564404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1564404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564404 prefixEnd_1564404 := by exact prefixLift 1564404
  have htrace : WordTrace (prefixWord ++ tailWord_1564404) baseStart_1564404 baseEnd_1564404 := by
    simpa [prefixWord, tailWord_1564404, baseEnd_1564404] using wordTrace_append hprefix tailTrace_1564404
  have hstable : (prefixWord ++ tailWord_1564404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564404).length < 2 ^ (prefixWord ++ tailWord_1564404).sum := by decide
  have hdescent : baseEnd_1564404 < baseStart_1564404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564428 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1564428 : Nat := 118140960795 + 1564428 * 2 ^ 59
def prefixEnd_1564428 : Nat := 4983230072969 + 3 ^ 40 * 1564428 * 2
def baseEnd_1564428 : Nat := 535535675568073601303555

theorem tailTrace_1564428 : CollatzResearch.WordTrace tailWord_1564428 prefixEnd_1564428 535535675568073601303555 := by
  unfold tailWord_1564428
  simp only [CollatzResearch.WordTrace]
  refine ⟨28529688388176006937990969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38039584517568009250654625 28529688388176006937990969)
  ·
    refine ⟨21397266291132005203493227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28529688388176006937990969 21397266291132005203493227)
    ·
      refine ⟨32095899436698007805239841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397266291132005203493227 32095899436698007805239841)
      ·
        refine ⟨24071924577523505853929881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32095899436698007805239841 24071924577523505853929881)
        ·
          refine ⟨18053943433142629390447411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24071924577523505853929881 18053943433142629390447411)
          ·
            refine ⟨27080915149713944085671117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18053943433142629390447411 27080915149713944085671117)
            ·
              refine ⟨10155343181142729032126669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27080915149713944085671117 10155343181142729032126669)
              ·
                refine ⟨3808253692928523387047501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10155343181142729032126669 3808253692928523387047501)
                ·
                  refine ⟨1428095134848196270142813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3808253692928523387047501 1428095134848196270142813)
                  ·
                    refine ⟨535535675568073601303555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428095134848196270142813 535535675568073601303555)
                    ·
                      rfl

theorem cell22_1564428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1564428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564428 prefixEnd_1564428 := by exact prefixLift 1564428
  have htrace : WordTrace (prefixWord ++ tailWord_1564428) baseStart_1564428 baseEnd_1564428 := by
    simpa [prefixWord, tailWord_1564428, baseEnd_1564428] using wordTrace_append hprefix tailTrace_1564428
  have hstable : (prefixWord ++ tailWord_1564428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564428).length < 2 ^ (prefixWord ++ tailWord_1564428).sum := by decide
  have hdescent : baseEnd_1564428 < baseStart_1564428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564434 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1564434 : Nat := 118140960795 + 1564434 * 2 ^ 59
def prefixEnd_1564434 : Nat := 4983230072969 + 3 ^ 40 * 1564434 * 2
def baseEnd_1564434 : Nat := 535537729490691585653537

theorem tailTrace_1564434 : CollatzResearch.WordTrace tailWord_1564434 prefixEnd_1564434 535537729490691585653537 := by
  unfold tailWord_1564434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264898903582569225175089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38039730409553517933800237 14264898903582569225175089)
  ·
    refine ⟨10698674177686926918881317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14264898903582569225175089 10698674177686926918881317)
    ·
      refine ⟨2006001408316298797290247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10698674177686926918881317 2006001408316298797290247)
      ·
        refine ⟨3009002112474448195935371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006001408316298797290247 3009002112474448195935371)
        ·
          refine ⟨4513503168711672293903057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009002112474448195935371 4513503168711672293903057)
          ·
            refine ⟨3385127376533754220427293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4513503168711672293903057 3385127376533754220427293)
            ·
              refine ⟨1269422766200157832660235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385127376533754220427293 1269422766200157832660235)
              ·
                refine ⟨1904134149300236748990353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269422766200157832660235 1904134149300236748990353)
                ·
                  refine ⟨1428100611975177561742765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904134149300236748990353 1428100611975177561742765)
                  ·
                    refine ⟨535537729490691585653537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428100611975177561742765 535537729490691585653537)
                    ·
                      rfl

theorem cell22_1564434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1564434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564434 prefixEnd_1564434 := by exact prefixLift 1564434
  have htrace : WordTrace (prefixWord ++ tailWord_1564434) baseStart_1564434 baseEnd_1564434 := by
    simpa [prefixWord, tailWord_1564434, baseEnd_1564434] using wordTrace_append hprefix tailTrace_1564434
  have hstable : (prefixWord ++ tailWord_1564434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564434).length < 2 ^ (prefixWord ++ tailWord_1564434).sum := by decide
  have hdescent : baseEnd_1564434 < baseStart_1564434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564479 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 1, 3]
def baseStart_1564479 : Nat := 118140960795 + 1564479 * 2 ^ 59
def prefixEnd_1564479 : Nat := 4983230072969 + 3 ^ 40 * 1564479 * 2
def baseEnd_1564479 : Nat := 535553133910326468278399

theorem tailTrace_1564479 : CollatzResearch.WordTrace tailWord_1564479 prefixEnd_1564479 535553133910326468278399 := by
  unfold tailWord_1564479
  simp only [CollatzResearch.WordTrace]
  refine ⟨57061236899167249586088491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38040824599444833057392327 57061236899167249586088491)
  ·
    refine ⟨85591855348750874379132737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57061236899167249586088491 85591855348750874379132737)
    ·
      refine ⟨64193891511563155784349553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85591855348750874379132737 64193891511563155784349553)
      ·
        refine ⟨48145418633672366838262165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64193891511563155784349553 48145418633672366838262165)
        ·
          refine ⟨2256816498453392195543539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48145418633672366838262165 2256816498453392195543539)
          ·
            refine ⟨3385224747680088293315309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256816498453392195543539 3385224747680088293315309)
            ·
              refine ⟨1269459280380033109993241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385224747680088293315309 1269459280380033109993241)
              ·
                refine ⟨952094460285024832494931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269459280380033109993241 952094460285024832494931)
                ·
                  refine ⟨1428141690427537248742397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952094460285024832494931 1428141690427537248742397)
                  ·
                    refine ⟨535553133910326468278399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428141690427537248742397 535553133910326468278399)
                    ·
                      rfl

theorem cell22_1564479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_1564479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564479 prefixEnd_1564479 := by exact prefixLift 1564479
  have htrace : WordTrace (prefixWord ++ tailWord_1564479) baseStart_1564479 baseEnd_1564479 := by
    simpa [prefixWord, tailWord_1564479, baseEnd_1564479] using wordTrace_append hprefix tailTrace_1564479
  have hstable : (prefixWord ++ tailWord_1564479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564479).length < 2 ^ (prefixWord ++ tailWord_1564479).sum := by decide
  have hdescent : baseEnd_1564479 < baseStart_1564479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564492 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 5]
def baseStart_1564492 : Nat := 118140960795 + 1564492 * 2 ^ 59
def prefixEnd_1564492 : Nat := 4983230072969 + 3 ^ 40 * 1564492 * 2
def baseEnd_1564492 : Nat := 178519194691999589234453

theorem tailTrace_1564492 : CollatzResearch.WordTrace tailWord_1564492 prefixEnd_1564492 178519194691999589234453 := by
  unfold tailWord_1564492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28530855524060076403155865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38041140698746768537541153 28530855524060076403155865)
  ·
    refine ⟨21398141643045057302366899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28530855524060076403155865 21398141643045057302366899)
    ·
      refine ⟨32097212464567585953550349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21398141643045057302366899 32097212464567585953550349)
      ·
        refine ⟨12036454674212844732581381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32097212464567585953550349 12036454674212844732581381)
        ·
          refine ⟨2256835251414908387359009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12036454674212844732581381 2256835251414908387359009)
          ·
            refine ⟨1692626438561181290519257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256835251414908387359009 1692626438561181290519257)
            ·
              refine ⟨1269469828920885967889443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692626438561181290519257 1269469828920885967889443)
              ·
                refine ⟨1904204743381328951834165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269469828920885967889443 1904204743381328951834165)
                ·
                  refine ⟨178519194691999589234453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1904204743381328951834165 178519194691999589234453)
                  ·
                    rfl

theorem cell22_1564492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_1564492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564492 prefixEnd_1564492 := by exact prefixLift 1564492
  have htrace : WordTrace (prefixWord ++ tailWord_1564492) baseStart_1564492 baseEnd_1564492 := by
    simpa [prefixWord, tailWord_1564492, baseEnd_1564492] using wordTrace_append hprefix tailTrace_1564492
  have hstable : (prefixWord ++ tailWord_1564492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564492).length < 2 ^ (prefixWord ++ tailWord_1564492).sum := by decide
  have hdescent : baseEnd_1564492 < baseStart_1564492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564520 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 4]
def baseStart_1564520 : Nat := 118140960795 + 1564520 * 2 ^ 59
def prefixEnd_1564520 : Nat := 4983230072969 + 3 ^ 40 * 1564520 * 2
def baseEnd_1564520 : Nat := 178522389682738676001091

theorem tailTrace_1564520 : CollatzResearch.WordTrace tailWord_1564520 prefixEnd_1564520 178522389682738676001091 := by
  unfold tailWord_1564520
  simp only [CollatzResearch.WordTrace]
  refine ⟨28531366146009356794165507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38041821528012475725554009 28531366146009356794165507)
  ·
    refine ⟨42797049219014035191248261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28531366146009356794165507 42797049219014035191248261)
    ·
      refine ⟨8024446728565131598359049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42797049219014035191248261 8024446728565131598359049)
      ·
        refine ⟨6018335046423848698769287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8024446728565131598359049 6018335046423848698769287)
        ·
          refine ⟨9027502569635773048153931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6018335046423848698769287 9027502569635773048153931)
          ·
            refine ⟨13541253854453659572230897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9027502569635773048153931 13541253854453659572230897)
            ·
              refine ⟨10155940390840244679173173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13541253854453659572230897 10155940390840244679173173)
              ·
                refine ⟨952119411641272938672485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10155940390840244679173173 952119411641272938672485)
                ·
                  refine ⟨178522389682738676001091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952119411641272938672485 178522389682738676001091)
                  ·
                    rfl

theorem cell22_1564520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_1564520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564520 prefixEnd_1564520 := by exact prefixLift 1564520
  have htrace : WordTrace (prefixWord ++ tailWord_1564520) baseStart_1564520 baseEnd_1564520 := by
    simpa [prefixWord, tailWord_1564520, baseEnd_1564520] using wordTrace_append hprefix tailTrace_1564520
  have hstable : (prefixWord ++ tailWord_1564520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564520).length < 2 ^ (prefixWord ++ tailWord_1564520).sum := by decide
  have hdescent : baseEnd_1564520 < baseStart_1564520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564548 : List Nat := [2, 3, 2, 1, 1, 1, 5, 7]
def baseStart_1564548 : Nat := 118140960795 + 1564548 * 2 ^ 59
def prefixEnd_1564548 : Nat := 4983230072969 + 3 ^ 40 * 1564548 * 2
def baseEnd_1564548 : Nat := 59508528224492587589243

theorem tailTrace_1564548 : CollatzResearch.WordTrace tailWord_1564548 prefixEnd_1564548 59508528224492587589243 := by
  unfold tailWord_1564548
  simp only [CollatzResearch.WordTrace]
  refine ⟨28531876767958637185175149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38042502357278182913566865 28531876767958637185175149)
  ·
    refine ⟨10699453787984488944440681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28531876767958637185175149 10699453787984488944440681)
    ·
      refine ⟨8024590340988366708330511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10699453787984488944440681 8024590340988366708330511)
      ·
        refine ⟨12036885511482550062495767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8024590340988366708330511 12036885511482550062495767)
        ·
          refine ⟨18055328267223825093743651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12036885511482550062495767 18055328267223825093743651)
          ·
            refine ⟨27082992400835737640615477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18055328267223825093743651 27082992400835737640615477)
            ·
              refine ⟨2539030537578350403807701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27082992400835737640615477 2539030537578350403807701)
              ·
                refine ⟨59508528224492587589243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2539030537578350403807701 59508528224492587589243)
                ·
                  rfl

theorem cell22_1564548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_1564548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564548 prefixEnd_1564548 := by exact prefixLift 1564548
  have htrace : WordTrace (prefixWord ++ tailWord_1564548) baseStart_1564548 baseEnd_1564548 := by
    simpa [prefixWord, tailWord_1564548, baseEnd_1564548] using wordTrace_append hprefix tailTrace_1564548
  have hstable : (prefixWord ++ tailWord_1564548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564548).length < 2 ^ (prefixWord ++ tailWord_1564548).sum := by decide
  have hdescent : baseEnd_1564548 < baseStart_1564548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564597 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1564597 : Nat := 118140960795 + 1564597 * 2 ^ 59
def prefixEnd_1564597 : Nat := 4983230072969 + 3 ^ 40 * 1564597 * 2
def baseEnd_1564597 : Nat := 535593527721813493828037

theorem tailTrace_1564597 : CollatzResearch.WordTrace tailWord_1564597 prefixEnd_1564597 535593527721813493828037 := by
  unfold tailWord_1564597
  simp only [CollatzResearch.WordTrace]
  refine ⟨57065540712739755738884045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38043693808493170492589363 57065540712739755738884045)
  ·
    refine ⟨21399577767277408402081517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57065540712739755738884045 21399577767277408402081517)
    ·
      refine ⟨8024841662729028150780569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21399577767277408402081517 8024841662729028150780569)
      ·
        refine ⟨6018631247046771113085427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8024841662729028150780569 6018631247046771113085427)
        ·
          refine ⟨9027946870570156669628141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6018631247046771113085427 9027946870570156669628141)
          ·
            refine ⟨3385480076463808751110553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9027946870570156669628141 3385480076463808751110553)
            ·
              refine ⟨2539110057347856563332915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3385480076463808751110553 2539110057347856563332915)
              ·
                refine ⟨3808665086021784844999373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539110057347856563332915 3808665086021784844999373)
                ·
                  refine ⟨1428249407258169316874765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3808665086021784844999373 1428249407258169316874765)
                  ·
                    refine ⟨535593527721813493828037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428249407258169316874765 535593527721813493828037)
                    ·
                      rfl

theorem cell22_1564597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1564597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564597 prefixEnd_1564597 := by exact prefixLift 1564597
  have htrace : WordTrace (prefixWord ++ tailWord_1564597) baseStart_1564597 baseEnd_1564597 := by
    simpa [prefixWord, tailWord_1564597, baseEnd_1564597] using wordTrace_append hprefix tailTrace_1564597
  have hstable : (prefixWord ++ tailWord_1564597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564597).length < 2 ^ (prefixWord ++ tailWord_1564597).sum := by decide
  have hdescent : baseEnd_1564597 < baseStart_1564597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564608 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_1564608 : Nat := 118140960795 + 1564608 * 2 ^ 59
def prefixEnd_1564608 : Nat := 4983230072969 + 3 ^ 40 * 1564608 * 2
def baseEnd_1564608 : Nat := 535597293246613131803003

theorem tailTrace_1564608 : CollatzResearch.WordTrace tailWord_1564608 prefixEnd_1564608 535597293246613131803003 := by
  unfold tailWord_1564608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28532970957849952308767239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38043961277133269745022985 28532970957849952308767239)
  ·
    refine ⟨42799456436774928463150859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28532970957849952308767239 42799456436774928463150859)
    ·
      refine ⟨64199184655162392694726289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42799456436774928463150859 64199184655162392694726289)
      ·
        refine ⟨48149388491371794521044717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64199184655162392694726289 48149388491371794521044717)
        ·
          refine ⟨18056020684264422945391769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48149388491371794521044717 18056020684264422945391769)
          ·
            refine ⟨13542015513198317209043827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18056020684264422945391769 13542015513198317209043827)
            ·
              refine ⟨20313023269797475813565741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13542015513198317209043827 20313023269797475813565741)
              ·
                refine ⟨7617383726174053430087153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20313023269797475813565741 7617383726174053430087153)
                ·
                  refine ⟨5713037794630540072565365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7617383726174053430087153 5713037794630540072565365)
                  ·
                    refine ⟨535597293246613131803003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5713037794630540072565365 535597293246613131803003)
                    ·
                      rfl

theorem cell22_1564608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_1564608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564608 prefixEnd_1564608 := by exact prefixLift 1564608
  have htrace : WordTrace (prefixWord ++ tailWord_1564608) baseStart_1564608 baseEnd_1564608 := by
    simpa [prefixWord, tailWord_1564608, baseEnd_1564608] using wordTrace_append hprefix tailTrace_1564608
  have hstable : (prefixWord ++ tailWord_1564608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564608).length < 2 ^ (prefixWord ++ tailWord_1564608).sum := by decide
  have hdescent : baseEnd_1564608 < baseStart_1564608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564683 : List Nat := [1, 1, 1, 1, 6, 1, 1, 10]
def baseStart_1564683 : Nat := 118140960795 + 1564683 * 2 ^ 59
def prefixEnd_1564683 : Nat := 4983230072969 + 3 ^ 40 * 1564683 * 2
def baseEnd_1564683 : Nat := 59513663031037548464197

theorem tailTrace_1564683 : CollatzResearch.WordTrace tailWord_1564683 prefixEnd_1564683 59513663031037548464197 := by
  unfold tailWord_1564683
  simp only [CollatzResearch.WordTrace]
  refine ⟨57068677390428192426514703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38045784926952128284343135 57068677390428192426514703)
  ·
    refine ⟨85603016085642288639772055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57068677390428192426514703 85603016085642288639772055)
    ·
      refine ⟨128404524128463432959658083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85603016085642288639772055 128404524128463432959658083)
      ·
        refine ⟨192606786192695149439487125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128404524128463432959658083 192606786192695149439487125)
        ·
          refine ⟨9028443102782585129975959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192606786192695149439487125 9028443102782585129975959)
          ·
            refine ⟨13542664654173877694963939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028443102782585129975959 13542664654173877694963939)
            ·
              refine ⟨20313996981260816542445909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13542664654173877694963939 20313996981260816542445909)
              ·
                refine ⟨59513663031037548464197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20313996981260816542445909 59513663031037548464197)
                ·
                  rfl

theorem cell22_1564683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 10].length) (baseStart_1564683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564683 prefixEnd_1564683 := by exact prefixLift 1564683
  have htrace : WordTrace (prefixWord ++ tailWord_1564683) baseStart_1564683 baseEnd_1564683 := by
    simpa [prefixWord, tailWord_1564683, baseEnd_1564683] using wordTrace_append hprefix tailTrace_1564683
  have hstable : (prefixWord ++ tailWord_1564683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564683).length < 2 ^ (prefixWord ++ tailWord_1564683).sum := by decide
  have hdescent : baseEnd_1564683 < baseStart_1564683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564732 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1564732 : Nat := 118140960795 + 1564732 * 2 ^ 59
def prefixEnd_1564732 : Nat := 4983230072969 + 3 ^ 40 * 1564732 * 2
def baseEnd_1564732 : Nat := 535639740980718141702623

theorem tailTrace_1564732 : CollatzResearch.WordTrace tailWord_1564732 prefixEnd_1564732 535639740980718141702623 := by
  unfold tailWord_1564732
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535232283625336897524225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38046976378167115863365633 28535232283625336897524225)
  ·
    refine ⟨21401424212719002673143169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28535232283625336897524225 21401424212719002673143169)
    ·
      refine ⟨16051068159539252004857377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21401424212719002673143169 16051068159539252004857377)
      ·
        refine ⟨12038301119654439003643033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16051068159539252004857377 12038301119654439003643033)
        ·
          refine ⟨9028725839740829252732275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12038301119654439003643033 9028725839740829252732275)
          ·
            refine ⟨13543088759611243879098413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028725839740829252732275 13543088759611243879098413)
            ·
              refine ⟨5078658284854216454661905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13543088759611243879098413 5078658284854216454661905)
              ·
                refine ⟨3808993713640662340996429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5078658284854216454661905 3808993713640662340996429)
                ·
                  refine ⟨1428372642615248377873661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3808993713640662340996429 1428372642615248377873661)
                  ·
                    refine ⟨535639740980718141702623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428372642615248377873661 535639740980718141702623)
                    ·
                      rfl

theorem cell22_1564732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1564732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564732 prefixEnd_1564732 := by exact prefixLift 1564732
  have htrace : WordTrace (prefixWord ++ tailWord_1564732) baseStart_1564732 baseEnd_1564732 := by
    simpa [prefixWord, tailWord_1564732, baseEnd_1564732] using wordTrace_append hprefix tailTrace_1564732
  have hstable : (prefixWord ++ tailWord_1564732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564732).length < 2 ^ (prefixWord ++ tailWord_1564732).sum := by decide
  have hdescent : baseEnd_1564732 < baseStart_1564732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564734 : List Nat := [4, 2, 1, 3, 2, 1, 3, 6]
def baseStart_1564734 : Nat := 118140960795 + 1564734 * 2 ^ 59
def prefixEnd_1564734 : Nat := 4983230072969 + 3 ^ 40 * 1564734 * 2
def baseEnd_1564734 : Nat := 59515602846843422572513

theorem tailTrace_1564734 : CollatzResearch.WordTrace tailWord_1564734 prefixEnd_1564734 59515602846843422572513 := by
  unfold tailWord_1564734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133817189155428517077657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38047025008828952091080837 7133817189155428517077657)
  ·
    refine ⟨5350362891866571387808243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7133817189155428517077657 5350362891866571387808243)
    ·
      refine ⟨8025544337799857081712365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350362891866571387808243 8025544337799857081712365)
      ·
        refine ⟨3009579126674946405642137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8025544337799857081712365 3009579126674946405642137)
        ·
          refine ⟨2257184345006209804231603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3009579126674946405642137 2257184345006209804231603)
          ·
            refine ⟨3385776517509314706347405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257184345006209804231603 3385776517509314706347405)
            ·
              refine ⟨1269666194065993014880277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385776517509314706347405 1269666194065993014880277)
              ·
                refine ⟨59515602846843422572513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1269666194065993014880277 59515602846843422572513)
                ·
                  rfl

theorem cell22_1564734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_1564734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564734 prefixEnd_1564734 := by exact prefixLift 1564734
  have htrace : WordTrace (prefixWord ++ tailWord_1564734) baseStart_1564734 baseEnd_1564734 := by
    simpa [prefixWord, tailWord_1564734, baseEnd_1564734] using wordTrace_append hprefix tailTrace_1564734
  have hstable : (prefixWord ++ tailWord_1564734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564734).length < 2 ^ (prefixWord ++ tailWord_1564734).sum := by decide
  have hdescent : baseEnd_1564734 < baseStart_1564734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564760 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1564760 : Nat := 118140960795 + 1564760 * 2 ^ 59
def prefixEnd_1564760 : Nat := 4983230072969 + 3 ^ 40 * 1564760 * 2
def baseEnd_1564760 : Nat := 535649325952935402002537

theorem tailTrace_1564760 : CollatzResearch.WordTrace tailWord_1564760 prefixEnd_1564760 535649325952935402002537 := by
  unfold tailWord_1564760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535742905574617288533867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38047657207432823051378489 28535742905574617288533867)
  ·
    refine ⟨42803614358361925932800801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28535742905574617288533867 42803614358361925932800801)
    ·
      refine ⟨32102710768771444449600601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42803614358361925932800801 32102710768771444449600601)
      ·
        refine ⟨24077033076578583337200451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32102710768771444449600601 24077033076578583337200451)
        ·
          refine ⟨36115549614867875005800677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24077033076578583337200451 36115549614867875005800677)
          ·
            refine ⟨6771665552787726563587627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36115549614867875005800677 6771665552787726563587627)
            ·
              refine ⟨10157498329181589845381441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771665552787726563587627 10157498329181589845381441)
              ·
                refine ⟨7618123746886192384036081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10157498329181589845381441 7618123746886192384036081)
                ·
                  refine ⟨5713592810164644288027061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7618123746886192384036081 5713592810164644288027061)
                  ·
                    refine ⟨535649325952935402002537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5713592810164644288027061 535649325952935402002537)
                    ·
                      rfl

theorem cell22_1564760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1564760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564760 prefixEnd_1564760 := by exact prefixLift 1564760
  have htrace : WordTrace (prefixWord ++ tailWord_1564760) baseStart_1564760 baseEnd_1564760 := by
    simpa [prefixWord, tailWord_1564760, baseEnd_1564760] using wordTrace_append hprefix tailTrace_1564760
  have hstable : (prefixWord ++ tailWord_1564760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564760).length < 2 ^ (prefixWord ++ tailWord_1564760).sum := by decide
  have hdescent : baseEnd_1564760 < baseStart_1564760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564824 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 6]
def baseStart_1564824 : Nat := 118140960795 + 1564824 * 2 ^ 59
def prefixEnd_1564824 : Nat := 4983230072969 + 3 ^ 40 * 1564824 * 2
def baseEnd_1564824 : Nat := 178557078153620189467447

theorem tailTrace_1564824 : CollatzResearch.WordTrace tailWord_1564824 prefixEnd_1564824 178557078153620189467447 := by
  unfold tailWord_1564824
  simp only [CollatzResearch.WordTrace]
  refine ⟨28536910041458686753698763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38049213388611582338265017 28536910041458686753698763)
  ·
    refine ⟨42805365062188030130548145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28536910041458686753698763 42805365062188030130548145)
    ·
      refine ⟨32104023796641022597911109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42805365062188030130548145 32104023796641022597911109)
      ·
        refine ⟨6019504461870191737108333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32104023796641022597911109 6019504461870191737108333)
        ·
          refine ⟨2257314173201321901415625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6019504461870191737108333 2257314173201321901415625)
          ·
            refine ⟨1692985629900991426061719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257314173201321901415625 1692985629900991426061719)
            ·
              refine ⟨2539478444851487139092579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692985629900991426061719 2539478444851487139092579)
              ·
                refine ⟨3809217667277230708638869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539478444851487139092579 3809217667277230708638869)
                ·
                  refine ⟨178557078153620189467447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3809217667277230708638869 178557078153620189467447)
                  ·
                    rfl

theorem cell22_1564824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_1564824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564824 prefixEnd_1564824 := by exact prefixLift 1564824
  have htrace : WordTrace (prefixWord ++ tailWord_1564824) baseStart_1564824 baseEnd_1564824 := by
    simpa [prefixWord, tailWord_1564824, baseEnd_1564824] using wordTrace_append hprefix tailTrace_1564824
  have hstable : (prefixWord ++ tailWord_1564824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564824).length < 2 ^ (prefixWord ++ tailWord_1564824).sum := by decide
  have hdescent : baseEnd_1564824 < baseStart_1564824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564882 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1564882 : Nat := 118140960795 + 1564882 * 2 ^ 59
def prefixEnd_1564882 : Nat := 4983230072969 + 3 ^ 40 * 1564882 * 2
def baseEnd_1564882 : Nat := 535691089046167750452163

theorem tailTrace_1564882 : CollatzResearch.WordTrace tailWord_1564882 prefixEnd_1564882 535691089046167750452163 := by
  unfold tailWord_1564882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268983879176812353252225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38050623677804832942005933 14268983879176812353252225)
  ·
    refine ⟨10701737909382609264939169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14268983879176812353252225 10701737909382609264939169)
    ·
      refine ⟨8026303432036956948704377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10701737909382609264939169 8026303432036956948704377)
      ·
        refine ⟨6019727574027717711528283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8026303432036956948704377 6019727574027717711528283)
        ·
          refine ⟨9029591361041576567292425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019727574027717711528283 9029591361041576567292425)
          ·
            refine ⟨6772193520781182425469319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9029591361041576567292425 6772193520781182425469319)
            ·
              refine ⟨10158290281171773638203979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772193520781182425469319 10158290281171773638203979)
              ·
                refine ⟨15237435421757660457305969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10158290281171773638203979 15237435421757660457305969)
                ·
                  refine ⟨11428076566318245342979477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15237435421757660457305969 11428076566318245342979477)
                  ·
                    refine ⟨535691089046167750452163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11428076566318245342979477 535691089046167750452163)
                    ·
                      rfl

theorem cell22_1564882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1564882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564882 prefixEnd_1564882 := by exact prefixLift 1564882
  have htrace : WordTrace (prefixWord ++ tailWord_1564882) baseStart_1564882 baseEnd_1564882 := by
    simpa [prefixWord, tailWord_1564882, baseEnd_1564882] using wordTrace_append hprefix tailTrace_1564882
  have hstable : (prefixWord ++ tailWord_1564882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564882).length < 2 ^ (prefixWord ++ tailWord_1564882).sum := by decide
  have hdescent : baseEnd_1564882 < baseStart_1564882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564886 : List Nat := [5, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1564886 : Nat := 118140960795 + 1564886 * 2 ^ 59
def prefixEnd_1564886 : Nat := 4983230072969 + 3 ^ 40 * 1564886 * 2
def baseEnd_1564886 : Nat := 59521384258657008150239

theorem tailTrace_1564886 : CollatzResearch.WordTrace tailWord_1564886 prefixEnd_1564886 59521384258657008150239 := by
  unfold tailWord_1564886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567255088043297381009657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38050720939128505397436341 3567255088043297381009657)
  ·
    refine ⟨2675441316032473035757243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3567255088043297381009657 2675441316032473035757243)
    ·
      refine ⟨4013161974048709553635865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2675441316032473035757243 4013161974048709553635865)
      ·
        refine ⟨3009871480536532165226899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4013161974048709553635865 3009871480536532165226899)
        ·
          refine ⟨4514807220804798247840349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009871480536532165226899 4514807220804798247840349)
          ·
            refine ⟨1693052707801799342940131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4514807220804798247840349 1693052707801799342940131)
            ·
              refine ⟨2539579061702699014410197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693052707801799342940131 2539579061702699014410197)
              ·
                refine ⟨59521384258657008150239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2539579061702699014410197 59521384258657008150239)
                ·
                  rfl

theorem cell22_1564886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1564886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564886 prefixEnd_1564886 := by exact prefixLift 1564886
  have htrace : WordTrace (prefixWord ++ tailWord_1564886) baseStart_1564886 baseEnd_1564886 := by
    simpa [prefixWord, tailWord_1564886, baseEnd_1564886] using wordTrace_append hprefix tailTrace_1564886
  have hstable : (prefixWord ++ tailWord_1564886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564886).length < 2 ^ (prefixWord ++ tailWord_1564886).sum := by decide
  have hdescent : baseEnd_1564886 < baseStart_1564886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564897 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 5]
def baseStart_1564897 : Nat := 118140960795 + 1564897 * 2 ^ 59
def prefixEnd_1564897 : Nat := 4983230072969 + 3 ^ 40 * 1564897 * 2
def baseEnd_1564897 : Nat := 178565407950904237109039

theorem tailTrace_1564897 : CollatzResearch.WordTrace tailWord_1564897 prefixEnd_1564897 178565407950904237109039 := by
  unfold tailWord_1564897
  simp only [CollatzResearch.WordTrace]
  refine ⟨57076482611652906974804945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38050988407768604649869963 57076482611652906974804945)
  ·
    refine ⟨42807361958739680231103709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57076482611652906974804945 42807361958739680231103709)
    ·
      refine ⟨16052760734527380086663891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42807361958739680231103709 16052760734527380086663891)
      ·
        refine ⟨24079141101791070129995837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16052760734527380086663891 24079141101791070129995837)
        ·
          refine ⟨9029677913171651298748439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24079141101791070129995837 9029677913171651298748439)
          ·
            refine ⟨13544516869757476948122659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029677913171651298748439 13544516869757476948122659)
            ·
              refine ⟨20316775304636215422183989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13544516869757476948122659 20316775304636215422183989)
              ·
                refine ⟨1904697684809645195829749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20316775304636215422183989 1904697684809645195829749)
                ·
                  refine ⟨178565407950904237109039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1904697684809645195829749 178565407950904237109039)
                  ·
                    rfl

theorem cell22_1564897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_1564897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564897 prefixEnd_1564897 := by exact prefixLift 1564897
  have htrace : WordTrace (prefixWord ++ tailWord_1564897) baseStart_1564897 baseEnd_1564897 := by
    simpa [prefixWord, tailWord_1564897, baseEnd_1564897] using wordTrace_append hprefix tailTrace_1564897
  have hstable : (prefixWord ++ tailWord_1564897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564897).length < 2 ^ (prefixWord ++ tailWord_1564897).sum := by decide
  have hdescent : baseEnd_1564897 < baseStart_1564897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564972 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1564972 : Nat := 118140960795 + 1564972 * 2 ^ 59
def prefixEnd_1564972 : Nat := 4983230072969 + 3 ^ 40 * 1564972 * 2
def baseEnd_1564972 : Nat := 535721897885437515701887

theorem tailTrace_1564972 : CollatzResearch.WordTrace tailWord_1564972 prefixEnd_1564972 535721897885437515701887 := by
  unfold tailWord_1564972
  simp only [CollatzResearch.WordTrace]
  refine ⟨28539609043190597391892585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38052812057587463189190113 28539609043190597391892585)
  ·
    refine ⟨21404706782392948043919439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28539609043190597391892585 21404706782392948043919439)
    ·
      refine ⟨32107060173589422065879159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21404706782392948043919439 32107060173589422065879159)
      ·
        refine ⟨48160590260384133098818739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32107060173589422065879159 48160590260384133098818739)
        ·
          refine ⟨72240885390576199648228109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48160590260384133098818739 72240885390576199648228109)
          ·
            refine ⟨27090332021466074868085541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72240885390576199648228109 27090332021466074868085541)
            ·
              refine ⟨5079437254024889037766039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27090332021466074868085541 5079437254024889037766039)
              ·
                refine ⟨7619155881037333556649059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079437254024889037766039 7619155881037333556649059)
                ·
                  refine ⟨11428733821556000334973589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619155881037333556649059 11428733821556000334973589)
                  ·
                    refine ⟨535721897885437515701887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11428733821556000334973589 535721897885437515701887)
                    ·
                      rfl

theorem cell22_1564972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1564972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564972 prefixEnd_1564972 := by exact prefixLift 1564972
  have htrace : WordTrace (prefixWord ++ tailWord_1564972) baseStart_1564972 baseEnd_1564972 := by
    simpa [prefixWord, tailWord_1564972, baseEnd_1564972] using wordTrace_append hprefix tailTrace_1564972
  have hstable : (prefixWord ++ tailWord_1564972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564972).length < 2 ^ (prefixWord ++ tailWord_1564972).sum := by decide
  have hdescent : baseEnd_1564972 < baseStart_1564972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564993 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 6]
def baseStart_1564993 : Nat := 118140960795 + 1564993 * 2 ^ 59
def prefixEnd_1564993 : Nat := 4983230072969 + 3 ^ 40 * 1564993 * 2
def baseEnd_1564993 : Nat := 178576362204866820308941

theorem tailTrace_1564993 : CollatzResearch.WordTrace tailWord_1564993 prefixEnd_1564993 178576362204866820308941 := by
  unfold tailWord_1564993
  simp only [CollatzResearch.WordTrace]
  refine ⟨57079984019305115370299633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38053322679536743580199755 57079984019305115370299633)
  ·
    refine ⟨42809988014478836527724725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57079984019305115370299633 42809988014478836527724725)
    ·
      refine ⟨4013436376357390924474193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42809988014478836527724725 4013436376357390924474193)
      ·
        refine ⟨3010077282268043193355645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4013436376357390924474193 3010077282268043193355645)
        ·
          refine ⟨1128778980850516197508367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3010077282268043193355645 1128778980850516197508367)
          ·
            refine ⟨1693168471275774296262551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128778980850516197508367 1693168471275774296262551)
            ·
              refine ⟨2539752706913661444393827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693168471275774296262551 2539752706913661444393827)
              ·
                refine ⟨3809629060370492166590741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539752706913661444393827 3809629060370492166590741)
                ·
                  refine ⟨178576362204866820308941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3809629060370492166590741 178576362204866820308941)
                  ·
                    rfl

theorem cell22_1564993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_1564993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1564993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1564993 prefixEnd_1564993 := by exact prefixLift 1564993
  have htrace : WordTrace (prefixWord ++ tailWord_1564993) baseStart_1564993 baseEnd_1564993 := by
    simpa [prefixWord, tailWord_1564993, baseEnd_1564993] using wordTrace_append hprefix tailTrace_1564993
  have hstable : (prefixWord ++ tailWord_1564993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564993).length < 2 ^ (prefixWord ++ tailWord_1564993).sum := by decide
  have hdescent : baseEnd_1564993 < baseStart_1564993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565008 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 2, 3]
def baseStart_1565008 : Nat := 118140960795 + 1565008 * 2 ^ 59
def prefixEnd_1565008 : Nat := 4983230072969 + 3 ^ 40 * 1565008 * 2
def baseEnd_1565008 : Nat := 535734221421145421801777

theorem tailTrace_1565008 : CollatzResearch.WordTrace tailWord_1565008 prefixEnd_1565008 535734221421145421801777 := by
  unfold tailWord_1565008
  simp only [CollatzResearch.WordTrace]
  refine ⟨28540265557125386466047839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38053687409500515288063785 28540265557125386466047839)
  ·
    refine ⟨42810398335688079699071759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28540265557125386466047839 42810398335688079699071759)
    ·
      refine ⟨64215597503532119548607639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42810398335688079699071759 64215597503532119548607639)
      ·
        refine ⟨96323396255298179322911459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64215597503532119548607639 96323396255298179322911459)
        ·
          refine ⟨144485094382947268984367189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96323396255298179322911459 144485094382947268984367189)
          ·
            refine ⟨1693184699800163308410553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 144485094382947268984367189 1693184699800163308410553)
            ·
              refine ⟨1269888524850122481307915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693184699800163308410553 1269888524850122481307915)
              ·
                refine ⟨1904832787275183721961873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269888524850122481307915 1904832787275183721961873)
                ·
                  refine ⟨1428624590456387791471405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904832787275183721961873 1428624590456387791471405)
                  ·
                    refine ⟨535734221421145421801777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428624590456387791471405 535734221421145421801777)
                    ·
                      rfl

theorem cell22_1565008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_1565008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565008 prefixEnd_1565008 := by exact prefixLift 1565008
  have htrace : WordTrace (prefixWord ++ tailWord_1565008) baseStart_1565008 baseEnd_1565008 := by
    simpa [prefixWord, tailWord_1565008, baseEnd_1565008] using wordTrace_append hprefix tailTrace_1565008
  have hstable : (prefixWord ++ tailWord_1565008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565008).length < 2 ^ (prefixWord ++ tailWord_1565008).sum := by decide
  have hdescent : baseEnd_1565008 < baseStart_1565008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565053 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_1565053 : Nat := 118140960795 + 1565053 * 2 ^ 59
def prefixEnd_1565053 : Nat := 4983230072969 + 3 ^ 40 * 1565053 * 2
def baseEnd_1565053 : Nat := 535749625840780304426639

theorem tailTrace_1565053 : CollatzResearch.WordTrace tailWord_1565053 prefixEnd_1565053 535749625840780304426639 := by
  unfold tailWord_1565053
  simp only [CollatzResearch.WordTrace]
  refine ⟨57082172399087745617483813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38054781599391830411655875 57082172399087745617483813)
  ·
    refine ⟨10702907324828952303278215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57082172399087745617483813 10702907324828952303278215)
    ·
      refine ⟨16054360987243428454917323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10702907324828952303278215 16054360987243428454917323)
      ·
        refine ⟨24081541480865142682375985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16054360987243428454917323 24081541480865142682375985)
        ·
          refine ⟨18061156110648857011781989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24081541480865142682375985 18061156110648857011781989)
          ·
            refine ⟨3386466770746660689709123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18061156110648857011781989 3386466770746660689709123)
            ·
              refine ⟨5079700156119991034563685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386466770746660689709123 5079700156119991034563685)
              ·
                refine ⟨952443779272498318980691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5079700156119991034563685 952443779272498318980691)
                ·
                  refine ⟨1428665668908747478471037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952443779272498318980691 1428665668908747478471037)
                  ·
                    refine ⟨535749625840780304426639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428665668908747478471037 535749625840780304426639)
                    ·
                      rfl

theorem cell22_1565053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_1565053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565053 prefixEnd_1565053 := by exact prefixLift 1565053
  have htrace : WordTrace (prefixWord ++ tailWord_1565053) baseStart_1565053 baseEnd_1565053 := by
    simpa [prefixWord, tailWord_1565053, baseEnd_1565053] using wordTrace_append hprefix tailTrace_1565053
  have hstable : (prefixWord ++ tailWord_1565053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565053).length < 2 ^ (prefixWord ++ tailWord_1565053).sum := by decide
  have hdescent : baseEnd_1565053 < baseStart_1565053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565064 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1565064 : Nat := 118140960795 + 1565064 * 2 ^ 59
def prefixEnd_1565064 : Nat := 4983230072969 + 3 ^ 40 * 1565064 * 2
def baseEnd_1565064 : Nat := 535753391365579942401605

theorem tailTrace_1565064 : CollatzResearch.WordTrace tailWord_1565064 prefixEnd_1565064 535753391365579942401605 := by
  unfold tailWord_1565064
  simp only [CollatzResearch.WordTrace]
  refine ⟨28541286801023947248067123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38055049068031929664089497 28541286801023947248067123)
  ·
    refine ⟨42811930201535920872100685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28541286801023947248067123 42811930201535920872100685)
    ·
      refine ⟨16054473825575970327037757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42811930201535920872100685 16054473825575970327037757)
      ·
        refine ⟨6020427684590988872639159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16054473825575970327037757 6020427684590988872639159)
        ·
          refine ⟨9030641526886483308958739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020427684590988872639159 9030641526886483308958739)
          ·
            refine ⟨13545962290329724963438109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9030641526886483308958739 13545962290329724963438109)
            ·
              refine ⟨5079735858873646861289291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13545962290329724963438109 5079735858873646861289291)
              ·
                refine ⟨7619603788310470291933937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079735858873646861289291 7619603788310470291933937)
                ·
                  refine ⟨5714702841232852718950453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7619603788310470291933937 5714702841232852718950453)
                  ·
                    refine ⟨535753391365579942401605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5714702841232852718950453 535753391365579942401605)
                    ·
                      rfl

theorem cell22_1565064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1565064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565064 prefixEnd_1565064 := by exact prefixLift 1565064
  have htrace : WordTrace (prefixWord ++ tailWord_1565064) baseStart_1565064 baseEnd_1565064 := by
    simpa [prefixWord, tailWord_1565064, baseEnd_1565064] using wordTrace_append hprefix tailTrace_1565064
  have hstable : (prefixWord ++ tailWord_1565064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565064).length < 2 ^ (prefixWord ++ tailWord_1565064).sum := by decide
  have hdescent : baseEnd_1565064 < baseStart_1565064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565079 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1565079 : Nat := 118140960795 + 1565079 * 2 ^ 59
def prefixEnd_1565079 : Nat := 4983230072969 + 3 ^ 40 * 1565079 * 2
def baseEnd_1565079 : Nat := 535758526172124903276559

theorem tailTrace_1565079 : CollatzResearch.WordTrace tailWord_1565079 prefixEnd_1565079 535758526172124903276559 := by
  unfold tailWord_1565079
  simp only [CollatzResearch.WordTrace]
  refine ⟨57083120696993552057930291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38055413797995701371953527 57083120696993552057930291)
  ·
    refine ⟨85624681045490328086895437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57083120696993552057930291 85624681045490328086895437)
    ·
      refine ⟨32109255392058873032585789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85624681045490328086895437 32109255392058873032585789)
      ·
        refine ⟨12040970772022077387219671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32109255392058873032585789 12040970772022077387219671)
        ·
          refine ⟨18061456158033116080829507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12040970772022077387219671 18061456158033116080829507)
          ·
            refine ⟨27092184237049674121244261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18061456158033116080829507 27092184237049674121244261)
            ·
              refine ⟨5079784544446813897733299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27092184237049674121244261 5079784544446813897733299)
              ·
                refine ⟨7619676816670220846599949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079784544446813897733299 7619676816670220846599949)
                ·
                  refine ⟨2857378806251332817474981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7619676816670220846599949 2857378806251332817474981)
                  ·
                    refine ⟨535758526172124903276559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2857378806251332817474981 535758526172124903276559)
                    ·
                      rfl

theorem cell22_1565079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1565079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565079 prefixEnd_1565079 := by exact prefixLift 1565079
  have htrace : WordTrace (prefixWord ++ tailWord_1565079) baseStart_1565079 baseEnd_1565079 := by
    simpa [prefixWord, tailWord_1565079, baseEnd_1565079] using wordTrace_append hprefix tailTrace_1565079
  have hstable : (prefixWord ++ tailWord_1565079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565079).length < 2 ^ (prefixWord ++ tailWord_1565079).sum := by decide
  have hdescent : baseEnd_1565079 < baseStart_1565079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565111 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 4]
def baseStart_1565111 : Nat := 118140960795 + 1565111 * 2 ^ 59
def prefixEnd_1565111 : Nat := 4983230072969 + 3 ^ 40 * 1565111 * 2
def baseEnd_1565111 : Nat := 178589826808695828825487

theorem tailTrace_1565111 : CollatzResearch.WordTrace tailWord_1565111 prefixEnd_1565111 178589826808695828825487 := by
  unfold tailWord_1565111
  simp only [CollatzResearch.WordTrace]
  refine ⟨57084287832877621523095187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38056191888585081015396791 57084287832877621523095187)
  ·
    refine ⟨85626431749316432284642781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57084287832877621523095187 85626431749316432284642781)
    ·
      refine ⟨32109911905993662106741043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85626431749316432284642781 32109911905993662106741043)
      ·
        refine ⟨48164867858990493160111565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32109911905993662106741043 48164867858990493160111565)
        ·
          refine ⟨18061825447121434935041837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48164867858990493160111565 18061825447121434935041837)
          ·
            refine ⟨6773184542670538100640689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18061825447121434935041837 6773184542670538100640689)
            ·
              refine ⟨5079888407002903575480517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6773184542670538100640689 5079888407002903575480517)
              ·
                refine ⟨952479076313044420402597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5079888407002903575480517 952479076313044420402597)
                ·
                  refine ⟨178589826808695828825487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952479076313044420402597 178589826808695828825487)
                  ·
                    rfl

theorem cell22_1565111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 4].length) (baseStart_1565111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565111 prefixEnd_1565111 := by exact prefixLift 1565111
  have htrace : WordTrace (prefixWord ++ tailWord_1565111) baseStart_1565111 baseEnd_1565111 := by
    simpa [prefixWord, tailWord_1565111, baseEnd_1565111] using wordTrace_append hprefix tailTrace_1565111
  have hstable : (prefixWord ++ tailWord_1565111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565111).length < 2 ^ (prefixWord ++ tailWord_1565111).sum := by decide
  have hdescent : baseEnd_1565111 < baseStart_1565111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565169 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1565169 : Nat := 118140960795 + 1565169 * 2 ^ 59
def prefixEnd_1565169 : Nat := 4983230072969 + 3 ^ 40 * 1565169 * 2
def baseEnd_1565169 : Nat := 535789335011394668526283

theorem tailTrace_1565169 : CollatzResearch.WordTrace tailWord_1565169 prefixEnd_1565169 535789335011394668526283 := by
  unfold tailWord_1565169
  simp only [CollatzResearch.WordTrace]
  refine ⟨57086403266667497428706561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38057602177778331619137707 57086403266667497428706561)
  ·
    refine ⟨42814802450000623071529921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57086403266667497428706561 42814802450000623071529921)
    ·
      refine ⟨32111101837500467303647441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42814802450000623071529921 32111101837500467303647441)
      ·
        refine ⟨24083326378125350477735581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32111101837500467303647441 24083326378125350477735581)
        ·
          refine ⟨9031247391797006429150843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24083326378125350477735581 9031247391797006429150843)
          ·
            refine ⟨13546871087695509643726265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031247391797006429150843 13546871087695509643726265)
            ·
              refine ⟨10160153315771632232794699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13546871087695509643726265 10160153315771632232794699)
              ·
                refine ⟨15240229973657448349192049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10160153315771632232794699 15240229973657448349192049)
                ·
                  refine ⟨11430172480243086261894037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15240229973657448349192049 11430172480243086261894037)
                  ·
                    refine ⟨535789335011394668526283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11430172480243086261894037 535789335011394668526283)
                    ·
                      rfl

theorem cell22_1565169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1565169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565169 prefixEnd_1565169 := by exact prefixLift 1565169
  have htrace : WordTrace (prefixWord ++ tailWord_1565169) baseStart_1565169 baseEnd_1565169 := by
    simpa [prefixWord, tailWord_1565169, baseEnd_1565169] using wordTrace_append hprefix tailTrace_1565169
  have hstable : (prefixWord ++ tailWord_1565169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565169).length < 2 ^ (prefixWord ++ tailWord_1565169).sum := by decide
  have hdescent : baseEnd_1565169 < baseStart_1565169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565173 : List Nat := [1, 3, 5, 1, 2, 1, 2, 7]
def baseStart_1565173 : Nat := 118140960795 + 1565173 * 2 ^ 59
def prefixEnd_1565173 : Nat := 4983230072969 + 3 ^ 40 * 1565173 * 2
def baseEnd_1565173 : Nat := 59532300477015554602919

theorem tailTrace_1565173 : CollatzResearch.WordTrace tailWord_1565173 prefixEnd_1565173 59532300477015554602919 := by
  unfold tailWord_1565173
  simp only [CollatzResearch.WordTrace]
  refine ⟨57086549158653006111852173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38057699439102004074568115 57086549158653006111852173)
  ·
    refine ⟨21407455934494877291944565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57086549158653006111852173 21407455934494877291944565)
    ·
      refine ⟨2006948993858894746119803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21407455934494877291944565 2006948993858894746119803)
      ·
        refine ⟨3010423490788342119179705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006948993858894746119803 3010423490788342119179705)
        ·
          refine ⟨2257817618091256589384779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3010423490788342119179705 2257817618091256589384779)
          ·
            refine ⟨3386726427136884884077169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257817618091256589384779 3386726427136884884077169)
            ·
              refine ⟨2540044820352663663057877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386726427136884884077169 2540044820352663663057877)
              ·
                refine ⟨59532300477015554602919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2540044820352663663057877 59532300477015554602919)
                ·
                  rfl

theorem cell22_1565173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 7].length) (baseStart_1565173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565173 prefixEnd_1565173 := by exact prefixLift 1565173
  have htrace : WordTrace (prefixWord ++ tailWord_1565173) baseStart_1565173 baseEnd_1565173 := by
    simpa [prefixWord, tailWord_1565173, baseEnd_1565173] using wordTrace_append hprefix tailTrace_1565173
  have hstable : (prefixWord ++ tailWord_1565173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565173).length < 2 ^ (prefixWord ++ tailWord_1565173).sum := by decide
  have hdescent : baseEnd_1565173 < baseStart_1565173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565190 : List Nat := [6, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1565190 : Nat := 118140960795 + 1565190 * 2 ^ 59
def prefixEnd_1565190 : Nat := 4983230072969 + 3 ^ 40 * 1565190 * 2
def baseEnd_1565190 : Nat := 59532947082284179305691

theorem tailTrace_1565190 : CollatzResearch.WordTrace tailWord_1565190 prefixEnd_1565190 59532947082284179305691 := by
  unfold tailWord_1565190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783974037487231812975657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38058112799727612010147349 1783974037487231812975657)
  ·
    refine ⟨1337980528115423859731743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1783974037487231812975657 1337980528115423859731743)
    ·
      refine ⟨2006970792173135789597615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337980528115423859731743 2006970792173135789597615)
      ·
        refine ⟨3010456188259703684396423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006970792173135789597615 3010456188259703684396423)
        ·
          refine ⟨4515684282389555526594635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010456188259703684396423 4515684282389555526594635)
          ·
            refine ⟨6773526423584333289891953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515684282389555526594635 6773526423584333289891953)
            ·
              refine ⟨5080144817688249967418965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6773526423584333289891953 5080144817688249967418965)
              ·
                refine ⟨59532947082284179305691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5080144817688249967418965 59532947082284179305691)
                ·
                  rfl

theorem cell22_1565190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1565190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565190 prefixEnd_1565190 := by exact prefixLift 1565190
  have htrace : WordTrace (prefixWord ++ tailWord_1565190) baseStart_1565190 baseEnd_1565190 := by
    simpa [prefixWord, tailWord_1565190, baseEnd_1565190] using wordTrace_append hprefix tailTrace_1565190
  have hstable : (prefixWord ++ tailWord_1565190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565190).length < 2 ^ (prefixWord ++ tailWord_1565190).sum := by decide
  have hdescent : baseEnd_1565190 < baseStart_1565190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565265 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 1, 4]
def baseStart_1565265 : Nat := 118140960795 + 1565265 * 2 ^ 59
def prefixEnd_1565265 : Nat := 4983230072969 + 3 ^ 40 * 1565265 * 2
def baseEnd_1565265 : Nat := 535822197773282418125989

theorem tailTrace_1565265 : CollatzResearch.WordTrace tailWord_1565265 prefixEnd_1565265 535822197773282418125989 := by
  unfold tailWord_1565265
  simp only [CollatzResearch.WordTrace]
  refine ⟨57089904674319705824201249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38059936449546470549467499 57089904674319705824201249)
  ·
    refine ⟨42817428505739779368150937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57089904674319705824201249 42817428505739779368150937)
    ·
      refine ⟨32113071379304834526113203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42817428505739779368150937 32113071379304834526113203)
      ·
        refine ⟨48169607068957251789169805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32113071379304834526113203 48169607068957251789169805)
        ·
          refine ⟨18063602650858969420938677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48169607068957251789169805 18063602650858969420938677)
          ·
            refine ⟨1693462748518028383213001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18063602650858969420938677 1693462748518028383213001)
            ·
              refine ⟨1270097061388521287409751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693462748518028383213001 1270097061388521287409751)
              ·
                refine ⟨1905145592082781931114627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270097061388521287409751 1905145592082781931114627)
                ·
                  refine ⟨2857718388124172896671941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905145592082781931114627 2857718388124172896671941)
                  ·
                    refine ⟨535822197773282418125989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2857718388124172896671941 535822197773282418125989)
                    ·
                      rfl

theorem cell22_1565265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_1565265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565265 prefixEnd_1565265 := by exact prefixLift 1565265
  have htrace : WordTrace (prefixWord ++ tailWord_1565265) baseStart_1565265 baseEnd_1565265 := by
    simpa [prefixWord, tailWord_1565265, baseEnd_1565265] using wordTrace_append hprefix tailTrace_1565265
  have hstable : (prefixWord ++ tailWord_1565265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565265).length < 2 ^ (prefixWord ++ tailWord_1565265).sum := by decide
  have hdescent : baseEnd_1565265 < baseStart_1565265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565336 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_1565336 : Nat := 118140960795 + 1565336 * 2 ^ 59
def prefixEnd_1565336 : Nat := 4983230072969 + 3 ^ 40 * 1565336 * 2
def baseEnd_1565336 : Nat := 178615500841420633200257

theorem tailTrace_1565336 : CollatzResearch.WordTrace tailWord_1565336 prefixEnd_1565336 178615500841420633200257 := by
  unfold tailWord_1565336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28546247128531242475017931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38061662838041656633357241 28546247128531242475017931)
  ·
    refine ⟨42819370692796863712526897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28546247128531242475017931 42819370692796863712526897)
    ·
      refine ⟨32114528019597647784395173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42819370692796863712526897 32114528019597647784395173)
      ·
        refine ⟨6021474003674558959574095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32114528019597647784395173 6021474003674558959574095)
        ·
          refine ⟨9032211005511838439361143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021474003674558959574095 9032211005511838439361143)
          ·
            refine ⟨13548316508267757659041715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9032211005511838439361143 13548316508267757659041715)
            ·
              refine ⟨20322474762401636488562573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13548316508267757659041715 20322474762401636488562573)
              ·
                refine ⟨7620928035900613683210965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20322474762401636488562573 7620928035900613683210965)
                ·
                  refine ⟨178615500841420633200257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7620928035900613683210965 178615500841420633200257)
                  ·
                    rfl

theorem cell22_1565336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_1565336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565336 prefixEnd_1565336 := by exact prefixLift 1565336
  have htrace : WordTrace (prefixWord ++ tailWord_1565336) baseStart_1565336 baseEnd_1565336 := by
    simpa [prefixWord, tailWord_1565336, baseEnd_1565336] using wordTrace_append hprefix tailTrace_1565336
  have hstable : (prefixWord ++ tailWord_1565336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565336).length < 2 ^ (prefixWord ++ tailWord_1565336).sum := by decide
  have hdescent : baseEnd_1565336 < baseStart_1565336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565340 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1565340 : Nat := 118140960795 + 1565340 * 2 ^ 59
def prefixEnd_1565340 : Nat := 4983230072969 + 3 ^ 40 * 1565340 * 2
def baseEnd_1565340 : Nat := 535847871806007222500759

theorem tailTrace_1565340 : CollatzResearch.WordTrace tailWord_1565340 prefixEnd_1565340 535847871806007222500759 := by
  unfold tailWord_1565340
  simp only [CollatzResearch.WordTrace]
  refine ⟨28546320074523996816590737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38061760099365329088787649 28546320074523996816590737)
  ·
    refine ⟨21409740055892997612443053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28546320074523996816590737 21409740055892997612443053)
    ·
      refine ⟨8028652520959874104666145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21409740055892997612443053 8028652520959874104666145)
      ·
        refine ⟨6021489390719905578499609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8028652520959874104666145 6021489390719905578499609)
        ·
          refine ⟨4516117043039929183874707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6021489390719905578499609 4516117043039929183874707)
          ·
            refine ⟨6774175564559893775812061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516117043039929183874707 6774175564559893775812061)
            ·
              refine ⟨2540315836709960165929523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6774175564559893775812061 2540315836709960165929523)
              ·
                refine ⟨3810473755064940248894285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540315836709960165929523 3810473755064940248894285)
                ·
                  refine ⟨1428927658149352593335357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3810473755064940248894285 1428927658149352593335357)
                  ·
                    refine ⟨535847871806007222500759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428927658149352593335357 535847871806007222500759)
                    ·
                      rfl

theorem cell22_1565340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1565340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565340 prefixEnd_1565340 := by exact prefixLift 1565340
  have htrace : WordTrace (prefixWord ++ tailWord_1565340) baseStart_1565340 baseEnd_1565340 := by
    simpa [prefixWord, tailWord_1565340, baseEnd_1565340] using wordTrace_append hprefix tailTrace_1565340
  have hstable : (prefixWord ++ tailWord_1565340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565340).length < 2 ^ (prefixWord ++ tailWord_1565340).sum := by decide
  have hdescent : baseEnd_1565340 < baseStart_1565340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565413 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_1565413 : Nat := 118140960795 + 1565413 * 2 ^ 59
def prefixEnd_1565413 : Nat := 4983230072969 + 3 ^ 40 * 1565413 * 2
def baseEnd_1565413 : Nat := 535872861197859365425535

theorem tailTrace_1565413 : CollatzResearch.WordTrace tailWord_1565413 prefixEnd_1565413 535872861197859365425535 := by
  unfold tailWord_1565413
  simp only [CollatzResearch.WordTrace]
  refine ⟨57095302677783527100588893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38063535118522351400392595 57095302677783527100588893)
  ·
    refine ⟨21410738504168822662720835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57095302677783527100588893 21410738504168822662720835)
    ·
      refine ⟨32116107756253233994081253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21410738504168822662720835 32116107756253233994081253)
      ·
        refine ⟨6021770204297481373890235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32116107756253233994081253 6021770204297481373890235)
        ·
          refine ⟨9032655306446222060835353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021770204297481373890235 9032655306446222060835353)
          ·
            refine ⟨6774491479834666545626515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9032655306446222060835353 6774491479834666545626515)
            ·
              refine ⟨10161737219751999818439773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774491479834666545626515 10161737219751999818439773)
              ·
                refine ⟨3810651457406999931914915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10161737219751999818439773 3810651457406999931914915)
                ·
                  refine ⟨5715977186110499897872373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810651457406999931914915 5715977186110499897872373)
                  ·
                    refine ⟨535872861197859365425535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5715977186110499897872373 535872861197859365425535)
                    ·
                      rfl

theorem cell22_1565413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_1565413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565413 prefixEnd_1565413 := by exact prefixLift 1565413
  have htrace : WordTrace (prefixWord ++ tailWord_1565413) baseStart_1565413 baseEnd_1565413 := by
    simpa [prefixWord, tailWord_1565413, baseEnd_1565413] using wordTrace_append hprefix tailTrace_1565413
  have hstable : (prefixWord ++ tailWord_1565413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565413).length < 2 ^ (prefixWord ++ tailWord_1565413).sum := by decide
  have hdescent : baseEnd_1565413 < baseStart_1565413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565430 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_1565430 : Nat := 118140960795 + 1565430 * 2 ^ 59
def prefixEnd_1565430 : Nat := 4983230072969 + 3 ^ 40 * 1565430 * 2
def baseEnd_1565430 : Nat := 535878680645276987750483

theorem tailTrace_1565430 : CollatzResearch.WordTrace tailWord_1565430 prefixEnd_1565430 535878680645276987750483 := by
  unfold tailWord_1565430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568495169920121187747359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38063948479147959335971829 3568495169920121187747359)
  ·
    refine ⟨5352742754880181781621039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3568495169920121187747359 5352742754880181781621039)
    ·
      refine ⟨8029114132320272672431559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5352742754880181781621039 8029114132320272672431559)
      ·
        refine ⟨12043671198480409008647339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8029114132320272672431559 12043671198480409008647339)
        ·
          refine ⟨18065506797720613512971009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043671198480409008647339 18065506797720613512971009)
          ·
            refine ⟨13549130098290460134728257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18065506797720613512971009 13549130098290460134728257)
            ·
              refine ⟨10161847573717845101046193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13549130098290460134728257 10161847573717845101046193)
              ·
                refine ⟨7621385680288383825784645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10161847573717845101046193 7621385680288383825784645)
                ·
                  refine ⟨1429009815054071967334621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7621385680288383825784645 1429009815054071967334621)
                  ·
                    refine ⟨535878680645276987750483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429009815054071967334621 535878680645276987750483)
                    ·
                      rfl

theorem cell22_1565430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_1565430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565430 prefixEnd_1565430 := by exact prefixLift 1565430
  have htrace : WordTrace (prefixWord ++ tailWord_1565430) baseStart_1565430 baseEnd_1565430 := by
    simpa [prefixWord, tailWord_1565430, baseEnd_1565430] using wordTrace_append hprefix tailTrace_1565430
  have hstable : (prefixWord ++ tailWord_1565430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565430).length < 2 ^ (prefixWord ++ tailWord_1565430).sum := by decide
  have hdescent : baseEnd_1565430 < baseStart_1565430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565447 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 2, 3]
def baseStart_1565447 : Nat := 118140960795 + 1565447 * 2 ^ 59
def prefixEnd_1565447 : Nat := 4983230072969 + 3 ^ 40 * 1565447 * 2
def baseEnd_1565447 : Nat := 535884500092694610075431

theorem tailTrace_1565447 : CollatzResearch.WordTrace tailWord_1565447 prefixEnd_1565447 535884500092694610075431 := by
  unfold tailWord_1565447
  simp only [CollatzResearch.WordTrace]
  refine ⟨57096542759660350907326595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38064361839773567271551063 57096542759660350907326595)
  ·
    refine ⟨85644814139490526360989893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57096542759660350907326595 85644814139490526360989893)
    ·
      refine ⟨16058402651154473692685605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85644814139490526360989893 16058402651154473692685605)
      ·
        refine ⟨3010950497091463817378551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16058402651154473692685605 3010950497091463817378551)
        ·
          refine ⟨4516425745637195726067827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010950497091463817378551 4516425745637195726067827)
          ·
            refine ⟨6774638618455793589101741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516425745637195726067827 6774638618455793589101741)
            ·
              refine ⟨2540489481920922595913153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6774638618455793589101741 2540489481920922595913153)
              ·
                refine ⟨1905367111440691946934865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540489481920922595913153 1905367111440691946934865)
                ·
                  refine ⟨1429025333580518960201149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905367111440691946934865 1429025333580518960201149)
                  ·
                    refine ⟨535884500092694610075431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429025333580518960201149 535884500092694610075431)
                    ·
                      rfl

theorem cell22_1565447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_1565447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565447 prefixEnd_1565447 := by exact prefixLift 1565447
  have htrace : WordTrace (prefixWord ++ tailWord_1565447) baseStart_1565447 baseEnd_1565447 := by
    simpa [prefixWord, tailWord_1565447, baseEnd_1565447] using wordTrace_append hprefix tailTrace_1565447
  have hstable : (prefixWord ++ tailWord_1565447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565447).length < 2 ^ (prefixWord ++ tailWord_1565447).sum := by decide
  have hdescent : baseEnd_1565447 < baseStart_1565447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565565 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1565565 : Nat := 118140960795 + 1565565 * 2 ^ 59
def prefixEnd_1565565 : Nat := 4983230072969 + 3 ^ 40 * 1565565 * 2
def baseEnd_1565565 : Nat := 535924893904181635625069

theorem tailTrace_1565565 : CollatzResearch.WordTrace tailWord_1565565 prefixEnd_1565565 535924893904181635625069 := by
  unfold tailWord_1565565
  simp only [CollatzResearch.WordTrace]
  refine ⟨57100846573232857060122149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38067231048821904706748099 57100846573232857060122149)
  ·
    refine ⟨10706408732481160698772903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57100846573232857060122149 10706408732481160698772903)
    ·
      refine ⟨16059613098721741048159355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10706408732481160698772903 16059613098721741048159355)
      ·
        refine ⟨24089419648082611572239033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16059613098721741048159355 24089419648082611572239033)
        ·
          refine ⟨18067064736061958679179275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24089419648082611572239033 18067064736061958679179275)
          ·
            refine ⟨27100597104092938018768913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18067064736061958679179275 27100597104092938018768913)
            ·
              refine ⟨20325447828069703514076685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27100597104092938018768913 20325447828069703514076685)
              ·
                refine ⟨7622042935526138817778757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20325447828069703514076685 7622042935526138817778757)
                ·
                  refine ⟨1429133050411151028333517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7622042935526138817778757 1429133050411151028333517)
                  ·
                    refine ⟨535924893904181635625069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429133050411151028333517 535924893904181635625069)
                    ·
                      rfl

theorem cell22_1565565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1565565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565565 prefixEnd_1565565 := by exact prefixLift 1565565
  have htrace : WordTrace (prefixWord ++ tailWord_1565565) baseStart_1565565 baseEnd_1565565 := by
    simpa [prefixWord, tailWord_1565565, baseEnd_1565565] using wordTrace_append hprefix tailTrace_1565565
  have hstable : (prefixWord ++ tailWord_1565565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565565).length < 2 ^ (prefixWord ++ tailWord_1565565).sum := by decide
  have hdescent : baseEnd_1565565 < baseStart_1565565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565567 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 4]
def baseStart_1565567 : Nat := 118140960795 + 1565567 * 2 ^ 59
def prefixEnd_1565567 : Nat := 4983230072969 + 3 ^ 40 * 1565567 * 2
def baseEnd_1565567 : Nat := 178641859515018099025021

theorem tailTrace_1565567 : CollatzResearch.WordTrace tailWord_1565567 prefixEnd_1565567 178641859515018099025021 := by
  unfold tailWord_1565567
  simp only [CollatzResearch.WordTrace]
  refine ⟨57100919519225611401694955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38067279679483740934463303 57100919519225611401694955)
  ·
    refine ⟨85651379278838417102542433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57100919519225611401694955 85651379278838417102542433)
    ·
      refine ⟨64238534459128812826906825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85651379278838417102542433 64238534459128812826906825)
      ·
        refine ⟨48178900844346609620180119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64238534459128812826906825 48178900844346609620180119)
        ·
          refine ⟨72268351266519914430270179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48178900844346609620180119 72268351266519914430270179)
          ·
            refine ⟨108402526899779871645405269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72268351266519914430270179 108402526899779871645405269)
            ·
              refine ⟨1270342112106795370844593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 108402526899779871645405269 1270342112106795370844593)
              ·
                refine ⟨952756584080096528133445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270342112106795370844593 952756584080096528133445)
                ·
                  refine ⟨178641859515018099025021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952756584080096528133445 178641859515018099025021)
                  ·
                    rfl

theorem cell22_1565567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 4].length) (baseStart_1565567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565567 prefixEnd_1565567 := by exact prefixLift 1565567
  have htrace : WordTrace (prefixWord ++ tailWord_1565567) baseStart_1565567 baseEnd_1565567 := by
    simpa [prefixWord, tailWord_1565567, baseEnd_1565567] using wordTrace_append hprefix tailTrace_1565567
  have hstable : (prefixWord ++ tailWord_1565567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565567).length < 2 ^ (prefixWord ++ tailWord_1565567).sum := by decide
  have hdescent : baseEnd_1565567 < baseStart_1565567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565661 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1565661 : Nat := 118140960795 + 1565661 * 2 ^ 59
def prefixEnd_1565661 : Nat := 4983230072969 + 3 ^ 40 * 1565661 * 2
def baseEnd_1565661 : Nat := 535957756666069385224775

theorem tailTrace_1565661 : CollatzResearch.WordTrace tailWord_1565661 prefixEnd_1565661 535957756666069385224775 := by
  unfold tailWord_1565661
  simp only [CollatzResearch.WordTrace]
  refine ⟨57104347980885065455616837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38069565320590043637077891 57104347980885065455616837)
  ·
    refine ⟨10707065246415949772928157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57104347980885065455616837 10707065246415949772928157)
    ·
      refine ⟨4015149467405981164848059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10707065246415949772928157 4015149467405981164848059)
      ·
        refine ⟨6022724201108971747272089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015149467405981164848059 6022724201108971747272089)
        ·
          refine ⟨4517043150831728810454067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6022724201108971747272089 4517043150831728810454067)
          ·
            refine ⟨6775564726247593215681101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517043150831728810454067 6775564726247593215681101)
            ·
              refine ⟨2540836772342847455880413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6775564726247593215681101 2540836772342847455880413)
              ·
                refine ⟨952813789628567795955155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2540836772342847455880413 952813789628567795955155)
                ·
                  refine ⟨1429220684442851693932733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952813789628567795955155 1429220684442851693932733)
                  ·
                    refine ⟨535957756666069385224775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429220684442851693932733 535957756666069385224775)
                    ·
                      rfl

theorem cell22_1565661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1565661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565661 prefixEnd_1565661 := by exact prefixLift 1565661
  have htrace : WordTrace (prefixWord ++ tailWord_1565661) baseStart_1565661 baseEnd_1565661 := by
    simpa [prefixWord, tailWord_1565661, baseEnd_1565661] using wordTrace_append hprefix tailTrace_1565661
  have hstable : (prefixWord ++ tailWord_1565661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565661).length < 2 ^ (prefixWord ++ tailWord_1565661).sum := by decide
  have hdescent : baseEnd_1565661 < baseStart_1565661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565678 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1565678 : Nat := 118140960795 + 1565678 * 2 ^ 59
def prefixEnd_1565678 : Nat := 4983230072969 + 3 ^ 40 * 1565678 * 2
def baseEnd_1565678 : Nat := 535963576113487007549723

theorem tailTrace_1565678 : CollatzResearch.WordTrace tailWord_1565678 prefixEnd_1565678 535963576113487007549723 := by
  unfold tailWord_1565678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7138121002727934669873211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38069978681215651572657125 7138121002727934669873211)
  ·
    refine ⟨10707181504091902004809817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7138121002727934669873211 10707181504091902004809817)
    ·
      refine ⟨8030386128068926503607363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10707181504091902004809817 8030386128068926503607363)
      ·
        refine ⟨12045579192103389755411045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030386128068926503607363 12045579192103389755411045)
        ·
          refine ⟨2258546098519385579139571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12045579192103389755411045 2258546098519385579139571)
          ·
            refine ⟨3387819147779078368709357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258546098519385579139571 3387819147779078368709357)
            ·
              refine ⟨1270432180417154388266009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3387819147779078368709357 1270432180417154388266009)
              ·
                refine ⟨952824135312865791199507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270432180417154388266009 952824135312865791199507)
                ·
                  refine ⟨1429236202969298686799261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952824135312865791199507 1429236202969298686799261)
                  ·
                    refine ⟨535963576113487007549723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429236202969298686799261 535963576113487007549723)
                    ·
                      rfl

theorem cell22_1565678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1565678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565678 prefixEnd_1565678 := by exact prefixLift 1565678
  have htrace : WordTrace (prefixWord ++ tailWord_1565678) baseStart_1565678 baseEnd_1565678 := by
    simpa [prefixWord, tailWord_1565678, baseEnd_1565678] using wordTrace_append hprefix tailTrace_1565678
  have hstable : (prefixWord ++ tailWord_1565678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565678).length < 2 ^ (prefixWord ++ tailWord_1565678).sum := by decide
  have hdescent : baseEnd_1565678 < baseStart_1565678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565684 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1565684 : Nat := 118140960795 + 1565684 * 2 ^ 59
def prefixEnd_1565684 : Nat := 4983230072969 + 3 ^ 40 * 1565684 * 2
def baseEnd_1565684 : Nat := 535965630036104991899705

theorem tailTrace_1565684 : CollatzResearch.WordTrace tailWord_1565684 prefixEnd_1565684 535965630036104991899705 := by
  unfold tailWord_1565684
  simp only [CollatzResearch.WordTrace]
  refine ⟨28552593429900870191852053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38070124573201160255802737 28552593429900870191852053)
  ·
    refine ⟨1338402817026603290243065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28552593429900870191852053 1338402817026603290243065)
    ·
      refine ⟨1003802112769952467682299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1338402817026603290243065 1003802112769952467682299)
      ·
        refine ⟨1505703169154928701523449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003802112769952467682299 1505703169154928701523449)
        ·
          refine ⟨1129277376866196526142587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1505703169154928701523449 1129277376866196526142587)
          ·
            refine ⟨1693916065299294789213881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129277376866196526142587 1693916065299294789213881)
            ·
              refine ⟨1270437048974471091910411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693916065299294789213881 1270437048974471091910411)
              ·
                refine ⟨1905655573461706637865617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270437048974471091910411 1905655573461706637865617)
                ·
                  refine ⟨1429241680096279978399213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905655573461706637865617 1429241680096279978399213)
                  ·
                    refine ⟨535965630036104991899705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429241680096279978399213 535965630036104991899705)
                    ·
                      rfl

theorem cell22_1565684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1565684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565684 prefixEnd_1565684 := by exact prefixLift 1565684
  have htrace : WordTrace (prefixWord ++ tailWord_1565684) baseStart_1565684 baseEnd_1565684 := by
    simpa [prefixWord, tailWord_1565684, baseEnd_1565684] using wordTrace_append hprefix tailTrace_1565684
  have hstable : (prefixWord ++ tailWord_1565684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565684).length < 2 ^ (prefixWord ++ tailWord_1565684).sum := by decide
  have hdescent : baseEnd_1565684 < baseStart_1565684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565704 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_1565704 : Nat := 118140960795 + 1565704 * 2 ^ 59
def prefixEnd_1565704 : Nat := 4983230072969 + 3 ^ 40 * 1565704 * 2
def baseEnd_1565704 : Nat := 535972476444831606399643

theorem tailTrace_1565704 : CollatzResearch.WordTrace tailWord_1565704 prefixEnd_1565704 535972476444831606399643 := by
  unfold tailWord_1565704
  simp only [CollatzResearch.WordTrace]
  refine ⟨28552958159864641899716083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38070610879819522532954777 28552958159864641899716083)
  ·
    refine ⟨42829437239796962849574125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28552958159864641899716083 42829437239796962849574125)
    ·
      refine ⟨16061038964923861068590297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42829437239796962849574125 16061038964923861068590297)
      ·
        refine ⟨12045779223692895801442723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16061038964923861068590297 12045779223692895801442723)
        ·
          refine ⟨18068668835539343702164085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12045779223692895801442723 18068668835539343702164085)
          ·
            refine ⟨1693937703331813472077883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18068668835539343702164085 1693937703331813472077883)
            ·
              refine ⟨2540906554997720208116825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693937703331813472077883 2540906554997720208116825)
              ·
                refine ⟨1905679916248290156087619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540906554997720208116825 1905679916248290156087619)
                ·
                  refine ⟨2858519874372435234131429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905679916248290156087619 2858519874372435234131429)
                  ·
                    refine ⟨535972476444831606399643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858519874372435234131429 535972476444831606399643)
                    ·
                      rfl

theorem cell22_1565704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_1565704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565704 prefixEnd_1565704 := by exact prefixLift 1565704
  have htrace : WordTrace (prefixWord ++ tailWord_1565704) baseStart_1565704 baseEnd_1565704 := by
    simpa [prefixWord, tailWord_1565704, baseEnd_1565704] using wordTrace_append hprefix tailTrace_1565704
  have hstable : (prefixWord ++ tailWord_1565704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565704).length < 2 ^ (prefixWord ++ tailWord_1565704).sum := by decide
  have hdescent : baseEnd_1565704 < baseStart_1565704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565717 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1565717 : Nat := 118140960795 + 1565717 * 2 ^ 59
def prefixEnd_1565717 : Nat := 4983230072969 + 3 ^ 40 * 1565717 * 2
def baseEnd_1565717 : Nat := 535976926610503905824603

theorem tailTrace_1565717 : CollatzResearch.WordTrace tailWord_1565717 prefixEnd_1565717 535976926610503905824603 := by
  unfold tailWord_1565717
  simp only [CollatzResearch.WordTrace]
  refine ⟨57106390468682187019655405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38070926979121458013103603 57106390468682187019655405)
  ·
    refine ⟨21414896425755820132370777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57106390468682187019655405 21414896425755820132370777)
    ·
      refine ⟨16061172319316865099278083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21414896425755820132370777 16061172319316865099278083)
      ·
        refine ⟨24091758478975297648917125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061172319316865099278083 24091758478975297648917125)
        ·
          refine ⟨4517204714807868309171961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24091758478975297648917125 4517204714807868309171961)
          ·
            refine ⟨3387903536105901231878971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517204714807868309171961 3387903536105901231878971)
            ·
              refine ⟨5081855304158851847818457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387903536105901231878971 5081855304158851847818457)
              ·
                refine ⟨3811391478119138885863843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081855304158851847818457 3811391478119138885863843)
                ·
                  refine ⟨5717087217178708328795765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811391478119138885863843 5717087217178708328795765)
                  ·
                    refine ⟨535976926610503905824603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5717087217178708328795765 535976926610503905824603)
                    ·
                      rfl

theorem cell22_1565717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1565717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565717 prefixEnd_1565717 := by exact prefixLift 1565717
  have htrace : WordTrace (prefixWord ++ tailWord_1565717) baseStart_1565717 baseEnd_1565717 := by
    simpa [prefixWord, tailWord_1565717, baseEnd_1565717] using wordTrace_append hprefix tailTrace_1565717
  have hstable : (prefixWord ++ tailWord_1565717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565717).length < 2 ^ (prefixWord ++ tailWord_1565717).sum := by decide
  have hdescent : baseEnd_1565717 < baseStart_1565717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565730 : List Nat := [3, 3, 1, 1, 1, 13]
def baseStart_1565730 : Nat := 118140960795 + 1565730 * 2 ^ 59
def prefixEnd_1565730 : Nat := 4983230072969 + 3 ^ 40 * 1565730 * 2
def baseEnd_1565730 : Nat := 6617054034273780311723

theorem tailTrace_1565730 : CollatzResearch.WordTrace tailWord_1565730 prefixEnd_1565730 6617054034273780311723 := by
  unfold tailWord_1565730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14276716154408772559969661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38071243078423393493252429 14276716154408772559969661)
  ·
    refine ⟨5353768557903289709988623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14276716154408772559969661 5353768557903289709988623)
    ·
      refine ⟨8030652836854934564982935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5353768557903289709988623 8030652836854934564982935)
      ·
        refine ⟨12045979255282401847474403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030652836854934564982935 12045979255282401847474403)
        ·
          refine ⟨18068968882923602771211605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12045979255282401847474403 18068968882923602771211605)
          ·
            refine ⟨6617054034273780311723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 18068968882923602771211605 6617054034273780311723)
            ·
              rfl

theorem cell22_1565730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 13].length) (baseStart_1565730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565730 prefixEnd_1565730 := by exact prefixLift 1565730
  have htrace : WordTrace (prefixWord ++ tailWord_1565730) baseStart_1565730 baseEnd_1565730 := by
    simpa [prefixWord, tailWord_1565730, baseEnd_1565730] using wordTrace_append hprefix tailTrace_1565730
  have hstable : (prefixWord ++ tailWord_1565730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565730).length < 2 ^ (prefixWord ++ tailWord_1565730).sum := by decide
  have hdescent : baseEnd_1565730 < baseStart_1565730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565760 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_1565760 : Nat := 118140960795 + 1565760 * 2 ^ 59
def prefixEnd_1565760 : Nat := 4983230072969 + 3 ^ 40 * 1565760 * 2
def baseEnd_1565760 : Nat := 535991646389266126999471

theorem tailTrace_1565760 : CollatzResearch.WordTrace tailWord_1565760 prefixEnd_1565760 535991646389266126999471 := by
  unfold tailWord_1565760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28553979403763202681735367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38071972538350936908980489 28553979403763202681735367)
  ·
    refine ⟨42830969105644804022603051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28553979403763202681735367 42830969105644804022603051)
    ·
      refine ⟨64246453658467206033904577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42830969105644804022603051 64246453658467206033904577)
      ·
        refine ⟨48184840243850404525428433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64246453658467206033904577 48184840243850404525428433)
        ·
          refine ⟨36138630182887803394071325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48184840243850404525428433 36138630182887803394071325)
          ·
            refine ⟨13551986318582926272776747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36138630182887803394071325 13551986318582926272776747)
            ·
              refine ⟨20327979477874389409165121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13551986318582926272776747 20327979477874389409165121)
              ·
                refine ⟨15245984608405792056873841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20327979477874389409165121 15245984608405792056873841)
                ·
                  refine ⟨11434488456304344042655381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15245984608405792056873841 11434488456304344042655381)
                  ·
                    refine ⟨535991646389266126999471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11434488456304344042655381 535991646389266126999471)
                    ·
                      rfl

theorem cell22_1565760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_1565760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565760 prefixEnd_1565760 := by exact prefixLift 1565760
  have htrace : WordTrace (prefixWord ++ tailWord_1565760) baseStart_1565760 baseEnd_1565760 := by
    simpa [prefixWord, tailWord_1565760, baseEnd_1565760] using wordTrace_append hprefix tailTrace_1565760
  have hstable : (prefixWord ++ tailWord_1565760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565760).length < 2 ^ (prefixWord ++ tailWord_1565760).sum := by decide
  have hdescent : baseEnd_1565760 < baseStart_1565760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565766 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1565766 : Nat := 118140960795 + 1565766 * 2 ^ 59
def prefixEnd_1565766 : Nat := 4983230072969 + 3 ^ 40 * 1565766 * 2
def baseEnd_1565766 : Nat := 535993700311884111349453

theorem tailTrace_1565766 : CollatzResearch.WordTrace tailWord_1565766 prefixEnd_1565766 535993700311884111349453 := by
  unfold tailWord_1565766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784630551422020887130911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38072118430336445592126101 1784630551422020887130911)
  ·
    refine ⟨2676945827133031330696367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784630551422020887130911 2676945827133031330696367)
    ·
      refine ⟨4015418740699546996044551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676945827133031330696367 4015418740699546996044551)
      ·
        refine ⟨6023128111049320494066827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015418740699546996044551 6023128111049320494066827)
        ·
          refine ⟨9034692166573980741100241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6023128111049320494066827 9034692166573980741100241)
          ·
            refine ⟨6776019124930485555825181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9034692166573980741100241 6776019124930485555825181)
            ·
              refine ⟨2541007171848932083434443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6776019124930485555825181 2541007171848932083434443)
              ·
                refine ⟨3811510757773398125151665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541007171848932083434443 3811510757773398125151665)
                ·
                  refine ⟨2858633068330048593863749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3811510757773398125151665 2858633068330048593863749)
                  ·
                    refine ⟨535993700311884111349453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858633068330048593863749 535993700311884111349453)
                    ·
                      rfl

theorem cell22_1565766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1565766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565766 prefixEnd_1565766 := by exact prefixLift 1565766
  have htrace : WordTrace (prefixWord ++ tailWord_1565766) baseStart_1565766 baseEnd_1565766 := by
    simpa [prefixWord, tailWord_1565766, baseEnd_1565766] using wordTrace_append hprefix tailTrace_1565766
  have hstable : (prefixWord ++ tailWord_1565766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565766).length < 2 ^ (prefixWord ++ tailWord_1565766).sum := by decide
  have hdescent : baseEnd_1565766 < baseStart_1565766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565779 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 1, 3]
def baseStart_1565779 : Nat := 118140960795 + 1565779 * 2 ^ 59
def prefixEnd_1565779 : Nat := 4983230072969 + 3 ^ 40 * 1565779 * 2
def baseEnd_1565779 : Nat := 535998150477556410774413

theorem tailTrace_1565779 : CollatzResearch.WordTrace tailWord_1565779 prefixEnd_1565779 535998150477556410774413 := by
  unfold tailWord_1565779
  simp only [CollatzResearch.WordTrace]
  refine ⟨57108651794457571608412391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38072434529638381072274927 57108651794457571608412391)
  ·
    refine ⟨85662977691686357412618587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57108651794457571608412391 85662977691686357412618587)
    ·
      refine ⟨128494466537529536118927881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85662977691686357412618587 128494466537529536118927881)
      ·
        refine ⟨96370849903147152089195911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128494466537529536118927881 96370849903147152089195911)
        ·
          refine ⟨144556274854720728133793867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96370849903147152089195911 144556274854720728133793867)
          ·
            refine ⟨216834412282081092200690801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144556274854720728133793867 216834412282081092200690801)
            ·
              refine ⟨162625809211560819150518101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216834412282081092200690801 162625809211560819150518101)
              ·
                refine ⟨952885600848989174710067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 162625809211560819150518101 952885600848989174710067)
                ·
                  refine ⟨1429328401273483762065101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952885600848989174710067 1429328401273483762065101)
                  ·
                    refine ⟨535998150477556410774413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429328401273483762065101 535998150477556410774413)
                    ·
                      rfl

theorem cell22_1565779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 3].length) (baseStart_1565779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565779 prefixEnd_1565779 := by exact prefixLift 1565779
  have htrace : WordTrace (prefixWord ++ tailWord_1565779) baseStart_1565779 baseEnd_1565779 := by
    simpa [prefixWord, tailWord_1565779, baseEnd_1565779] using wordTrace_append hprefix tailTrace_1565779
  have hstable : (prefixWord ++ tailWord_1565779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565779).length < 2 ^ (prefixWord ++ tailWord_1565779).sum := by decide
  have hdescent : baseEnd_1565779 < baseStart_1565779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565884 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1565884 : Nat := 118140960795 + 1565884 * 2 ^ 59
def prefixEnd_1565884 : Nat := 4983230072969 + 3 ^ 40 * 1565884 * 2
def baseEnd_1565884 : Nat := 536034094123371136899091

theorem tailTrace_1565884 : CollatzResearch.WordTrace tailWord_1565884 prefixEnd_1565884 536034094123371136899091 := by
  unfold tailWord_1565884
  simp only [CollatzResearch.WordTrace]
  refine ⟨28556240729538587270492353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38074987639384783027323137 28556240729538587270492353)
  ·
    refine ⟨21417180547153940452869265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28556240729538587270492353 21417180547153940452869265)
    ·
      refine ⟨16062885410365455339651949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21417180547153940452869265 16062885410365455339651949)
      ·
        refine ⟨6023582028887045752369481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16062885410365455339651949 6023582028887045752369481)
        ·
          refine ⟨4517686521665284314277111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6023582028887045752369481 4517686521665284314277111)
          ·
            refine ⟨6776529782497926471415667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517686521665284314277111 6776529782497926471415667)
            ·
              refine ⟨10164794673746889707123501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776529782497926471415667 10164794673746889707123501)
              ·
                refine ⟨3811798002655083640171313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10164794673746889707123501 3811798002655083640171313)
                ·
                  refine ⟨2858848501991312730128485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3811798002655083640171313 2858848501991312730128485)
                  ·
                    refine ⟨536034094123371136899091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858848501991312730128485 536034094123371136899091)
                    ·
                      rfl

theorem cell22_1565884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1565884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565884 prefixEnd_1565884 := by exact prefixLift 1565884
  have htrace : WordTrace (prefixWord ++ tailWord_1565884) baseStart_1565884 baseEnd_1565884 := by
    simpa [prefixWord, tailWord_1565884, baseEnd_1565884] using wordTrace_append hprefix tailTrace_1565884
  have hstable : (prefixWord ++ tailWord_1565884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565884).length < 2 ^ (prefixWord ++ tailWord_1565884).sum := by decide
  have hdescent : baseEnd_1565884 < baseStart_1565884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565914 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_1565914 : Nat := 118140960795 + 1565914 * 2 ^ 59
def prefixEnd_1565914 : Nat := 4983230072969 + 3 ^ 40 * 1565914 * 2
def baseEnd_1565914 : Nat := 536044363736461058648999

theorem tailTrace_1565914 : CollatzResearch.WordTrace tailWord_1565914 prefixEnd_1565914 536044363736461058648999 := by
  unfold tailWord_1565914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278393912242122416144199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38075717099312326443051197 14278393912242122416144199)
  ·
    refine ⟨21417590868363183624216299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14278393912242122416144199 21417590868363183624216299)
    ·
      refine ⟨32126386302544775436324449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21417590868363183624216299 32126386302544775436324449)
      ·
        refine ⟨24094789726908581577243337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32126386302544775436324449 24094789726908581577243337)
        ·
          refine ⟨18071092295181436182932503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24094789726908581577243337 18071092295181436182932503)
          ·
            refine ⟨27106638442772154274398755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18071092295181436182932503 27106638442772154274398755)
            ·
              refine ⟨40659957664158231411598133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27106638442772154274398755 40659957664158231411598133)
              ·
                refine ⟨3811871031014834194837325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40659957664158231411598133 3811871031014834194837325)
                ·
                  refine ⟨1429451636630562823063997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3811871031014834194837325 1429451636630562823063997)
                  ·
                    refine ⟨536044363736461058648999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429451636630562823063997 536044363736461058648999)
                    ·
                      rfl

theorem cell22_1565914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_1565914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565914 prefixEnd_1565914 := by exact prefixLift 1565914
  have htrace : WordTrace (prefixWord ++ tailWord_1565914) baseStart_1565914 baseEnd_1565914 := by
    simpa [prefixWord, tailWord_1565914, baseEnd_1565914] using wordTrace_append hprefix tailTrace_1565914
  have hstable : (prefixWord ++ tailWord_1565914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565914).length < 2 ^ (prefixWord ++ tailWord_1565914).sum := by decide
  have hdescent : baseEnd_1565914 < baseStart_1565914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565989 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 6]
def baseStart_1565989 : Nat := 118140960795 + 1565989 * 2 ^ 59
def prefixEnd_1565989 : Nat := 4983230072969 + 3 ^ 40 * 1565989 * 2
def baseEnd_1565989 : Nat := 178690012589728621007923

theorem tailTrace_1565989 : CollatzResearch.WordTrace tailWord_1565989 prefixEnd_1565989 178690012589728621007923 := by
  unfold tailWord_1565989
  simp only [CollatzResearch.WordTrace]
  refine ⟨57116311123696777473557021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38077540749131184982371347 57116311123696777473557021)
  ·
    refine ⟨21418616671386291552583883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57116311123696777473557021 21418616671386291552583883)
    ·
      refine ⟨32127925007079437328875825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21418616671386291552583883 32127925007079437328875825)
      ·
        refine ⟨24095943755309577996656869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32127925007079437328875825 24095943755309577996656869)
        ·
          refine ⟨4517989454120545874373163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24095943755309577996656869 4517989454120545874373163)
          ·
            refine ⟨6776984181180818811559745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517989454120545874373163 6776984181180818811559745)
            ·
              refine ⟨5082738135885614108669809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6776984181180818811559745 5082738135885614108669809)
              ·
                refine ⟨3812053601914210581502357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5082738135885614108669809 3812053601914210581502357)
                ·
                  refine ⟨178690012589728621007923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3812053601914210581502357 178690012589728621007923)
                  ·
                    rfl

theorem cell22_1565989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_1565989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1565989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1565989 prefixEnd_1565989 := by exact prefixLift 1565989
  have htrace : WordTrace (prefixWord ++ tailWord_1565989) baseStart_1565989 baseEnd_1565989 := by
    simpa [prefixWord, tailWord_1565989, baseEnd_1565989] using wordTrace_append hprefix tailTrace_1565989
  have hstable : (prefixWord ++ tailWord_1565989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565989).length < 2 ^ (prefixWord ++ tailWord_1565989).sum := by decide
  have hdescent : baseEnd_1565989 < baseStart_1565989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566023 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 4]
def baseStart_1566023 : Nat := 118140960795 + 1566023 * 2 ^ 59
def prefixEnd_1566023 : Nat := 4983230072969 + 3 ^ 40 * 1566023 * 2
def baseEnd_1566023 : Nat := 178693892221340369224555

theorem tailTrace_1566023 : CollatzResearch.WordTrace tailWord_1566023 prefixEnd_1566023 178693892221340369224555 := by
  unfold tailWord_1566023
  simp only [CollatzResearch.WordTrace]
  refine ⟨57117551205573601280294723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38078367470382400853529815 57117551205573601280294723)
  ·
    refine ⟨85676326808360401920442085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57117551205573601280294723 85676326808360401920442085)
    ·
      refine ⟨16064311276567575360082891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85676326808360401920442085 16064311276567575360082891)
      ·
        refine ⟨24096466914851363040124337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16064311276567575360082891 24096466914851363040124337)
        ·
          refine ⟨18072350186138522280093253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24096466914851363040124337 18072350186138522280093253)
          ·
            refine ⟨3388565659900972927517485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18072350186138522280093253 3388565659900972927517485)
            ·
              refine ⟨1270712122462864847819057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3388565659900972927517485 1270712122462864847819057)
              ·
                refine ⟨953034091847148635864293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270712122462864847819057 953034091847148635864293)
                ·
                  refine ⟨178693892221340369224555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953034091847148635864293 178693892221340369224555)
                  ·
                    rfl

theorem cell22_1566023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 4].length) (baseStart_1566023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566023 prefixEnd_1566023 := by exact prefixLift 1566023
  have htrace : WordTrace (prefixWord ++ tailWord_1566023) baseStart_1566023 baseEnd_1566023 := by
    simpa [prefixWord, tailWord_1566023, baseEnd_1566023] using wordTrace_append hprefix tailTrace_1566023
  have hstable : (prefixWord ++ tailWord_1566023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566023).length < 2 ^ (prefixWord ++ tailWord_1566023).sum := by decide
  have hdescent : baseEnd_1566023 < baseStart_1566023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566141 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 6]
def baseStart_1566141 : Nat := 118140960795 + 1566141 * 2 ^ 59
def prefixEnd_1566141 : Nat := 4983230072969 + 3 ^ 40 * 1566141 * 2
def baseEnd_1566141 : Nat := 178707356825169377741101

theorem tailTrace_1566141 : CollatzResearch.WordTrace tailWord_1566141 prefixEnd_1566141 178707356825169377741101 := by
  unfold tailWord_1566141
  simp only [CollatzResearch.WordTrace]
  refine ⟨57121855019146107433090277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38081236679430738288726851 57121855019146107433090277)
  ·
    refine ⟨10710347816089895143704427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57121855019146107433090277 10710347816089895143704427)
    ·
      refine ⟨16065521724134842715556641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10710347816089895143704427 16065521724134842715556641)
      ·
        refine ⟨12049141293101132036667481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16065521724134842715556641 12049141293101132036667481)
        ·
          refine ⟨9036855969825849027500611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12049141293101132036667481 9036855969825849027500611)
          ·
            refine ⟨13555283954738773541250917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9036855969825849027500611 13555283954738773541250917)
            ·
              refine ⟨2541615741513520038984547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13555283954738773541250917 2541615741513520038984547)
              ·
                refine ⟨3812423612270280058476821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541615741513520038984547 3812423612270280058476821)
                ·
                  refine ⟨178707356825169377741101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3812423612270280058476821 178707356825169377741101)
                  ·
                    rfl

theorem cell22_1566141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_1566141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566141 prefixEnd_1566141 := by exact prefixLift 1566141
  have htrace : WordTrace (prefixWord ++ tailWord_1566141) baseStart_1566141 baseEnd_1566141 := by
    simpa [prefixWord, tailWord_1566141, baseEnd_1566141] using wordTrace_append hprefix tailTrace_1566141
  have hstable : (prefixWord ++ tailWord_1566141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566141).length < 2 ^ (prefixWord ++ tailWord_1566141).sum := by decide
  have hdescent : baseEnd_1566141 < baseStart_1566141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566173 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1566173 : Nat := 118140960795 + 1566173 * 2 ^ 59
def prefixEnd_1566173 : Nat := 4983230072969 + 3 ^ 40 * 1566173 * 2
def baseEnd_1566173 : Nat := 536133024729470716423205

theorem tailTrace_1566173 : CollatzResearch.WordTrace tailWord_1566173 prefixEnd_1566173 536133024729470716423205 := by
  unfold tailWord_1566173
  simp only [CollatzResearch.WordTrace]
  refine ⟨57123022155030176898255173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38082014770020117932170115 57123022155030176898255173)
  ·
    refine ⟨10710566654068158168422845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57123022155030176898255173 10710566654068158168422845)
    ·
      refine ⟨4016462495275559313158567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10710566654068158168422845 4016462495275559313158567)
      ·
        refine ⟨6024693742913338969737851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016462495275559313158567 6024693742913338969737851)
        ·
          refine ⟨9037040614370008454606777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6024693742913338969737851 9037040614370008454606777)
          ·
            refine ⟨6777780460777506340955083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9037040614370008454606777 6777780460777506340955083)
            ·
              refine ⟨10166670691166259511432625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777780460777506340955083 10166670691166259511432625)
              ·
                refine ⟨7625003018374694633574469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10166670691166259511432625 7625003018374694633574469)
                ·
                  refine ⟨1429688065945255243795213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7625003018374694633574469 1429688065945255243795213)
                  ·
                    refine ⟨536133024729470716423205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429688065945255243795213 536133024729470716423205)
                    ·
                      rfl

theorem cell22_1566173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1566173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566173 prefixEnd_1566173 := by exact prefixLift 1566173
  have htrace : WordTrace (prefixWord ++ tailWord_1566173) baseStart_1566173 baseEnd_1566173 := by
    simpa [prefixWord, tailWord_1566173, baseEnd_1566173] using wordTrace_append hprefix tailTrace_1566173
  have hstable : (prefixWord ++ tailWord_1566173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566173).length < 2 ^ (prefixWord ++ tailWord_1566173).sum := by decide
  have hdescent : baseEnd_1566173 < baseStart_1566173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566295 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 1, 4]
def baseStart_1566295 : Nat := 118140960795 + 1566295 * 2 ^ 59
def prefixEnd_1566295 : Nat := 4983230072969 + 3 ^ 40 * 1566295 * 2
def baseEnd_1566295 : Nat := 536174787822703064872831

theorem tailTrace_1566295 : CollatzResearch.WordTrace tailWord_1566295 prefixEnd_1566295 536174787822703064872831 := by
  unfold tailWord_1566295
  simp only [CollatzResearch.WordTrace]
  refine ⟨57127471860588191734196339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38084981240392127822797559 57127471860588191734196339)
  ·
    refine ⟨85691207790882287601294509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57127471860588191734196339 85691207790882287601294509)
    ·
      refine ⟨32134202921580857850485441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85691207790882287601294509 32134202921580857850485441)
      ·
        refine ⟨24100652191185643387864081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32134202921580857850485441 24100652191185643387864081)
        ·
          refine ⟨18075489143389232540898061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24100652191185643387864081 18075489143389232540898061)
          ·
            refine ⟨6778308428770962202836773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18075489143389232540898061 6778308428770962202836773)
            ·
              refine ⟨1270932830394555413031895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6778308428770962202836773 1270932830394555413031895)
              ·
                refine ⟨1906399245591833119547843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270932830394555413031895 1906399245591833119547843)
                ·
                  refine ⟨2859598868387749679321765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906399245591833119547843 2859598868387749679321765)
                  ·
                    refine ⟨536174787822703064872831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2859598868387749679321765 536174787822703064872831)
                    ·
                      rfl

theorem cell22_1566295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_1566295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566295 prefixEnd_1566295 := by exact prefixLift 1566295
  have htrace : WordTrace (prefixWord ++ tailWord_1566295) baseStart_1566295 baseEnd_1566295 := by
    simpa [prefixWord, tailWord_1566295, baseEnd_1566295] using wordTrace_append hprefix tailTrace_1566295
  have hstable : (prefixWord ++ tailWord_1566295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566295).length < 2 ^ (prefixWord ++ tailWord_1566295).sum := by decide
  have hdescent : baseEnd_1566295 < baseStart_1566295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566325 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1566325 : Nat := 118140960795 + 1566325 * 2 ^ 59
def prefixEnd_1566325 : Nat := 4983230072969 + 3 ^ 40 * 1566325 * 2
def baseEnd_1566325 : Nat := 536185057435792986622739

theorem tailTrace_1566325 : CollatzResearch.WordTrace tailWord_1566325 prefixEnd_1566325 536185057435792986622739 := by
  unfold tailWord_1566325
  simp only [CollatzResearch.WordTrace]
  refine ⟨57128566050479506857788429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38085710700319671238525619 57128566050479506857788429)
  ·
    refine ⟨21423212268929815071670661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57128566050479506857788429 21423212268929815071670661)
    ·
      refine ⟨4016852300424340325938249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21423212268929815071670661 4016852300424340325938249)
      ·
        refine ⟨3012639225318255244453687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4016852300424340325938249 3012639225318255244453687)
        ·
          refine ⟨4518958837977382866680531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012639225318255244453687 4518958837977382866680531)
          ·
            refine ⟨6778438256966074300020797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518958837977382866680531 6778438256966074300020797)
            ·
              refine ⟨2541914346362277862507799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6778438256966074300020797 2541914346362277862507799)
              ·
                refine ⟨3812871519543416793761699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541914346362277862507799 3812871519543416793761699)
                ·
                  refine ⟨5719307279315125190642549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812871519543416793761699 5719307279315125190642549)
                  ·
                    refine ⟨536185057435792986622739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5719307279315125190642549 536185057435792986622739)
                    ·
                      rfl

theorem cell22_1566325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1566325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566325 prefixEnd_1566325 := by exact prefixLift 1566325
  have htrace : WordTrace (prefixWord ++ tailWord_1566325) baseStart_1566325 baseEnd_1566325 := by
    simpa [prefixWord, tailWord_1566325, baseEnd_1566325] using wordTrace_append hprefix tailTrace_1566325
  have hstable : (prefixWord ++ tailWord_1566325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566325).length < 2 ^ (prefixWord ++ tailWord_1566325).sum := by decide
  have hdescent : baseEnd_1566325 < baseStart_1566325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566336 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_1566336 : Nat := 118140960795 + 1566336 * 2 ^ 59
def prefixEnd_1566336 : Nat := 4983230072969 + 3 ^ 40 * 1566336 * 2
def baseEnd_1566336 : Nat := 536188822960592624597705

theorem tailTrace_1566336 : CollatzResearch.WordTrace tailWord_1566336 prefixEnd_1566336 536188822960592624597705 := by
  unfold tailWord_1566336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564483626719827868219431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38085978168959770490959241 28564483626719827868219431)
  ·
    refine ⟨42846725440079741802329147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28564483626719827868219431 42846725440079741802329147)
    ·
      refine ⟨64270088160119612703493721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42846725440079741802329147 64270088160119612703493721)
      ·
        refine ⟨48202566120089709527620291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64270088160119612703493721 48202566120089709527620291)
        ·
          refine ⟨72303849180134564291430437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48202566120089709527620291 72303849180134564291430437)
          ·
            refine ⟨13556971721275230804643207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72303849180134564291430437 13556971721275230804643207)
            ·
              refine ⟨20335457581912846206964811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556971721275230804643207 20335457581912846206964811)
              ·
                refine ⟨30503186372869269310447217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20335457581912846206964811 30503186372869269310447217)
                ·
                  refine ⟨22877389779651951982835413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30503186372869269310447217 22877389779651951982835413)
                  ·
                    refine ⟨536188822960592624597705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22877389779651951982835413 536188822960592624597705)
                    ·
                      rfl

theorem cell22_1566336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_1566336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566336 prefixEnd_1566336 := by exact prefixLift 1566336
  have htrace : WordTrace (prefixWord ++ tailWord_1566336) baseStart_1566336 baseEnd_1566336 := by
    simpa [prefixWord, tailWord_1566336, baseEnd_1566336] using wordTrace_append hprefix tailTrace_1566336
  have hstable : (prefixWord ++ tailWord_1566336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566336).length < 2 ^ (prefixWord ++ tailWord_1566336).sum := by decide
  have hdescent : baseEnd_1566336 < baseStart_1566336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566344 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 4]
def baseStart_1566344 : Nat := 118140960795 + 1566344 * 2 ^ 59
def prefixEnd_1566344 : Nat := 4983230072969 + 3 ^ 40 * 1566344 * 2
def baseEnd_1566344 : Nat := 178730520508027756799227

theorem tailTrace_1566344 : CollatzResearch.WordTrace tailWord_1566344 prefixEnd_1566344 178730520508027756799227 := by
  unfold tailWord_1566344
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564629518705336551365043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38086172691607115401820057 28564629518705336551365043)
  ·
    refine ⟨42846944278058004827047565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28564629518705336551365043 42846944278058004827047565)
    ·
      refine ⟨16067604104271751810142837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42846944278058004827047565 16067604104271751810142837)
      ·
        refine ⟨1506337884775476732200891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16067604104271751810142837 1506337884775476732200891)
        ·
          refine ⟨2259506827163215098301337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506337884775476732200891 2259506827163215098301337)
          ·
            refine ⟨1694630120372411323726003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259506827163215098301337 1694630120372411323726003)
            ·
              refine ⟨2541945180558616985589005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694630120372411323726003 2541945180558616985589005)
              ·
                refine ⟨953229442709481369595877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2541945180558616985589005 953229442709481369595877)
                ·
                  refine ⟨178730520508027756799227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953229442709481369595877 178730520508027756799227)
                  ·
                    rfl

theorem cell22_1566344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_1566344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566344 prefixEnd_1566344 := by exact prefixLift 1566344
  have htrace : WordTrace (prefixWord ++ tailWord_1566344) baseStart_1566344 baseEnd_1566344 := by
    simpa [prefixWord, tailWord_1566344, baseEnd_1566344] using wordTrace_append hprefix tailTrace_1566344
  have hstable : (prefixWord ++ tailWord_1566344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566344).length < 2 ^ (prefixWord ++ tailWord_1566344).sum := by decide
  have hdescent : baseEnd_1566344 < baseStart_1566344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566376 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1566376 : Nat := 118140960795 + 1566376 * 2 ^ 59
def prefixEnd_1566376 : Nat := 4983230072969 + 3 ^ 40 * 1566376 * 2
def baseEnd_1566376 : Nat := 536202515778045853597583

theorem tailTrace_1566376 : CollatzResearch.WordTrace tailWord_1566376 prefixEnd_1566376 536202515778045853597583 := by
  unfold tailWord_1566376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565213086647371283947491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38086950782196495045263321 28565213086647371283947491)
  ·
    refine ⟨42847819629971056925921237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28565213086647371283947491 42847819629971056925921237)
    ·
      refine ⟨1004245772577446646701279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42847819629971056925921237 1004245772577446646701279)
      ·
        refine ⟨1506368658866169970051919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004245772577446646701279 1506368658866169970051919)
        ·
          refine ⟨2259552988299254955077879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506368658866169970051919 2259552988299254955077879)
          ·
            refine ⟨3389329482448882432616819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259552988299254955077879 3389329482448882432616819)
            ·
              refine ⟨5083994223673323648925229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389329482448882432616819 5083994223673323648925229)
              ·
                refine ⟨1906497833877496368346961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5083994223673323648925229 1906497833877496368346961)
                ·
                  refine ⟨1429873375408122276260221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1906497833877496368346961 1429873375408122276260221)
                  ·
                    refine ⟨536202515778045853597583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429873375408122276260221 536202515778045853597583)
                    ·
                      rfl

theorem cell22_1566376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1566376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566376 prefixEnd_1566376 := by exact prefixLift 1566376
  have htrace : WordTrace (prefixWord ++ tailWord_1566376) baseStart_1566376 baseEnd_1566376 := by
    simpa [prefixWord, tailWord_1566376, baseEnd_1566376] using wordTrace_append hprefix tailTrace_1566376
  have hstable : (prefixWord ++ tailWord_1566376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566376).length < 2 ^ (prefixWord ++ tailWord_1566376).sum := by decide
  have hdescent : baseEnd_1566376 < baseStart_1566376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566383 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 5]
def baseStart_1566383 : Nat := 118140960795 + 1566383 * 2 ^ 59
def prefixEnd_1566383 : Nat := 4983230072969 + 3 ^ 40 * 1566383 * 2
def baseEnd_1566383 : Nat := 178734970673700056224187

theorem tailTrace_1566383 : CollatzResearch.WordTrace tailWord_1566383 prefixEnd_1566383 178734970673700056224187 := by
  unfold tailWord_1566383
  simp only [CollatzResearch.WordTrace]
  refine ⟨57130681484269382763399803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38087120989512921842266535 57130681484269382763399803)
  ·
    refine ⟨85696022226404074145099705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57130681484269382763399803 85696022226404074145099705)
    ·
      refine ⟨64272016669803055608824779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85696022226404074145099705 64272016669803055608824779)
      ·
        refine ⟨96408025004704583413237169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64272016669803055608824779 96408025004704583413237169)
        ·
          refine ⟨72306018753528437559927877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96408025004704583413237169 72306018753528437559927877)
          ·
            refine ⟨13557378516286582042486477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72306018753528437559927877 13557378516286582042486477)
            ·
              refine ⟨5084016943607468265932429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13557378516286582042486477 5084016943607468265932429)
              ·
                refine ⟨1906506353852800599724661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5084016943607468265932429 1906506353852800599724661)
                ·
                  refine ⟨178734970673700056224187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1906506353852800599724661 178734970673700056224187)
                  ·
                    rfl

theorem cell22_1566383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 5].length) (baseStart_1566383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566383 prefixEnd_1566383 := by exact prefixLift 1566383
  have htrace : WordTrace (prefixWord ++ tailWord_1566383) baseStart_1566383 baseEnd_1566383 := by
    simpa [prefixWord, tailWord_1566383, baseEnd_1566383] using wordTrace_append hprefix tailTrace_1566383
  have hstable : (prefixWord ++ tailWord_1566383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566383).length < 2 ^ (prefixWord ++ tailWord_1566383).sum := by decide
  have hdescent : baseEnd_1566383 < baseStart_1566383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566443 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 1, 5]
def baseStart_1566443 : Nat := 118140960795 + 1566443 * 2 ^ 59
def prefixEnd_1566443 : Nat := 4983230072969 + 3 ^ 40 * 1566443 * 2
def baseEnd_1566443 : Nat := 536225451247280012172377

theorem tailTrace_1566443 : CollatzResearch.WordTrace tailWord_1566443 prefixEnd_1566443 536225451247280012172377 := by
  unfold tailWord_1566443
  simp only [CollatzResearch.WordTrace]
  refine ⟨57132869864052013010583983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38088579909368008673722655 57132869864052013010583983)
  ·
    refine ⟨85699304796078019515875975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57132869864052013010583983 85699304796078019515875975)
    ·
      refine ⟨128548957194117029273813963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85699304796078019515875975 128548957194117029273813963)
      ·
        refine ⟨192823435791175543910720945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128548957194117029273813963 192823435791175543910720945)
        ·
          refine ⟨144617576843381657933040709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192823435791175543910720945 144617576843381657933040709)
          ·
            refine ⟨27115795658134060862445133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144617576843381657933040709 27115795658134060862445133)
            ·
              refine ⟨10168423371800272823416925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27115795658134060862445133 10168423371800272823416925)
              ·
                refine ⟨3813158764425102308781347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10168423371800272823416925 3813158764425102308781347)
                ·
                  refine ⟨5719738146637653463172021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813158764425102308781347 5719738146637653463172021)
                  ·
                    refine ⟨536225451247280012172377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5719738146637653463172021 536225451247280012172377)
                    ·
                      rfl

theorem cell22_1566443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_1566443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566443 prefixEnd_1566443 := by exact prefixLift 1566443
  have htrace : WordTrace (prefixWord ++ tailWord_1566443) baseStart_1566443 baseEnd_1566443 := by
    simpa [prefixWord, tailWord_1566443, baseEnd_1566443] using wordTrace_append hprefix tailTrace_1566443
  have hstable : (prefixWord ++ tailWord_1566443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566443).length < 2 ^ (prefixWord ++ tailWord_1566443).sum := by decide
  have hdescent : baseEnd_1566443 < baseStart_1566443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566445 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1566445 : Nat := 118140960795 + 1566445 * 2 ^ 59
def prefixEnd_1566445 : Nat := 4983230072969 + 3 ^ 40 * 1566445 * 2
def baseEnd_1566445 : Nat := 178742045296050891207457

theorem tailTrace_1566445 : CollatzResearch.WordTrace tailWord_1566445 prefixEnd_1566445 178742045296050891207457 := by
  unfold tailWord_1566445
  simp only [CollatzResearch.WordTrace]
  refine ⟨57132942810044767352156789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38088628540029844901437859 57132942810044767352156789)
  ·
    refine ⟨5356213388441696939264699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57132942810044767352156789 5356213388441696939264699)
    ·
      refine ⟨8034320082662545408897049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5356213388441696939264699 8034320082662545408897049)
      ·
        refine ⟨6025740061996909056672787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8034320082662545408897049 6025740061996909056672787)
        ·
          refine ⟨9038610092995363585009181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025740061996909056672787 9038610092995363585009181)
          ·
            refine ⟨3389478784873261344378443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9038610092995363585009181 3389478784873261344378443)
            ·
              refine ⟨5084218177309892016567665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389478784873261344378443 5084218177309892016567665)
              ·
                refine ⟨3813163632982419012425749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5084218177309892016567665 3813163632982419012425749)
                ·
                  refine ⟨178742045296050891207457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3813163632982419012425749 178742045296050891207457)
                  ·
                    rfl

theorem cell22_1566445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1566445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566445 prefixEnd_1566445 := by exact prefixLift 1566445
  have htrace : WordTrace (prefixWord ++ tailWord_1566445) baseStart_1566445 baseEnd_1566445 := by
    simpa [prefixWord, tailWord_1566445, baseEnd_1566445] using wordTrace_append hprefix tailTrace_1566445
  have hstable : (prefixWord ++ tailWord_1566445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566445).length < 2 ^ (prefixWord ++ tailWord_1566445).sum := by decide
  have hdescent : baseEnd_1566445 < baseStart_1566445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566460 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1566460 : Nat := 118140960795 + 1566460 * 2 ^ 59
def prefixEnd_1566460 : Nat := 4983230072969 + 3 ^ 40 * 1566460 * 2
def baseEnd_1566460 : Nat := 536231270694697634497325

theorem tailTrace_1566460 : CollatzResearch.WordTrace tailWord_1566460 prefixEnd_1566460 536231270694697634497325 := by
  unfold tailWord_1566460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28566744952495212456976417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38088993269993616609301889 28566744952495212456976417)
  ·
    refine ⟨21425058714371409342732313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28566744952495212456976417 21425058714371409342732313)
    ·
      refine ⟨16068794035778557007049235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21425058714371409342732313 16068794035778557007049235)
      ·
        refine ⟨24103191053667835510573853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16068794035778557007049235 24103191053667835510573853)
        ·
          refine ⟨9038696645125438316465195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24103191053667835510573853 9038696645125438316465195)
          ·
            refine ⟨13558044967688157474697793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038696645125438316465195 13558044967688157474697793)
            ·
              refine ⟨10168533725766118106023345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13558044967688157474697793 10168533725766118106023345)
              ·
                refine ⟨7626400294324588579517509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10168533725766118106023345 7626400294324588579517509)
                ·
                  refine ⟨1429950055185860358659533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7626400294324588579517509 1429950055185860358659533)
                  ·
                    refine ⟨536231270694697634497325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429950055185860358659533 536231270694697634497325)
                    ·
                      rfl

theorem cell22_1566460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1566460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566460 prefixEnd_1566460 := by exact prefixLift 1566460
  have htrace : WordTrace (prefixWord ++ tailWord_1566460) baseStart_1566460 baseEnd_1566460 := by
    simpa [prefixWord, tailWord_1566460, baseEnd_1566460] using wordTrace_append hprefix tailTrace_1566460
  have hstable : (prefixWord ++ tailWord_1566460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566460).length < 2 ^ (prefixWord ++ tailWord_1566460).sum := by decide
  have hdescent : baseEnd_1566460 < baseStart_1566460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566590 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1566590 : Nat := 118140960795 + 1566590 * 2 ^ 59
def prefixEnd_1566590 : Nat := 4983230072969 + 3 ^ 40 * 1566590 * 2
def baseEnd_1566590 : Nat := 536275772351420628746927

theorem tailTrace_1566590 : CollatzResearch.WordTrace tailWord_1566590 prefixEnd_1566590 536275772351420628746927 := by
  unfold tailWord_1566590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142278924314932139523153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38092154263012971410790149 7142278924314932139523153)
  ·
    refine ⟨5356709193236199104642365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7142278924314932139523153 5356709193236199104642365)
    ·
      refine ⟨2008765947463574664240887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5356709193236199104642365 2008765947463574664240887)
      ·
        refine ⟨3013148921195361996361331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008765947463574664240887 3013148921195361996361331)
        ·
          refine ⟨4519723381793042994541997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013148921195361996361331 4519723381793042994541997)
          ·
            refine ⟨1694896268172391122953249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4519723381793042994541997 1694896268172391122953249)
            ·
              refine ⟨1271172201129293342214937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694896268172391122953249 1271172201129293342214937)
              ·
                refine ⟨953379150846970006661203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271172201129293342214937 953379150846970006661203)
                ·
                  refine ⟨1430068726270455009991805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953379150846970006661203 1430068726270455009991805)
                  ·
                    refine ⟨536275772351420628746927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1430068726270455009991805 536275772351420628746927)
                    ·
                      rfl

theorem cell22_1566590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1566590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566590 prefixEnd_1566590 := by exact prefixLift 1566590
  have htrace : WordTrace (prefixWord ++ tailWord_1566590) baseStart_1566590 baseEnd_1566590 := by
    simpa [prefixWord, tailWord_1566590, baseEnd_1566590] using wordTrace_append hprefix tailTrace_1566590
  have hstable : (prefixWord ++ tailWord_1566590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566590).length < 2 ^ (prefixWord ++ tailWord_1566590).sum := by decide
  have hdescent : baseEnd_1566590 < baseStart_1566590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566597 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 4]
def baseStart_1566597 : Nat := 118140960795 + 1566597 * 2 ^ 59
def prefixEnd_1566597 : Nat := 4983230072969 + 3 ^ 40 * 1566597 * 2
def baseEnd_1566597 : Nat := 178759389531491647940635

theorem tailTrace_1566597 : CollatzResearch.WordTrace tailWord_1566597 prefixEnd_1566597 178759389531491647940635 := by
  unfold tailWord_1566597
  simp only [CollatzResearch.WordTrace]
  refine ⟨57138486705494097311690045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38092324470329398207793363 57138486705494097311690045)
  ·
    refine ⟨21426932514560286491883767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57138486705494097311690045 21426932514560286491883767)
    ·
      refine ⟨32140398771840429737825651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21426932514560286491883767 32140398771840429737825651)
      ·
        refine ⟨48210598157760644606738477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32140398771840429737825651 48210598157760644606738477)
        ·
          refine ⟨18078974309160241727526929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48210598157760644606738477 18078974309160241727526929)
          ·
            refine ⟨13559230731870181295645197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18078974309160241727526929 13559230731870181295645197)
            ·
              refine ⟨5084711524451317985866949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13559230731870181295645197 5084711524451317985866949)
              ·
                refine ⟨953383410834622122350053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5084711524451317985866949 953383410834622122350053)
                ·
                  refine ⟨178759389531491647940635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953383410834622122350053 178759389531491647940635)
                  ·
                    rfl

theorem cell22_1566597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_1566597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566597 prefixEnd_1566597 := by exact prefixLift 1566597
  have htrace : WordTrace (prefixWord ++ tailWord_1566597) baseStart_1566597 baseEnd_1566597 := by
    simpa [prefixWord, tailWord_1566597, baseEnd_1566597] using wordTrace_append hprefix tailTrace_1566597
  have hstable : (prefixWord ++ tailWord_1566597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566597).length < 2 ^ (prefixWord ++ tailWord_1566597).sum := by decide
  have hdescent : baseEnd_1566597 < baseStart_1566597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566612 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1566612 : Nat := 118140960795 + 1566612 * 2 ^ 59
def prefixEnd_1566612 : Nat := 4983230072969 + 3 ^ 40 * 1566612 * 2
def baseEnd_1566612 : Nat := 536283303401019904696859

theorem tailTrace_1566612 : CollatzResearch.WordTrace tailWord_1566612 prefixEnd_1566612 536283303401019904696859 := by
  unfold tailWord_1566612
  simp only [CollatzResearch.WordTrace]
  refine ⟨28569516900219877436743045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38092689200293169915657393 28569516900219877436743045)
  ·
    refine ⟨5356784418791227019389321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28569516900219877436743045 5356784418791227019389321)
    ·
      refine ⟨4017588314093420264541991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5356784418791227019389321 4017588314093420264541991)
      ·
        refine ⟨6026382471140130396812987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017588314093420264541991 6026382471140130396812987)
        ·
          refine ⟨9039573706710195595219481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6026382471140130396812987 9039573706710195595219481)
          ·
            refine ⟨6779680280032646696414611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9039573706710195595219481 6779680280032646696414611)
            ·
              refine ⟨10169520420048970044621917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779680280032646696414611 10169520420048970044621917)
              ·
                refine ⟨3813570157518363766733219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10169520420048970044621917 3813570157518363766733219)
                ·
                  refine ⟨5720355236277545650099829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813570157518363766733219 5720355236277545650099829)
                  ·
                    refine ⟨536283303401019904696859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5720355236277545650099829 536283303401019904696859)
                    ·
                      rfl

theorem cell22_1566612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1566612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566612 prefixEnd_1566612 := by exact prefixLift 1566612
  have htrace : WordTrace (prefixWord ++ tailWord_1566612) baseStart_1566612 baseEnd_1566612 := by
    simpa [prefixWord, tailWord_1566612, baseEnd_1566612] using wordTrace_append hprefix tailTrace_1566612
  have hstable : (prefixWord ++ tailWord_1566612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566612).length < 2 ^ (prefixWord ++ tailWord_1566612).sum := by decide
  have hdescent : baseEnd_1566612 < baseStart_1566612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566691 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 1, 3]
def baseStart_1566691 : Nat := 118140960795 + 1566691 * 2 ^ 59
def prefixEnd_1566691 : Nat := 4983230072969 + 3 ^ 40 * 1566691 * 2
def baseEnd_1566691 : Nat := 536310346715490031971617

theorem tailTrace_1566691 : CollatzResearch.WordTrace tailWord_1566691 prefixEnd_1566691 536310346715490031971617 := by
  unfold tailWord_1566691
  simp only [CollatzResearch.WordTrace]
  refine ⟨57141915167153551365611927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38094610111435700910407951 57141915167153551365611927)
  ·
    refine ⟨85712872750730327048417891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57141915167153551365611927 85712872750730327048417891)
    ·
      refine ⟨128569309126095490572626837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85712872750730327048417891 128569309126095490572626837)
      ·
        refine ⟨6026686365285726120591883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128569309126095490572626837 6026686365285726120591883)
        ·
          refine ⟨9040029547928589180887825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6026686365285726120591883 9040029547928589180887825)
          ·
            refine ⟨6780022160946441885665869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9040029547928589180887825 6780022160946441885665869)
            ·
              refine ⟨2542508310354915707124701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6780022160946441885665869 2542508310354915707124701)
              ·
                refine ⟨953440616383093390171763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2542508310354915707124701 953440616383093390171763)
                ·
                  refine ⟨1430160924574640085257645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953440616383093390171763 1430160924574640085257645)
                  ·
                    refine ⟨536310346715490031971617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1430160924574640085257645 536310346715490031971617)
                    ·
                      rfl

theorem cell22_1566691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 3].length) (baseStart_1566691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566691 prefixEnd_1566691 := by exact prefixLift 1566691
  have htrace : WordTrace (prefixWord ++ tailWord_1566691) baseStart_1566691 baseEnd_1566691 := by
    simpa [prefixWord, tailWord_1566691, baseEnd_1566691] using wordTrace_append hprefix tailTrace_1566691
  have hstable : (prefixWord ++ tailWord_1566691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566691).length < 2 ^ (prefixWord ++ tailWord_1566691).sum := by decide
  have hdescent : baseEnd_1566691 < baseStart_1566691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566747 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 4, 3]
def baseStart_1566747 : Nat := 118140960795 + 1566747 * 2 ^ 59
def prefixEnd_1566747 : Nat := 4983230072969 + 3 ^ 40 * 1566747 * 2
def baseEnd_1566747 : Nat := 536329516659924552571445

theorem tailTrace_1566747 : CollatzResearch.WordTrace tailWord_1566747 prefixEnd_1566747 536329516659924552571445 := by
  unfold tailWord_1566747
  simp only [CollatzResearch.WordTrace]
  refine ⟨57143957654950672929650495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38095971769967115286433663 57143957654950672929650495)
  ·
    refine ⟨85715936482426009394475743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57143957654950672929650495 85715936482426009394475743)
    ·
      refine ⟨128573904723639014091713615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85715936482426009394475743 128573904723639014091713615)
      ·
        refine ⟨192860857085458521137570423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128573904723639014091713615 192860857085458521137570423)
        ·
          refine ⟨289291285628187781706355635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192860857085458521137570423 289291285628187781706355635)
          ·
            refine ⟨433936928442281672559533453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289291285628187781706355635 433936928442281672559533453)
            ·
              refine ⟨162726348165855627209825045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433936928442281672559533453 162726348165855627209825045)
              ·
                refine ⟨7627797570274482525460549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162726348165855627209825045 7627797570274482525460549)
                ·
                  refine ⟨1430212044426465473523853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7627797570274482525460549 1430212044426465473523853)
                  ·
                    refine ⟨536329516659924552571445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1430212044426465473523853 536329516659924552571445)
                    ·
                      rfl

theorem cell22_1566747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 3].length) (baseStart_1566747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566747 prefixEnd_1566747 := by exact prefixLift 1566747
  have htrace : WordTrace (prefixWord ++ tailWord_1566747) baseStart_1566747 baseEnd_1566747 := by
    simpa [prefixWord, tailWord_1566747, baseEnd_1566747] using wordTrace_append hprefix tailTrace_1566747
  have hstable : (prefixWord ++ tailWord_1566747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566747).length < 2 ^ (prefixWord ++ tailWord_1566747).sum := by decide
  have hdescent : baseEnd_1566747 < baseStart_1566747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566766 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_1566766 : Nat := 118140960795 + 1566766 * 2 ^ 59
def prefixEnd_1566766 : Nat := 4983230072969 + 3 ^ 40 * 1566766 * 2
def baseEnd_1566766 : Nat := 178778673582738278782129

theorem tailTrace_1566766 : CollatzResearch.WordTrace tailWord_1566766 prefixEnd_1566766 178778673582738278782129 := by
  unfold tailWord_1566766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7143081330235229896824019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38096433761254559449728101 7143081330235229896824019)
  ·
    refine ⟨10714621995352844845236029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7143081330235229896824019 10714621995352844845236029)
    ·
      refine ⟨4017983248257316816963511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10714621995352844845236029 4017983248257316816963511)
      ·
        refine ⟨6026974872385975225445267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017983248257316816963511 6026974872385975225445267)
        ·
          refine ⟨9040462308578962838167901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6026974872385975225445267 9040462308578962838167901)
          ·
            refine ⟨3390173365717111064312963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9040462308578962838167901 3390173365717111064312963)
            ·
              refine ⟨5085260048575666596469445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390173365717111064312963 5085260048575666596469445)
              ·
                refine ⟨953486259107937486838021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5085260048575666596469445 953486259107937486838021)
                ·
                  refine ⟨178778673582738278782129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953486259107937486838021 178778673582738278782129)
                  ·
                    rfl

theorem cell22_1566766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_1566766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566766 prefixEnd_1566766 := by exact prefixLift 1566766
  have htrace : WordTrace (prefixWord ++ tailWord_1566766) baseStart_1566766 baseEnd_1566766 := by
    simpa [prefixWord, tailWord_1566766, baseEnd_1566766] using wordTrace_append hprefix tailTrace_1566766
  have hstable : (prefixWord ++ tailWord_1566766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566766).length < 2 ^ (prefixWord ++ tailWord_1566766).sum := by decide
  have hdescent : baseEnd_1566766 < baseStart_1566766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566869 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1566869 : Nat := 118140960795 + 1566869 * 2 ^ 59
def prefixEnd_1566869 : Nat := 4983230072969 + 3 ^ 40 * 1566869 * 2
def baseEnd_1566869 : Nat := 536371279753156901021071

theorem tailTrace_1566869 : CollatzResearch.WordTrace tailWord_1566869 prefixEnd_1566869 536371279753156901021071 := by
  unfold tailWord_1566869
  simp only [CollatzResearch.WordTrace]
  refine ⟨57148407360508687765591661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38098938240339125177061107 57148407360508687765591661)
  ·
    refine ⟨21430652760190757912096873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57148407360508687765591661 21430652760190757912096873)
    ·
      refine ⟨16072989570143068434072655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21430652760190757912096873 16072989570143068434072655)
      ·
        refine ⟨24109484355214602651108983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16072989570143068434072655 24109484355214602651108983)
        ·
          refine ⟨36164226532821903976663475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24109484355214602651108983 36164226532821903976663475)
          ·
            refine ⟨54246339799232855964995213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36164226532821903976663475 54246339799232855964995213)
            ·
              refine ⟨20342377424712320986873205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54246339799232855964995213 20342377424712320986873205)
              ·
                refine ⟨1907097883566780092519363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20342377424712320986873205 1907097883566780092519363)
                ·
                  refine ⟨2860646825350170138779045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907097883566780092519363 2860646825350170138779045)
                  ·
                    refine ⟨536371279753156901021071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860646825350170138779045 536371279753156901021071)
                    ·
                      rfl

theorem cell22_1566869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1566869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566869 prefixEnd_1566869 := by exact prefixLift 1566869
  have htrace : WordTrace (prefixWord ++ tailWord_1566869) baseStart_1566869 baseEnd_1566869 := by
    simpa [prefixWord, tailWord_1566869, baseEnd_1566869] using wordTrace_append hprefix tailTrace_1566869
  have hstable : (prefixWord ++ tailWord_1566869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566869).length < 2 ^ (prefixWord ++ tailWord_1566869).sum := by decide
  have hdescent : baseEnd_1566869 < baseStart_1566869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566890 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_1566890 : Nat := 118140960795 + 1566890 * 2 ^ 59
def prefixEnd_1566890 : Nat := 4983230072969 + 3 ^ 40 * 1566890 * 2
def baseEnd_1566890 : Nat := 178792822827439948748669

theorem tailTrace_1566890 : CollatzResearch.WordTrace tailWord_1566890 prefixEnd_1566890 178792822827439948748669 := by
  unfold tailWord_1566890
  simp only [CollatzResearch.WordTrace]
  refine ⟨14287293323358152088026531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38099448862288405568070749 14287293323358152088026531)
  ·
    refine ⟨21430939985037228132039797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14287293323358152088026531 21430939985037228132039797)
    ·
      refine ⟨2009150623597240137378731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21430939985037228132039797 2009150623597240137378731)
      ·
        refine ⟨3013725935395860206068097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009150623597240137378731 3013725935395860206068097)
        ·
          refine ⟨2260294451546895154551073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013725935395860206068097 2260294451546895154551073)
          ·
            refine ⟨1695220838660171365913305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2260294451546895154551073 1695220838660171365913305)
            ·
              refine ⟨1271415628995128524434979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695220838660171365913305 1271415628995128524434979)
              ·
                refine ⟨1907123443492692786652469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271415628995128524434979 1907123443492692786652469)
                ·
                  refine ⟨178792822827439948748669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1907123443492692786652469 178792822827439948748669)
                  ·
                    rfl

theorem cell22_1566890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_1566890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566890 prefixEnd_1566890 := by exact prefixLift 1566890
  have htrace : WordTrace (prefixWord ++ tailWord_1566890) baseStart_1566890 baseEnd_1566890 := by
    simpa [prefixWord, tailWord_1566890, baseEnd_1566890] using wordTrace_append hprefix tailTrace_1566890
  have hstable : (prefixWord ++ tailWord_1566890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566890).length < 2 ^ (prefixWord ++ tailWord_1566890).sum := by decide
  have hdescent : baseEnd_1566890 < baseStart_1566890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566916 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1566916 : Nat := 118140960795 + 1566916 * 2 ^ 59
def prefixEnd_1566916 : Nat := 4983230072969 + 3 ^ 40 * 1566916 * 2
def baseEnd_1566916 : Nat := 536387368813664445095927

theorem tailTrace_1566916 : CollatzResearch.WordTrace tailWord_1566916 prefixEnd_1566916 536387368813664445095927 := by
  unfold tailWord_1566916
  simp only [CollatzResearch.WordTrace]
  refine ⟨28575060795669207396276301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38100081060892276528368401 28575060795669207396276301)
  ·
    refine ⟨10715647798375952773603613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28575060795669207396276301 10715647798375952773603613)
    ·
      refine ⟨4018367924390982290101355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10715647798375952773603613 4018367924390982290101355)
      ·
        refine ⟨6027551886586473435152033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018367924390982290101355 6027551886586473435152033)
        ·
          refine ⟨4520663914939855076364025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6027551886586473435152033 4520663914939855076364025)
          ·
            refine ⟨3390497936204891307273019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520663914939855076364025 3390497936204891307273019)
            ·
              refine ⟨5085746904307336960909529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390497936204891307273019 5085746904307336960909529)
              ·
                refine ⟨3814310178230502720682147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5085746904307336960909529 3814310178230502720682147)
                ·
                  refine ⟨5721465267345754081023221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814310178230502720682147 5721465267345754081023221)
                  ·
                    refine ⟨536387368813664445095927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5721465267345754081023221 536387368813664445095927)
                    ·
                      rfl

theorem cell22_1566916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1566916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1566916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1566916 prefixEnd_1566916 := by exact prefixLift 1566916
  have htrace : WordTrace (prefixWord ++ tailWord_1566916) baseStart_1566916 baseEnd_1566916 := by
    simpa [prefixWord, tailWord_1566916, baseEnd_1566916] using wordTrace_append hprefix tailTrace_1566916
  have hstable : (prefixWord ++ tailWord_1566916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566916).length < 2 ^ (prefixWord ++ tailWord_1566916).sum := by decide
  have hdescent : baseEnd_1566916 < baseStart_1566916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567008 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 5]
def baseStart_1567008 : Nat := 118140960795 + 1567008 * 2 ^ 59
def prefixEnd_1567008 : Nat := 4983230072969 + 3 ^ 40 * 1567008 * 2
def baseEnd_1567008 : Nat := 178806287431268957265215

theorem tailTrace_1567008 : CollatzResearch.WordTrace tailWord_1567008 prefixEnd_1567008 178806287431268957265215 := by
  unfold tailWord_1567008
  simp only [CollatzResearch.WordTrace]
  refine ⟨28576738553502557252450839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38102318071336743003267785 28576738553502557252450839)
  ·
    refine ⟨42865107830253835878676259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28576738553502557252450839 42865107830253835878676259)
    ·
      refine ⟨64297661745380753818014389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42865107830253835878676259 64297661745380753818014389)
      ·
        refine ⟨6027905788629445670438849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64297661745380753818014389 6027905788629445670438849)
        ·
          refine ⟨4520929341472084252829137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6027905788629445670438849 4520929341472084252829137)
          ·
            refine ⟨3390697006104063189621853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520929341472084252829137 3390697006104063189621853)
            ·
              refine ⟨1271511377289023696108195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3390697006104063189621853 1271511377289023696108195)
              ·
                refine ⟨1907267065933535544162293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271511377289023696108195 1907267065933535544162293)
                ·
                  refine ⟨178806287431268957265215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1907267065933535544162293 178806287431268957265215)
                  ·
                    rfl

theorem cell22_1567008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_1567008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567008 prefixEnd_1567008 := by exact prefixLift 1567008
  have htrace : WordTrace (prefixWord ++ tailWord_1567008) baseStart_1567008 baseEnd_1567008 := by
    simpa [prefixWord, tailWord_1567008, baseEnd_1567008] using wordTrace_append hprefix tailTrace_1567008
  have hstable : (prefixWord ++ tailWord_1567008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567008).length < 2 ^ (prefixWord ++ tailWord_1567008).sum := by decide
  have hdescent : baseEnd_1567008 < baseStart_1567008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567038 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1567038 : Nat := 118140960795 + 1567038 * 2 ^ 59
def prefixEnd_1567038 : Nat := 4983230072969 + 3 ^ 40 * 1567038 * 2
def baseEnd_1567038 : Nat := 536429131906896793545553

theorem tailTrace_1567038 : CollatzResearch.WordTrace tailWord_1567038 prefixEnd_1567038 536429131906896793545553 := by
  unfold tailWord_1567038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144321412112053703561721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38103047531264286418995845 7144321412112053703561721)
  ·
    refine ⟨5358241059084040277671291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7144321412112053703561721 5358241059084040277671291)
    ·
      refine ⟨8037361588626060416506937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358241059084040277671291 8037361588626060416506937)
      ·
        refine ⟨6028021191469545312380203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8037361588626060416506937 6028021191469545312380203)
        ·
          refine ⟨9042031787204317968570305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028021191469545312380203 9042031787204317968570305)
          ·
            refine ⟨6781523840403238476427729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9042031787204317968570305 6781523840403238476427729)
            ·
              refine ⟨5086142880302428857320797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6781523840403238476427729 5086142880302428857320797)
              ·
                refine ⟨1907303580113410821495299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5086142880302428857320797 1907303580113410821495299)
                ·
                  refine ⟨2860955370170116232242949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907303580113410821495299 2860955370170116232242949)
                  ·
                    refine ⟨536429131906896793545553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860955370170116232242949 536429131906896793545553)
                    ·
                      rfl

theorem cell22_1567038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1567038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567038 prefixEnd_1567038 := by exact prefixLift 1567038
  have htrace : WordTrace (prefixWord ++ tailWord_1567038) baseStart_1567038 baseEnd_1567038 := by
    simpa [prefixWord, tailWord_1567038, baseEnd_1567038] using wordTrace_append hprefix tailTrace_1567038
  have hstable : (prefixWord ++ tailWord_1567038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567038).length < 2 ^ (prefixWord ++ tailWord_1567038).sum := by decide
  have hdescent : baseEnd_1567038 < baseStart_1567038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567188 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1567188 : Nat := 118140960795 + 1567188 * 2 ^ 59
def prefixEnd_1567188 : Nat := 4983230072969 + 3 ^ 40 * 1567188 * 2
def baseEnd_1567188 : Nat := 178826826657448800765031

theorem tailTrace_1567188 : CollatzResearch.WordTrace tailWord_1567188 prefixEnd_1567188 178826826657448800765031 := by
  unfold tailWord_1567188
  simp only [CollatzResearch.WordTrace]
  refine ⟨28580021123176502623227109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38106694830902003497636145 28580021123176502623227109)
  ·
    refine ⟨5358753960595594241855083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28580021123176502623227109 5358753960595594241855083)
    ·
      refine ⟨8038130940893391362782625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358753960595594241855083 8038130940893391362782625)
      ·
        refine ⟨6028598205670043522086969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038130940893391362782625 6028598205670043522086969)
        ·
          refine ⟨4521448654252532641565227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6028598205670043522086969 4521448654252532641565227)
          ·
            refine ⟨6782172981378798962347841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521448654252532641565227 6782172981378798962347841)
            ·
              refine ⟨5086629736034099221760881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6782172981378798962347841 5086629736034099221760881)
              ·
                refine ⟨3814972302025574416320661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086629736034099221760881 3814972302025574416320661)
                ·
                  refine ⟨178826826657448800765031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3814972302025574416320661 178826826657448800765031)
                  ·
                    rfl

theorem cell22_1567188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1567188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567188 prefixEnd_1567188 := by exact prefixLift 1567188
  have htrace : WordTrace (prefixWord ++ tailWord_1567188) baseStart_1567188 baseEnd_1567188 := by
    simpa [prefixWord, tailWord_1567188, baseEnd_1567188] using wordTrace_append hprefix tailTrace_1567188
  have hstable : (prefixWord ++ tailWord_1567188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567188).length < 2 ^ (prefixWord ++ tailWord_1567188).sum := by decide
  have hdescent : baseEnd_1567188 < baseStart_1567188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567201 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1567201 : Nat := 118140960795 + 1567201 * 2 ^ 59
def prefixEnd_1567201 : Nat := 4983230072969 + 3 ^ 40 * 1567201 * 2
def baseEnd_1567201 : Nat := 536484930138018701720053

theorem tailTrace_1567201 : CollatzResearch.WordTrace tailWord_1567201 prefixEnd_1567201 536484930138018701720053 := by
  unfold tailWord_1567201
  simp only [CollatzResearch.WordTrace]
  refine ⟨57160516395305908466677457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38107010930203938977784971 57160516395305908466677457)
  ·
    refine ⟨42870387296479431350008093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57160516395305908466677457 42870387296479431350008093)
    ·
      refine ⟨16076395236179786756253035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42870387296479431350008093 16076395236179786756253035)
      ·
        refine ⟨24114592854269680134379553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16076395236179786756253035 24114592854269680134379553)
        ·
          refine ⟨18085944640702260100784665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24114592854269680134379553 18085944640702260100784665)
          ·
            refine ⟨13564458480526695075588499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18085944640702260100784665 13564458480526695075588499)
            ·
              refine ⟨20346687720790042613382749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13564458480526695075588499 20346687720790042613382749)
              ·
                refine ⟨7630007895296265980018531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20346687720790042613382749 7630007895296265980018531)
                ·
                  refine ⟨11445011842944398970027797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630007895296265980018531 11445011842944398970027797)
                  ·
                    refine ⟨536484930138018701720053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11445011842944398970027797 536484930138018701720053)
                    ·
                      rfl

theorem cell22_1567201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1567201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567201 prefixEnd_1567201 := by exact prefixLift 1567201
  have htrace : WordTrace (prefixWord ++ tailWord_1567201) baseStart_1567201 baseEnd_1567201 := by
    simpa [prefixWord, tailWord_1567201, baseEnd_1567201] using wordTrace_append hprefix tailTrace_1567201
  have hstable : (prefixWord ++ tailWord_1567201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567201).length < 2 ^ (prefixWord ++ tailWord_1567201).sum := by decide
  have hdescent : baseEnd_1567201 < baseStart_1567201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567222 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1567222 : Nat := 118140960795 + 1567222 * 2 ^ 59
def prefixEnd_1567222 : Nat := 4983230072969 + 3 ^ 40 * 1567222 * 2
def baseEnd_1567222 : Nat := 178830706289060548981663

theorem tailTrace_1567222 : CollatzResearch.WordTrace tailWord_1567222 prefixEnd_1567222 178830706289060548981663 := by
  unfold tailWord_1567222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572580145514364315824495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38107521552153219368794613 3572580145514364315824495)
  ·
    refine ⟨5358870218271546473736743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3572580145514364315824495 5358870218271546473736743)
    ·
      refine ⟨8038305327407319710605115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358870218271546473736743 8038305327407319710605115)
      ·
        refine ⟨12057457991110979565907673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8038305327407319710605115 12057457991110979565907673)
        ·
          refine ⟨9043093493333234674430755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12057457991110979565907673 9043093493333234674430755)
          ·
            refine ⟨13564640239999852011646133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043093493333234674430755 13564640239999852011646133)
            ·
              refine ⟨1271685022499986126091825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13564640239999852011646133 1271685022499986126091825)
              ·
                refine ⟨953763766874989594568869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271685022499986126091825 953763766874989594568869)
                ·
                  refine ⟨178830706289060548981663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953763766874989594568869 178830706289060548981663)
                  ·
                    rfl

theorem cell22_1567222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1567222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567222 prefixEnd_1567222 := by exact prefixLift 1567222
  have htrace : WordTrace (prefixWord ++ tailWord_1567222) baseStart_1567222 baseEnd_1567222 := by
    simpa [prefixWord, tailWord_1567222, baseEnd_1567222] using wordTrace_append hprefix tailTrace_1567222
  have hstable : (prefixWord ++ tailWord_1567222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567222).length < 2 ^ (prefixWord ++ tailWord_1567222).sum := by decide
  have hdescent : baseEnd_1567222 < baseStart_1567222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567233 : List Nat := [1, 2, 4, 1, 3, 2, 2, 7]
def baseStart_1567233 : Nat := 118140960795 + 1567233 * 2 ^ 59
def prefixEnd_1567233 : Nat := 4983230072969 + 3 ^ 40 * 1567233 * 2
def baseEnd_1567233 : Nat := 59610653821331253879995

theorem tailTrace_1567233 : CollatzResearch.WordTrace tailWord_1567233 prefixEnd_1567233 59610653821331253879995 := by
  unfold tailWord_1567233
  simp only [CollatzResearch.WordTrace]
  refine ⟨57161683531189977931842353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38107789020793318621228235 57161683531189977931842353)
  ·
    refine ⟨42871262648392483448881765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57161683531189977931842353 42871262648392483448881765)
    ·
      refine ⟨8038361746573590646665331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42871262648392483448881765 8038361746573590646665331)
      ·
        refine ⟨12057542619860385969997997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8038361746573590646665331 12057542619860385969997997)
        ·
          refine ⟨4521578482447644738749249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12057542619860385969997997 4521578482447644738749249)
          ·
            refine ⟨3391183861835733554061937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521578482447644738749249 3391183861835733554061937)
            ·
              refine ⟨2543387896376800165546453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3391183861835733554061937 2543387896376800165546453)
              ·
                refine ⟨59610653821331253879995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2543387896376800165546453 59610653821331253879995)
                ·
                  rfl

theorem cell22_1567233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 7].length) (baseStart_1567233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567233 prefixEnd_1567233 := by exact prefixLift 1567233
  have htrace : WordTrace (prefixWord ++ tailWord_1567233) baseStart_1567233 baseEnd_1567233 := by
    simpa [prefixWord, tailWord_1567233, baseEnd_1567233] using wordTrace_append hprefix tailTrace_1567233
  have hstable : (prefixWord ++ tailWord_1567233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567233).length < 2 ^ (prefixWord ++ tailWord_1567233).sum := by decide
  have hdescent : baseEnd_1567233 < baseStart_1567233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567252 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1567252 : Nat := 118140960795 + 1567252 * 2 ^ 59
def prefixEnd_1567252 : Nat := 4983230072969 + 3 ^ 40 * 1567252 * 2
def baseEnd_1567252 : Nat := 536502388480271568694897

theorem tailTrace_1567252 : CollatzResearch.WordTrace tailWord_1567252 prefixEnd_1567252 536502388480271568694897 := by
  unfold tailWord_1567252
  simp only [CollatzResearch.WordTrace]
  refine ⟨28581188259060572088392005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38108251012080762784522673 28581188259060572088392005)
  ·
    refine ⟨5358972798573857266573501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28581188259060572088392005 5358972798573857266573501)
    ·
      refine ⟨2009614799465196474965063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5358972798573857266573501 2009614799465196474965063)
      ·
        refine ⟨3014422199197794712447595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009614799465196474965063 3014422199197794712447595)
        ·
          refine ⟨4521633298796692068671393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014422199197794712447595 4521633298796692068671393)
          ·
            refine ⟨3391224974097519051503545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521633298796692068671393 3391224974097519051503545)
            ·
              refine ⟨2543418730573139288627659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3391224974097519051503545 2543418730573139288627659)
              ·
                refine ⟨3815128095859708932941489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543418730573139288627659 3815128095859708932941489)
                ·
                  refine ⟨2861346071894781699706117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815128095859708932941489 2861346071894781699706117)
                  ·
                    refine ⟨536502388480271568694897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861346071894781699706117 536502388480271568694897)
                    ·
                      rfl

theorem cell22_1567252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1567252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567252 prefixEnd_1567252 := by exact prefixLift 1567252
  have htrace : WordTrace (prefixWord ++ tailWord_1567252) baseStart_1567252 baseEnd_1567252 := by
    simpa [prefixWord, tailWord_1567252, baseEnd_1567252] using wordTrace_append hprefix tailTrace_1567252
  have hstable : (prefixWord ++ tailWord_1567252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567252).length < 2 ^ (prefixWord ++ tailWord_1567252).sum := by decide
  have hdescent : baseEnd_1567252 < baseStart_1567252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567276 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1567276 : Nat := 118140960795 + 1567276 * 2 ^ 59
def prefixEnd_1567276 : Nat := 4983230072969 + 3 ^ 40 * 1567276 * 2
def baseEnd_1567276 : Nat := 536510604170743506094823

theorem tailTrace_1567276 : CollatzResearch.WordTrace tailWord_1567276 prefixEnd_1567276 536510604170743506094823 := by
  unfold tailWord_1567276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28581625935017098137828841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38108834580022797517105121 28581625935017098137828841)
  ·
    refine ⟨21436219451262823603371631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28581625935017098137828841 21436219451262823603371631)
    ·
      refine ⟨32154329176894235405057447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21436219451262823603371631 32154329176894235405057447)
      ·
        refine ⟨48231493765341353107586171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32154329176894235405057447 48231493765341353107586171)
        ·
          refine ⟨72347240648012029661379257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48231493765341353107586171 72347240648012029661379257)
          ·
            refine ⟨54260430486009022246034443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72347240648012029661379257 54260430486009022246034443)
            ·
              refine ⟨81390645729013533369051665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54260430486009022246034443 81390645729013533369051665)
              ·
                refine ⟨61042984296760150026788749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81390645729013533369051665 61042984296760150026788749)
                ·
                  refine ⟨22891119111285056260045781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61042984296760150026788749 22891119111285056260045781)
                  ·
                    refine ⟨536510604170743506094823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22891119111285056260045781 536510604170743506094823)
                    ·
                      rfl

theorem cell22_1567276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1567276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567276 prefixEnd_1567276 := by exact prefixLift 1567276
  have htrace : WordTrace (prefixWord ++ tailWord_1567276) baseStart_1567276 baseEnd_1567276 := by
    simpa [prefixWord, tailWord_1567276, baseEnd_1567276] using wordTrace_append hprefix tailTrace_1567276
  have hstable : (prefixWord ++ tailWord_1567276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567276).length < 2 ^ (prefixWord ++ tailWord_1567276).sum := by decide
  have hdescent : baseEnd_1567276 < baseStart_1567276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567284 : List Nat := [2, 5, 1, 3, 2, 1, 1, 7]
def baseStart_1567284 : Nat := 118140960795 + 1567284 * 2 ^ 59
def prefixEnd_1567284 : Nat := 4983230072969 + 3 ^ 40 * 1567284 * 2
def baseEnd_1567284 : Nat := 59612593637137127988311

theorem tailTrace_1567284 : CollatzResearch.WordTrace tailWord_1567284 prefixEnd_1567284 59612593637137127988311 := by
  unfold tailWord_1567284
  simp only [CollatzResearch.WordTrace]
  refine ⟨28581771827002606820974453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38109029102670142427965937 28581771827002606820974453)
  ·
    refine ⟨2679541108781494389466355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28581771827002606820974453 2679541108781494389466355)
    ·
      refine ⟨4019311663172241584199533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2679541108781494389466355 4019311663172241584199533)
      ·
        refine ⟨1507241873689590594074825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4019311663172241584199533 1507241873689590594074825)
        ·
          refine ⟨1130431405267192945556119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1507241873689590594074825 1130431405267192945556119)
          ·
            refine ⟨1695647107900789418334179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130431405267192945556119 1695647107900789418334179)
            ·
              refine ⟨2543470661851184127501269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695647107900789418334179 2543470661851184127501269)
              ·
                refine ⟨59612593637137127988311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2543470661851184127501269 59612593637137127988311)
                ·
                  rfl

theorem cell22_1567284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 7].length) (baseStart_1567284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567284 prefixEnd_1567284 := by exact prefixLift 1567284
  have htrace : WordTrace (prefixWord ++ tailWord_1567284) baseStart_1567284 baseEnd_1567284 := by
    simpa [prefixWord, tailWord_1567284, baseEnd_1567284] using wordTrace_append hprefix tailTrace_1567284
  have hstable : (prefixWord ++ tailWord_1567284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567284).length < 2 ^ (prefixWord ++ tailWord_1567284).sum := by decide
  have hdescent : baseEnd_1567284 < baseStart_1567284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567293 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1567293 : Nat := 118140960795 + 1567293 * 2 ^ 59
def prefixEnd_1567293 : Nat := 4983230072969 + 3 ^ 40 * 1567293 * 2
def baseEnd_1567293 : Nat := 536516423618161128419771

theorem tailTrace_1567293 : CollatzResearch.WordTrace tailWord_1567293 prefixEnd_1567293 536516423618161128419771 := by
  unfold tailWord_1567293
  simp only [CollatzResearch.WordTrace]
  refine ⟨57163871910972608179026533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38109247940648405452684355 57163871910972608179026533)
  ·
    refine ⟨10718225983307364033567475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57163871910972608179026533 10718225983307364033567475)
    ·
      refine ⟨16077338974961046050351213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718225983307364033567475 16077338974961046050351213)
      ·
        refine ⟨6029002115610392268881705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16077338974961046050351213 6029002115610392268881705)
        ·
          refine ⟨4521751586707794201661279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6029002115610392268881705 4521751586707794201661279)
          ·
            refine ⟨6782627380061691302491919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521751586707794201661279 6782627380061691302491919)
            ·
              refine ⟨10173941070092536953737879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782627380061691302491919 10173941070092536953737879)
              ·
                refine ⟨15260911605138805430606819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173941070092536953737879 15260911605138805430606819)
                ·
                  refine ⟨22891367407708208145910229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15260911605138805430606819 22891367407708208145910229)
                  ·
                    refine ⟨536516423618161128419771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22891367407708208145910229 536516423618161128419771)
                    ·
                      rfl

theorem cell22_1567293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1567293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567293 prefixEnd_1567293 := by exact prefixLift 1567293
  have htrace : WordTrace (prefixWord ++ tailWord_1567293) baseStart_1567293 baseEnd_1567293 := by
    simpa [prefixWord, tailWord_1567293, baseEnd_1567293] using wordTrace_append hprefix tailTrace_1567293
  have hstable : (prefixWord ++ tailWord_1567293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567293).length < 2 ^ (prefixWord ++ tailWord_1567293).sum := by decide
  have hdescent : baseEnd_1567293 < baseStart_1567293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567308 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1567308 : Nat := 118140960795 + 1567308 * 2 ^ 59
def prefixEnd_1567308 : Nat := 4983230072969 + 3 ^ 40 * 1567308 * 2
def baseEnd_1567308 : Nat := 536521558424706089294725

theorem tailTrace_1567308 : CollatzResearch.WordTrace tailWord_1567308 prefixEnd_1567308 536521558424706089294725 := by
  unfold tailWord_1567308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582209502959132870411289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38109612670612177160548385 28582209502959132870411289)
  ·
    refine ⟨21436657127219349652808467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28582209502959132870411289 21436657127219349652808467)
    ·
      refine ⟨32154985690829024479212701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21436657127219349652808467 32154985690829024479212701)
      ·
        refine ⟨12058119634060884179704763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32154985690829024479212701 12058119634060884179704763)
        ·
          refine ⟨18087179451091326269557145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12058119634060884179704763 18087179451091326269557145)
          ·
            refine ⟨13565384588318494702167859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18087179451091326269557145 13565384588318494702167859)
            ·
              refine ⟨20348076882477742053251789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13565384588318494702167859 20348076882477742053251789)
              ·
                refine ⟨7630528830929153269969421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20348076882477742053251789 7630528830929153269969421)
                ·
                  refine ⟨2861448311598432476238533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7630528830929153269969421 2861448311598432476238533)
                  ·
                    refine ⟨536521558424706089294725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861448311598432476238533 536521558424706089294725)
                    ·
                      rfl

theorem cell22_1567308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1567308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567308 prefixEnd_1567308 := by exact prefixLift 1567308
  have htrace : WordTrace (prefixWord ++ tailWord_1567308) baseStart_1567308 baseEnd_1567308 := by
    simpa [prefixWord, tailWord_1567308, baseEnd_1567308] using wordTrace_append hprefix tailTrace_1567308
  have hstable : (prefixWord ++ tailWord_1567308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567308).length < 2 ^ (prefixWord ++ tailWord_1567308).sum := by decide
  have hdescent : baseEnd_1567308 < baseStart_1567308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567340 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 4]
def baseStart_1567340 : Nat := 118140960795 + 1567340 * 2 ^ 59
def prefixEnd_1567340 : Nat := 4983230072969 + 3 ^ 40 * 1567340 * 2
def baseEnd_1567340 : Nat := 178844170892889557498209

theorem tailTrace_1567340 : CollatzResearch.WordTrace tailWord_1567340 prefixEnd_1567340 178844170892889557498209 := by
  unfold tailWord_1567340
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582793070901167602993737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38110390761201556803991649 28582793070901167602993737)
  ·
    refine ⟨21437094803175875702245303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28582793070901167602993737 21437094803175875702245303)
    ·
      refine ⟨32155642204763813553367955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21437094803175875702245303 32155642204763813553367955)
      ·
        refine ⟨48233463307145720330051933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32155642204763813553367955 48233463307145720330051933)
        ·
          refine ⟨18087548740179645123769475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48233463307145720330051933 18087548740179645123769475)
          ·
            refine ⟨27131323110269467685654213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18087548740179645123769475 27131323110269467685654213)
            ·
              refine ⟨5087123083175525191060165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27131323110269467685654213 5087123083175525191060165)
              ·
                refine ⟨953835578095410973323781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5087123083175525191060165 953835578095410973323781)
                ·
                  refine ⟨178844170892889557498209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953835578095410973323781 178844170892889557498209)
                  ·
                    rfl

theorem cell22_1567340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_1567340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567340 prefixEnd_1567340 := by exact prefixLift 1567340
  have htrace : WordTrace (prefixWord ++ tailWord_1567340) baseStart_1567340 baseEnd_1567340 := by
    simpa [prefixWord, tailWord_1567340, baseEnd_1567340] using wordTrace_append hprefix tailTrace_1567340
  have hstable : (prefixWord ++ tailWord_1567340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567340).length < 2 ^ (prefixWord ++ tailWord_1567340).sum := by decide
  have hdescent : baseEnd_1567340 < baseStart_1567340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567353 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_1567353 : Nat := 118140960795 + 1567353 * 2 ^ 59
def prefixEnd_1567353 : Nat := 4983230072969 + 3 ^ 40 * 1567353 * 2
def baseEnd_1567353 : Nat := 536536962844340971919587

theorem tailTrace_1567353 : CollatzResearch.WordTrace tailWord_1567353 prefixEnd_1567353 536536962844340971919587 := by
  unfold tailWord_1567353
  simp only [CollatzResearch.WordTrace]
  refine ⟨57166060290755238426210713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38110706860503492284140475 57166060290755238426210713)
  ·
    refine ⟨42874545218066428819658035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57166060290755238426210713 42874545218066428819658035)
    ·
      refine ⟨64311817827099643229487053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42874545218066428819658035 64311817827099643229487053)
      ·
        refine ⟨24116931685162366211057645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64311817827099643229487053 24116931685162366211057645)
        ·
          refine ⟨9043849381935887329146617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24116931685162366211057645 9043849381935887329146617)
          ·
            refine ⟨6782887036451915496859963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9043849381935887329146617 6782887036451915496859963)
            ·
              refine ⟨10174330554677873245289945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782887036451915496859963 10174330554677873245289945)
              ·
                refine ⟨7630747916008404933967459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10174330554677873245289945 7630747916008404933967459)
                ·
                  refine ⟨11446121874012607400951189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630747916008404933967459 11446121874012607400951189)
                  ·
                    refine ⟨536536962844340971919587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11446121874012607400951189 536536962844340971919587)
                    ·
                      rfl

theorem cell22_1567353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_1567353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567353 prefixEnd_1567353 := by exact prefixLift 1567353
  have htrace : WordTrace (prefixWord ++ tailWord_1567353) baseStart_1567353 baseEnd_1567353 := by
    simpa [prefixWord, tailWord_1567353, baseEnd_1567353] using wordTrace_append hprefix tailTrace_1567353
  have hstable : (prefixWord ++ tailWord_1567353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567353).length < 2 ^ (prefixWord ++ tailWord_1567353).sum := by decide
  have hdescent : baseEnd_1567353 < baseStart_1567353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567406 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1567406 : Nat := 118140960795 + 1567406 * 2 ^ 59
def prefixEnd_1567406 : Nat := 4983230072969 + 3 ^ 40 * 1567406 * 2
def baseEnd_1567406 : Nat := 536555105827466500344425

theorem tailTrace_1567406 : CollatzResearch.WordTrace tailWord_1567406 prefixEnd_1567406 536555105827466500344425 := by
  unfold tailWord_1567406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145999169945403559736259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38111995573042152318593381 7145999169945403559736259)
  ·
    refine ⟨10718998754918105339604389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7145999169945403559736259 10718998754918105339604389)
    ·
      refine ⟨2009812266547144751175823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10718998754918105339604389 2009812266547144751175823)
      ·
        refine ⟨3014718399820717126763735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009812266547144751175823 3014718399820717126763735)
        ·
          refine ⟨4522077599731075690145603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014718399820717126763735 4522077599731075690145603)
          ·
            refine ⟨6783116399596613535218405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522077599731075690145603 6783116399596613535218405)
            ·
              refine ⟨1271834324924365037853451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6783116399596613535218405 1271834324924365037853451)
              ·
                refine ⟨1907751487386547556780177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271834324924365037853451 1907751487386547556780177)
                ·
                  refine ⟨1430813615539910667585133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1907751487386547556780177 1430813615539910667585133)
                  ·
                    refine ⟨536555105827466500344425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1430813615539910667585133 536555105827466500344425)
                    ·
                      rfl

theorem cell22_1567406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1567406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567406 prefixEnd_1567406 := by exact prefixLift 1567406
  have htrace : WordTrace (prefixWord ++ tailWord_1567406) baseStart_1567406 baseEnd_1567406 := by
    simpa [prefixWord, tailWord_1567406, baseEnd_1567406] using wordTrace_append hprefix tailTrace_1567406
  have hstable : (prefixWord ++ tailWord_1567406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567406).length < 2 ^ (prefixWord ++ tailWord_1567406).sum := by decide
  have hdescent : baseEnd_1567406 < baseStart_1567406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567460 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1567460 : Nat := 118140960795 + 1567460 * 2 ^ 59
def prefixEnd_1567460 : Nat := 4983230072969 + 3 ^ 40 * 1567460 * 2
def baseEnd_1567460 : Nat := 536573591131028359494259

theorem tailTrace_1567460 : CollatzResearch.WordTrace tailWord_1567460 prefixEnd_1567460 536573591131028359494259 := by
  unfold tailWord_1567460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28584981450683797850177917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38113308600911730466903889 28584981450683797850177917)
  ·
    refine ⟨10719368044006424193816719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28584981450683797850177917 10719368044006424193816719)
    ·
      refine ⟨16079052066009636290725079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719368044006424193816719 16079052066009636290725079)
      ·
        refine ⟨24118578099014454436087619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16079052066009636290725079 24118578099014454436087619)
        ·
          refine ⟨36177867148521681654131429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24118578099014454436087619 36177867148521681654131429)
          ·
            refine ⟨6783350090347815310149643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36177867148521681654131429 6783350090347815310149643)
            ·
              refine ⟨10175025135521722965224465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783350090347815310149643 10175025135521722965224465)
              ·
                refine ⟨7631268851641292223918349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10175025135521722965224465 7631268851641292223918349)
                ·
                  refine ⟨2861725819365484583969381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7631268851641292223918349 2861725819365484583969381)
                  ·
                    refine ⟨536573591131028359494259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861725819365484583969381 536573591131028359494259)
                    ·
                      rfl

theorem cell22_1567460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1567460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567460 prefixEnd_1567460 := by exact prefixLift 1567460
  have htrace : WordTrace (prefixWord ++ tailWord_1567460) baseStart_1567460 baseEnd_1567460 := by
    simpa [prefixWord, tailWord_1567460, baseEnd_1567460] using wordTrace_append hprefix tailTrace_1567460
  have hstable : (prefixWord ++ tailWord_1567460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567460).length < 2 ^ (prefixWord ++ tailWord_1567460).sum := by decide
  have hdescent : baseEnd_1567460 < baseStart_1567460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567503 : List Nat := [1, 1, 2, 1, 1, 1, 15]
def baseStart_1567503 : Nat := 118140960795 + 1567503 * 2 ^ 59
def prefixEnd_1567503 : Nat := 4983230072969 + 3 ^ 40 * 1567503 * 2
def baseEnd_1567503 : Nat := 19873641144807058543301

theorem tailTrace_1567503 : CollatzResearch.WordTrace tailWord_1567503 prefixEnd_1567503 19873641144807058543301 := by
  unfold tailWord_1567503
  simp only [CollatzResearch.WordTrace]
  refine ⟨57171531240211814044171163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38114354160141209362780775 57171531240211814044171163)
  ·
    refine ⟨85757296860317721066256745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57171531240211814044171163 85757296860317721066256745)
    ·
      refine ⟨64317972645238290799692559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85757296860317721066256745 64317972645238290799692559)
      ·
        refine ⟨96476958967857436199538839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64317972645238290799692559 96476958967857436199538839)
        ·
          refine ⟨144715438451786154299308259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96476958967857436199538839 144715438451786154299308259)
          ·
            refine ⟨217073157677679231448962389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144715438451786154299308259 217073157677679231448962389)
            ·
              refine ⟨19873641144807058543301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 217073157677679231448962389 19873641144807058543301)
              ·
                rfl

theorem cell22_1567503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 15].length) (baseStart_1567503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567503 prefixEnd_1567503 := by exact prefixLift 1567503
  have htrace : WordTrace (prefixWord ++ tailWord_1567503) baseStart_1567503 baseEnd_1567503 := by
    simpa [prefixWord, tailWord_1567503, baseEnd_1567503] using wordTrace_append hprefix tailTrace_1567503
  have hstable : (prefixWord ++ tailWord_1567503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567503).length < 2 ^ (prefixWord ++ tailWord_1567503).sum := by decide
  have hdescent : baseEnd_1567503 < baseStart_1567503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567505 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_1567505 : Nat := 118140960795 + 1567505 * 2 ^ 59
def prefixEnd_1567505 : Nat := 4983230072969 + 3 ^ 40 * 1567505 * 2
def baseEnd_1567505 : Nat := 536588995550663242119121

theorem tailTrace_1567505 : CollatzResearch.WordTrace tailWord_1567505 prefixEnd_1567505 536588995550663242119121 := by
  unfold tailWord_1567505
  simp only [CollatzResearch.WordTrace]
  refine ⟨57171604186204568385743969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38114402790803045590495979 57171604186204568385743969)
  ·
    refine ⟨42878703139653426289307977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57171604186204568385743969 42878703139653426289307977)
    ·
      refine ⟨32159027354740069716980983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42878703139653426289307977 32159027354740069716980983)
      ·
        refine ⟨48238541032110104575471475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32159027354740069716980983 48238541032110104575471475)
        ·
          refine ⟨72357811548165156863207213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48238541032110104575471475 72357811548165156863207213)
          ·
            refine ⟨27134179330561933823702705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72357811548165156863207213 27134179330561933823702705)
            ·
              refine ⟨20350634497921450367777029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27134179330561933823702705 20350634497921450367777029)
              ·
                refine ⟨3815743968360271943958193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20350634497921450367777029 3815743968360271943958193)
                ·
                  refine ⟨2861807976270203957968645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815743968360271943958193 2861807976270203957968645)
                  ·
                    refine ⟨536588995550663242119121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861807976270203957968645 536588995550663242119121)
                    ·
                      rfl

theorem cell22_1567505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_1567505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567505 prefixEnd_1567505 := by exact prefixLift 1567505
  have htrace : WordTrace (prefixWord ++ tailWord_1567505) baseStart_1567505 baseEnd_1567505 := by
    simpa [prefixWord, tailWord_1567505, baseEnd_1567505] using wordTrace_append hprefix tailTrace_1567505
  have hstable : (prefixWord ++ tailWord_1567505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567505).length < 2 ^ (prefixWord ++ tailWord_1567505).sum := by decide
  have hdescent : baseEnd_1567505 < baseStart_1567505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567524 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1567524 : Nat := 118140960795 + 1567524 * 2 ^ 59
def prefixEnd_1567524 : Nat := 4983230072969 + 3 ^ 40 * 1567524 * 2
def baseEnd_1567524 : Nat := 536595499638953525894063

theorem tailTrace_1567524 : CollatzResearch.WordTrace tailWord_1567524 prefixEnd_1567524 536595499638953525894063 := by
  unfold tailWord_1567524
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586148586567867315342813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38114864782090489753790417 28586148586567867315342813)
  ·
    refine ⟨10719805719962950243253555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28586148586567867315342813 10719805719962950243253555)
    ·
      refine ⟨16079708579944425364880333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719805719962950243253555 16079708579944425364880333)
      ·
        refine ⟨6029890717479159511830125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16079708579944425364880333 6029890717479159511830125)
        ·
          refine ⟨2261209019054684816936297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6029890717479159511830125 2261209019054684816936297)
          ·
            refine ⟨1695906764291013612702223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2261209019054684816936297 1695906764291013612702223)
            ·
              refine ⟨2543860146436520419053335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695906764291013612702223 2543860146436520419053335)
              ·
                refine ⟨3815790219654780628580003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543860146436520419053335 3815790219654780628580003)
                ·
                  refine ⟨5723685329482170942870005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815790219654780628580003 5723685329482170942870005)
                  ·
                    refine ⟨536595499638953525894063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5723685329482170942870005 536595499638953525894063)
                    ·
                      rfl

theorem cell22_1567524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1567524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567524 prefixEnd_1567524 := by exact prefixLift 1567524
  have htrace : WordTrace (prefixWord ++ tailWord_1567524) baseStart_1567524 baseEnd_1567524 := by
    simpa [prefixWord, tailWord_1567524, baseEnd_1567524] using wordTrace_append hprefix tailTrace_1567524
  have hstable : (prefixWord ++ tailWord_1567524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567524).length < 2 ^ (prefixWord ++ tailWord_1567524).sum := by decide
  have hdescent : baseEnd_1567524 < baseStart_1567524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567556 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1567556 : Nat := 118140960795 + 1567556 * 2 ^ 59
def prefixEnd_1567556 : Nat := 4983230072969 + 3 ^ 40 * 1567556 * 2
def baseEnd_1567556 : Nat := 536606453892916109093965

theorem tailTrace_1567556 : CollatzResearch.WordTrace tailWord_1567556 prefixEnd_1567556 536606453892916109093965 := by
  unfold tailWord_1567556
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586732154509902047925261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38115642872679869397233681 28586732154509902047925261)
  ·
    refine ⟨10720024557941213267971973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28586732154509902047925261 10720024557941213267971973)
    ·
      refine ⟨2010004604613977487744745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10720024557941213267971973 2010004604613977487744745)
      ·
        refine ⟨1507503453460483115808559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2010004604613977487744745 1507503453460483115808559)
        ·
          refine ⟨2261255180190724673712839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507503453460483115808559 2261255180190724673712839)
          ·
            refine ⟨3391882770286087010569259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261255180190724673712839 3391882770286087010569259)
            ·
              refine ⟨5087824155429130515853889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391882770286087010569259 5087824155429130515853889)
              ·
                refine ⟨3815868116571847886890417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087824155429130515853889 3815868116571847886890417)
                ·
                  refine ⟨2861901087428885915167813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815868116571847886890417 2861901087428885915167813)
                  ·
                    refine ⟨536606453892916109093965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861901087428885915167813 536606453892916109093965)
                    ·
                      rfl

theorem cell22_1567556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1567556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567556 prefixEnd_1567556 := by exact prefixLift 1567556
  have htrace : WordTrace (prefixWord ++ tailWord_1567556) baseStart_1567556 baseEnd_1567556 := by
    simpa [prefixWord, tailWord_1567556, baseEnd_1567556] using wordTrace_append hprefix tailTrace_1567556
  have hstable : (prefixWord ++ tailWord_1567556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567556).length < 2 ^ (prefixWord ++ tailWord_1567556).sum := by decide
  have hdescent : baseEnd_1567556 < baseStart_1567556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567612 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1567612 : Nat := 118140960795 + 1567612 * 2 ^ 59
def prefixEnd_1567612 : Nat := 4983230072969 + 3 ^ 40 * 1567612 * 2
def baseEnd_1567612 : Nat := 536625623837350629693793

theorem tailTrace_1567612 : CollatzResearch.WordTrace tailWord_1567612 prefixEnd_1567612 536625623837350629693793 := by
  unfold tailWord_1567612
  simp only [CollatzResearch.WordTrace]
  refine ⟨28587753398408462829944545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38117004531211283773259393 28587753398408462829944545)
  ·
    refine ⟨21440815048806347122458409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28587753398408462829944545 21440815048806347122458409)
    ·
      refine ⟨16080611286604760341843807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21440815048806347122458409 16080611286604760341843807)
      ·
        refine ⟨24120916929907140512765711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16080611286604760341843807 24120916929907140512765711)
        ·
          refine ⟨36181375394860710769148567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120916929907140512765711 36181375394860710769148567)
          ·
            refine ⟨54272063092291066153722851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36181375394860710769148567 54272063092291066153722851)
            ·
              refine ⟨81408094638436599230584277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54272063092291066153722851 81408094638436599230584277)
              ·
                refine ⟨1908002218088357794466819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81408094638436599230584277 1908002218088357794466819)
                ·
                  refine ⟨2862003327132536691700229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908002218088357794466819 2862003327132536691700229)
                  ·
                    refine ⟨536625623837350629693793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2862003327132536691700229 536625623837350629693793)
                    ·
                      rfl

theorem cell22_1567612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1567612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567612 prefixEnd_1567612 := by exact prefixLift 1567612
  have htrace : WordTrace (prefixWord ++ tailWord_1567612) baseStart_1567612 baseEnd_1567612 := by
    simpa [prefixWord, tailWord_1567612, baseEnd_1567612] using wordTrace_append hprefix tailTrace_1567612
  have hstable : (prefixWord ++ tailWord_1567612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567612).length < 2 ^ (prefixWord ++ tailWord_1567612).sum := by decide
  have hdescent : baseEnd_1567612 < baseStart_1567612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567644 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_1567644 : Nat := 118140960795 + 1567644 * 2 ^ 59
def prefixEnd_1567644 : Nat := 4983230072969 + 3 ^ 40 * 1567644 * 2
def baseEnd_1567644 : Nat := 178878859363771070964565

theorem tailTrace_1567644 : CollatzResearch.WordTrace tailWord_1567644 prefixEnd_1567644 178878859363771070964565 := by
  unfold tailWord_1567644
  simp only [CollatzResearch.WordTrace]
  refine ⟨28588336966350497562526993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38117782621800663416702657 28588336966350497562526993)
  ·
    refine ⟨21441252724762873171895245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28588336966350497562526993 21441252724762873171895245)
    ·
      refine ⟨8040469771786077439460717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21441252724762873171895245 8040469771786077439460717)
      ·
        refine ⟨3015176164419779039797769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8040469771786077439460717 3015176164419779039797769)
        ·
          refine ⟨2261382123314834279848327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3015176164419779039797769 2261382123314834279848327)
          ·
            refine ⟨3392073184972251419772491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261382123314834279848327 3392073184972251419772491)
            ·
              refine ⟨5088109777458377129658737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392073184972251419772491 5088109777458377129658737)
              ·
                refine ⟨3816082333093782847244053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088109777458377129658737 3816082333093782847244053)
                ·
                  refine ⟨178878859363771070964565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3816082333093782847244053 178878859363771070964565)
                  ·
                    rfl

theorem cell22_1567644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_1567644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567644 prefixEnd_1567644 := by exact prefixLift 1567644
  have htrace : WordTrace (prefixWord ++ tailWord_1567644) baseStart_1567644 baseEnd_1567644 := by
    simpa [prefixWord, tailWord_1567644, baseEnd_1567644] using wordTrace_append hprefix tailTrace_1567644
  have hstable : (prefixWord ++ tailWord_1567644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567644).length < 2 ^ (prefixWord ++ tailWord_1567644).sum := by decide
  have hdescent : baseEnd_1567644 < baseStart_1567644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567704 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_1567704 : Nat := 118140960795 + 1567704 * 2 ^ 59
def prefixEnd_1567704 : Nat := 4983230072969 + 3 ^ 40 * 1567704 * 2
def baseEnd_1567704 : Nat := 536657117317493056393511

theorem tailTrace_1567704 : CollatzResearch.WordTrace tailWord_1567704 prefixEnd_1567704 536657117317493056393511 := by
  unfold tailWord_1567704
  simp only [CollatzResearch.WordTrace]
  refine ⟨28589431156241812686119083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38119241541655750248158777 28589431156241812686119083)
  ·
    refine ⟨42884146734362719029178625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28589431156241812686119083 42884146734362719029178625)
    ·
      refine ⟨32163110050772039271883969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42884146734362719029178625 32163110050772039271883969)
      ·
        refine ⟨24122332538079029453912977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32163110050772039271883969 24122332538079029453912977)
        ·
          refine ⟨18091749403559272090434733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24122332538079029453912977 18091749403559272090434733)
          ·
            refine ⟨6784406026334727033913025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18091749403559272090434733 6784406026334727033913025)
            ·
              refine ⟨5088304519751045275434769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6784406026334727033913025 5088304519751045275434769)
              ·
                refine ⟨3816228389813283956576077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088304519751045275434769 3816228389813283956576077)
                ·
                  refine ⟨1431085646179981483716029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3816228389813283956576077 1431085646179981483716029)
                  ·
                    refine ⟨536657117317493056393511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431085646179981483716029 536657117317493056393511)
                    ·
                      rfl

theorem cell22_1567704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_1567704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567704 prefixEnd_1567704 := by exact prefixLift 1567704
  have htrace : WordTrace (prefixWord ++ tailWord_1567704) baseStart_1567704 baseEnd_1567704 := by
    simpa [prefixWord, tailWord_1567704, baseEnd_1567704] using wordTrace_append hprefix tailTrace_1567704
  have hstable : (prefixWord ++ tailWord_1567704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567704).length < 2 ^ (prefixWord ++ tailWord_1567704).sum := by decide
  have hdescent : baseEnd_1567704 < baseStart_1567704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567734 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_1567734 : Nat := 118140960795 + 1567734 * 2 ^ 59
def prefixEnd_1567734 : Nat := 4983230072969 + 3 ^ 40 * 1567734 * 2
def baseEnd_1567734 : Nat := 178889128976860992714473

theorem tailTrace_1567734 : CollatzResearch.WordTrace tailWord_1567734 prefixEnd_1567734 178889128976860992714473 := by
  unfold tailWord_1567734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573747281398433780989391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38119971001583293663886837 3573747281398433780989391)
  ·
    refine ⟨5360620922097650671484087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573747281398433780989391 5360620922097650671484087)
    ·
      refine ⟨8040931383146476007226131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360620922097650671484087 8040931383146476007226131)
      ·
        refine ⟨12061397074719714010839197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040931383146476007226131 12061397074719714010839197)
        ·
          refine ⟨4523023903019892754064699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12061397074719714010839197 4523023903019892754064699)
          ·
            refine ⟨6784535854529839131097049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523023903019892754064699 6784535854529839131097049)
            ·
              refine ⟨5088401890897379348322787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6784535854529839131097049 5088401890897379348322787)
              ·
                refine ⟨7632602836346069022484181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088401890897379348322787 7632602836346069022484181)
                ·
                  refine ⟨178889128976860992714473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7632602836346069022484181 178889128976860992714473)
                  ·
                    rfl

theorem cell22_1567734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_1567734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567734 prefixEnd_1567734 := by exact prefixLift 1567734
  have htrace : WordTrace (prefixWord ++ tailWord_1567734) baseStart_1567734 baseEnd_1567734 := by
    simpa [prefixWord, tailWord_1567734, baseEnd_1567734] using wordTrace_append hprefix tailTrace_1567734
  have hstable : (prefixWord ++ tailWord_1567734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567734).length < 2 ^ (prefixWord ++ tailWord_1567734).sum := by decide
  have hdescent : baseEnd_1567734 < baseStart_1567734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567781 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_1567781 : Nat := 118140960795 + 1567781 * 2 ^ 59
def prefixEnd_1567781 : Nat := 4983230072969 + 3 ^ 40 * 1567781 * 2
def baseEnd_1567781 : Nat := 536683475991090522218275

theorem tailTrace_1567781 : CollatzResearch.WordTrace tailWord_1567781 prefixEnd_1567781 536683475991090522218275 := by
  unfold tailWord_1567781
  simp only [CollatzResearch.WordTrace]
  refine ⟨57181670733204667522791197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38121113822136445015194131 57181670733204667522791197)
  ·
    refine ⟨21443126524951750321046699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57181670733204667522791197 21443126524951750321046699)
    ·
      refine ⟨32164689787427625481570049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21443126524951750321046699 32164689787427625481570049)
      ·
        refine ⟨24123517340570719111177537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32164689787427625481570049 24123517340570719111177537)
        ·
          refine ⟨18092638005428039333383153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24123517340570719111177537 18092638005428039333383153)
          ·
            refine ⟨13569478504071029500037365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18092638005428039333383153 13569478504071029500037365)
            ·
              refine ⟨1272138609756659015628503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13569478504071029500037365 1272138609756659015628503)
              ·
                refine ⟨1908207914634988523442755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272138609756659015628503 1908207914634988523442755)
                ·
                  refine ⟨2862311871952482785164133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908207914634988523442755 2862311871952482785164133)
                  ·
                    refine ⟨536683475991090522218275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2862311871952482785164133 536683475991090522218275)
                    ·
                      rfl

theorem cell22_1567781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_1567781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567781 prefixEnd_1567781 := by exact prefixLift 1567781
  have htrace : WordTrace (prefixWord ++ tailWord_1567781) baseStart_1567781 baseEnd_1567781 := by
    simpa [prefixWord, tailWord_1567781, baseEnd_1567781] using wordTrace_append hprefix tailTrace_1567781
  have hstable : (prefixWord ++ tailWord_1567781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567781).length < 2 ^ (prefixWord ++ tailWord_1567781).sum := by decide
  have hdescent : baseEnd_1567781 < baseStart_1567781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567826 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1567826 : Nat := 118140960795 + 1567826 * 2 ^ 59
def prefixEnd_1567826 : Nat := 4983230072969 + 3 ^ 40 * 1567826 * 2
def baseEnd_1567826 : Nat := 536698880410725404843137

theorem tailTrace_1567826 : CollatzResearch.WordTrace tailWord_1567826 prefixEnd_1567826 536698880410725404843137 := by
  unfold tailWord_1567826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14295828004510410052044833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38122208012027760138786221 14295828004510410052044833)
  ·
    refine ⟨10721871003382807539033625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14295828004510410052044833 10721871003382807539033625)
    ·
      refine ⟨8041403252537105654275219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10721871003382807539033625 8041403252537105654275219)
      ·
        refine ⟨12062104878805658481412829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8041403252537105654275219 12062104878805658481412829)
        ·
          refine ⟨4523289329552121930529811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12062104878805658481412829 4523289329552121930529811)
          ·
            refine ⟨6784933994328182895794717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523289329552121930529811 6784933994328182895794717)
            ·
              refine ⟨2544350247873068585923019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6784933994328182895794717 2544350247873068585923019)
              ·
                refine ⟨3816525371809602878884529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544350247873068585923019 3816525371809602878884529)
                ·
                  refine ⟨2862394028857202159163397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816525371809602878884529 2862394028857202159163397)
                  ·
                    refine ⟨536698880410725404843137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2862394028857202159163397 536698880410725404843137)
                    ·
                      rfl

theorem cell22_1567826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1567826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567826 prefixEnd_1567826 := by exact prefixLift 1567826
  have htrace : WordTrace (prefixWord ++ tailWord_1567826) baseStart_1567826 baseEnd_1567826 := by
    simpa [prefixWord, tailWord_1567826, baseEnd_1567826] using wordTrace_append hprefix tailTrace_1567826
  have hstable : (prefixWord ++ tailWord_1567826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567826).length < 2 ^ (prefixWord ++ tailWord_1567826).sum := by decide
  have hdescent : baseEnd_1567826 < baseStart_1567826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567839 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 5, 3]
def baseStart_1567839 : Nat := 118140960795 + 1567839 * 2 ^ 59
def prefixEnd_1567839 : Nat := 4983230072969 + 3 ^ 40 * 1567839 * 2
def baseEnd_1567839 : Nat := 536703330576397704268097

theorem tailTrace_1567839 : CollatzResearch.WordTrace tailWord_1567839 prefixEnd_1567839 536703330576397704268097 := by
  unfold tailWord_1567839
  simp only [CollatzResearch.WordTrace]
  refine ⟨57183786166994543428402571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38122524111329695618935047 57183786166994543428402571)
  ·
    refine ⟨85775679250491815142603857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57183786166994543428402571 85775679250491815142603857)
    ·
      refine ⟨64331759437868861356952893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85775679250491815142603857 64331759437868861356952893)
      ·
        refine ⟨24124409789200823008857335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64331759437868861356952893 24124409789200823008857335)
        ·
          refine ⟨36186614683801234513286003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24124409789200823008857335 36186614683801234513286003)
          ·
            refine ⟨54279922025701851769929005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36186614683801234513286003 54279922025701851769929005)
            ·
              refine ⟨20354970759638194413723377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54279922025701851769929005 20354970759638194413723377)
              ·
                refine ⟨15266228069728645810292533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20354970759638194413723377 15266228069728645810292533)
                ·
                  refine ⟨1431208881537060544714925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15266228069728645810292533 1431208881537060544714925)
                  ·
                    refine ⟨536703330576397704268097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431208881537060544714925 536703330576397704268097)
                    ·
                      rfl

theorem cell22_1567839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_1567839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567839 prefixEnd_1567839 := by exact prefixLift 1567839
  have htrace : WordTrace (prefixWord ++ tailWord_1567839) baseStart_1567839 baseEnd_1567839 := by
    simpa [prefixWord, tailWord_1567839, baseEnd_1567839] using wordTrace_append hprefix tailTrace_1567839
  have hstable : (prefixWord ++ tailWord_1567839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567839).length < 2 ^ (prefixWord ++ tailWord_1567839).sum := by decide
  have hdescent : baseEnd_1567839 < baseStart_1567839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567856 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_1567856 : Nat := 118140960795 + 1567856 * 2 ^ 59
def prefixEnd_1567856 : Nat := 4983230072969 + 3 ^ 40 * 1567856 * 2
def baseEnd_1567856 : Nat := 536709150023815326593045

theorem tailTrace_1567856 : CollatzResearch.WordTrace tailWord_1567856 prefixEnd_1567856 536709150023815326593045 := by
  unfold tailWord_1567856
  simp only [CollatzResearch.WordTrace]
  refine ⟨28592203103966477665885711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38122937471955303554514281 28592203103966477665885711)
  ·
    refine ⟨42888304655949716498828567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28592203103966477665885711 42888304655949716498828567)
    ·
      refine ⟨64332456983924574748242851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42888304655949716498828567 64332456983924574748242851)
      ·
        refine ⟨96498685475886862122364277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64332456983924574748242851 96498685475886862122364277)
        ·
          refine ⟨9046751763364393323971651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96498685475886862122364277 9046751763364393323971651)
          ·
            refine ⟨13570127645046589985957477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9046751763364393323971651 13570127645046589985957477)
            ·
              refine ⟨2544398933446235622367027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13570127645046589985957477 2544398933446235622367027)
              ·
                refine ⟨3816598400169353433550541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544398933446235622367027 3816598400169353433550541)
                ·
                  refine ⟨1431224400063507537581453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3816598400169353433550541 1431224400063507537581453)
                  ·
                    refine ⟨536709150023815326593045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431224400063507537581453 536709150023815326593045)
                    ·
                      rfl

theorem cell22_1567856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_1567856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567856 prefixEnd_1567856 := by exact prefixLift 1567856
  have htrace : WordTrace (prefixWord ++ tailWord_1567856) baseStart_1567856 baseEnd_1567856 := by
    simpa [prefixWord, tailWord_1567856, baseEnd_1567856] using wordTrace_append hprefix tailTrace_1567856
  have hstable : (prefixWord ++ tailWord_1567856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567856).length < 2 ^ (prefixWord ++ tailWord_1567856).sum := by decide
  have hdescent : baseEnd_1567856 < baseStart_1567856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567890 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1567890 : Nat := 118140960795 + 1567890 * 2 ^ 59
def prefixEnd_1567890 : Nat := 4983230072969 + 3 ^ 40 * 1567890 * 2
def baseEnd_1567890 : Nat := 536720788918650571242941

theorem tailTrace_1567890 : CollatzResearch.WordTrace tailWord_1567890 prefixEnd_1567890 536720788918650571242941 := by
  unfold tailWord_1567890
  simp only [CollatzResearch.WordTrace]
  refine ⟨14296411572452444784627281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38123764193206519425672749 14296411572452444784627281)
  ·
    refine ⟨10722308679339333588470461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14296411572452444784627281 10722308679339333588470461)
    ·
      refine ⟨4020865754752250095676423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10722308679339333588470461 4020865754752250095676423)
      ·
        refine ⟨6031298632128375143514635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020865754752250095676423 6031298632128375143514635)
        ·
          refine ⟨9046947948192562715271953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031298632128375143514635 9046947948192562715271953)
          ·
            refine ⟨6785210961144422036453965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9046947948192562715271953 6785210961144422036453965)
            ·
              refine ⟨2544454110429158263670237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6785210961144422036453965 2544454110429158263670237)
              ·
                refine ⟨954170291410934348876339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2544454110429158263670237 954170291410934348876339)
                ·
                  refine ⟨1431255437116401523314509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954170291410934348876339 1431255437116401523314509)
                  ·
                    refine ⟨536720788918650571242941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431255437116401523314509 536720788918650571242941)
                    ·
                      rfl

theorem cell22_1567890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1567890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567890 prefixEnd_1567890 := by exact prefixLift 1567890
  have htrace : WordTrace (prefixWord ++ tailWord_1567890) baseStart_1567890 baseEnd_1567890 := by
    simpa [prefixWord, tailWord_1567890, baseEnd_1567890] using wordTrace_append hprefix tailTrace_1567890
  have hstable : (prefixWord ++ tailWord_1567890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567890).length < 2 ^ (prefixWord ++ tailWord_1567890).sum := by decide
  have hdescent : baseEnd_1567890 < baseStart_1567890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567944 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1567944 : Nat := 118140960795 + 1567944 * 2 ^ 59
def prefixEnd_1567944 : Nat := 4983230072969 + 3 ^ 40 * 1567944 * 2
def baseEnd_1567944 : Nat := 536739274222212430392775

theorem tailTrace_1567944 : CollatzResearch.WordTrace tailWord_1567944 prefixEnd_1567944 536739274222212430392775 := by
  unfold tailWord_1567944
  simp only [CollatzResearch.WordTrace]
  refine ⟨28593807915807073180487443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38125077221076097573983257 28593807915807073180487443)
  ·
    refine ⟨42890711873710609770731165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28593807915807073180487443 42890711873710609770731165)
    ·
      refine ⟨16084016952641478664024187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42890711873710609770731165 16084016952641478664024187)
      ·
        refine ⟨24126025428962217996036281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16084016952641478664024187 24126025428962217996036281)
        ·
          refine ⟨18094519071721663497027211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24126025428962217996036281 18094519071721663497027211)
          ·
            refine ⟨27141778607582495245540817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18094519071721663497027211 27141778607582495245540817)
            ·
              refine ⟨20356333955686871434155613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27141778607582495245540817 20356333955686871434155613)
              ·
                refine ⟨7633625233382576787808355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20356333955686871434155613 7633625233382576787808355)
                ·
                  refine ⟨11450437850073865181712533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633625233382576787808355 11450437850073865181712533)
                  ·
                    refine ⟨536739274222212430392775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11450437850073865181712533 536739274222212430392775)
                    ·
                      rfl

theorem cell22_1567944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1567944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567944 prefixEnd_1567944 := by exact prefixLift 1567944
  have htrace : WordTrace (prefixWord ++ tailWord_1567944) baseStart_1567944 baseEnd_1567944 := by
    simpa [prefixWord, tailWord_1567944, baseEnd_1567944] using wordTrace_append hprefix tailTrace_1567944
  have hstable : (prefixWord ++ tailWord_1567944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567944).length < 2 ^ (prefixWord ++ tailWord_1567944).sum := by decide
  have hdescent : baseEnd_1567944 < baseStart_1567944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567946 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1567946 : Nat := 118140960795 + 1567946 * 2 ^ 59
def prefixEnd_1567946 : Nat := 4983230072969 + 3 ^ 40 * 1567946 * 2
def baseEnd_1567946 : Nat := 536739958863085091842769

theorem tailTrace_1567946 : CollatzResearch.WordTrace tailWord_1567946 prefixEnd_1567946 536739958863085091842769 := by
  unfold tailWord_1567946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14296922194401725175636923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38125125851737933801698461 14296922194401725175636923)
  ·
    refine ⟨21445383291602587763455385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14296922194401725175636923 21445383291602587763455385)
    ·
      refine ⟨16084037468701940822591539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21445383291602587763455385 16084037468701940822591539)
      ·
        refine ⟨24126056203052911233887309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16084037468701940822591539 24126056203052911233887309)
        ·
          refine ⟨9047271076144841712707741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24126056203052911233887309 9047271076144841712707741)
          ·
            refine ⟨3392726653554315642265403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9047271076144841712707741 3392726653554315642265403)
            ·
              refine ⟨5089089980331473463398105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392726653554315642265403 5089089980331473463398105)
              ·
                refine ⟨3816817485248605097548579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5089089980331473463398105 3816817485248605097548579)
                ·
                  refine ⟨5725226227872907646322869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816817485248605097548579 5725226227872907646322869)
                  ·
                    refine ⟨536739958863085091842769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5725226227872907646322869 536739958863085091842769)
                    ·
                      rfl

theorem cell22_1567946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1567946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567946 prefixEnd_1567946 := by exact prefixLift 1567946
  have htrace : WordTrace (prefixWord ++ tailWord_1567946) baseStart_1567946 baseEnd_1567946 := by
    simpa [prefixWord, tailWord_1567946, baseEnd_1567946] using wordTrace_append hprefix tailTrace_1567946
  have hstable : (prefixWord ++ tailWord_1567946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567946).length < 2 ^ (prefixWord ++ tailWord_1567946).sum := by decide
  have hdescent : baseEnd_1567946 < baseStart_1567946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567950 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_1567950 : Nat := 118140960795 + 1567950 * 2 ^ 59
def prefixEnd_1567950 : Nat := 4983230072969 + 3 ^ 40 * 1567950 * 2
def baseEnd_1567950 : Nat := 536741328144830414742757

theorem tailTrace_1567950 : CollatzResearch.WordTrace tailWord_1567950 prefixEnd_1567950 536741328144830414742757 := by
  unfold tailWord_1567950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148479333699051173211663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38125223113061606257128869 7148479333699051173211663)
  ·
    refine ⟨10722719000548576759817495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7148479333699051173211663 10722719000548576759817495)
    ·
      refine ⟨16084078500822865139726243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10722719000548576759817495 16084078500822865139726243)
      ·
        refine ⟨24126117751234297709589365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16084078500822865139726243 24126117751234297709589365)
        ·
          refine ⟨2261823539178215410274003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24126117751234297709589365 2261823539178215410274003)
          ·
            refine ⟨3392735308767323115411005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261823539178215410274003 3392735308767323115411005)
            ·
              refine ⟨1272275740787746168279127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3392735308767323115411005 1272275740787746168279127)
              ·
                refine ⟨1908413611181619252418691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272275740787746168279127 1908413611181619252418691)
                ·
                  refine ⟨2862620416772428878628037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908413611181619252418691 2862620416772428878628037)
                  ·
                    refine ⟨536741328144830414742757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2862620416772428878628037 536741328144830414742757)
                    ·
                      rfl

theorem cell22_1567950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_1567950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567950 prefixEnd_1567950 := by exact prefixLift 1567950
  have htrace : WordTrace (prefixWord ++ tailWord_1567950) baseStart_1567950 baseEnd_1567950 := by
    simpa [prefixWord, tailWord_1567950, baseEnd_1567950] using wordTrace_append hprefix tailTrace_1567950
  have hstable : (prefixWord ++ tailWord_1567950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567950).length < 2 ^ (prefixWord ++ tailWord_1567950).sum := by decide
  have hdescent : baseEnd_1567950 < baseStart_1567950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567965 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 4]
def baseStart_1567965 : Nat := 118140960795 + 1567965 * 2 ^ 59
def prefixEnd_1567965 : Nat := 4983230072969 + 3 ^ 40 * 1567965 * 2
def baseEnd_1567965 : Nat := 178915487650458458539237

theorem tailTrace_1567965 : CollatzResearch.WordTrace tailWord_1567965 prefixEnd_1567965 178915487650458458539237 := by
  unfold tailWord_1567965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57188381764538066947489349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38125587843025377964992899 57188381764538066947489349)
  ·
    refine ⟨10722821580850887552654253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57188381764538066947489349 10722821580850887552654253)
    ·
      refine ⟨4021058092819082832245345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10722821580850887552654253 4021058092819082832245345)
      ·
        refine ⟨3015793569614312124184009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4021058092819082832245345 3015793569614312124184009)
        ·
          refine ⟨2261845177210734093138007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3015793569614312124184009 2261845177210734093138007)
          ·
            refine ⟨3392767765816101139707011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261845177210734093138007 3392767765816101139707011)
            ·
              refine ⟨5089151648724151709560517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392767765816101139707011 5089151648724151709560517)
              ·
                refine ⟨954215934135778445542597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5089151648724151709560517 954215934135778445542597)
                ·
                  refine ⟨178915487650458458539237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 954215934135778445542597 178915487650458458539237)
                  ·
                    rfl

theorem cell22_1567965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_1567965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567965 prefixEnd_1567965 := by exact prefixLift 1567965
  have htrace : WordTrace (prefixWord ++ tailWord_1567965) baseStart_1567965 baseEnd_1567965 := by
    simpa [prefixWord, tailWord_1567965, baseEnd_1567965] using wordTrace_append hprefix tailTrace_1567965
  have hstable : (prefixWord ++ tailWord_1567965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567965).length < 2 ^ (prefixWord ++ tailWord_1567965).sum := by decide
  have hdescent : baseEnd_1567965 < baseStart_1567965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567991 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 3, 3]
def baseStart_1567991 : Nat := 118140960795 + 1567991 * 2 ^ 59
def prefixEnd_1567991 : Nat := 4983230072969 + 3 ^ 40 * 1567991 * 2
def baseEnd_1567991 : Nat := 536755363282719974467631

theorem tailTrace_1567991 : CollatzResearch.WordTrace tailWord_1567991 prefixEnd_1567991 536755363282719974467631 := by
  unfold tailWord_1567991
  simp only [CollatzResearch.WordTrace]
  refine ⟨57189330062443873387935827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38126220041629248925290551 57189330062443873387935827)
  ·
    refine ⟨85783995093665810081903741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57189330062443873387935827 85783995093665810081903741)
    ·
      refine ⟨32168998160124678780713903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85783995093665810081903741 32168998160124678780713903)
      ·
        refine ⟨48253497240187018171070855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32168998160124678780713903 48253497240187018171070855)
        ·
          refine ⟨72380245860280527256606283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48253497240187018171070855 72380245860280527256606283)
          ·
            refine ⟨108570368790420790884909425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72380245860280527256606283 108570368790420790884909425)
            ·
              refine ⟨81427776592815593163682069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108570368790420790884909425 81427776592815593163682069)
              ·
                refine ⟨3816927027788230929547597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81427776592815593163682069 3816927027788230929547597)
                ·
                  refine ⟨1431347635420586598580349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3816927027788230929547597 1431347635420586598580349)
                  ·
                    refine ⟨536755363282719974467631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431347635420586598580349 536755363282719974467631)
                    ·
                      rfl

theorem cell22_1567991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_1567991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1567991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1567991 prefixEnd_1567991 := by exact prefixLift 1567991
  have htrace : WordTrace (prefixWord ++ tailWord_1567991) baseStart_1567991 baseEnd_1567991 := by
    simpa [prefixWord, tailWord_1567991, baseEnd_1567991] using wordTrace_append hprefix tailTrace_1567991
  have hstable : (prefixWord ++ tailWord_1567991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567991).length < 2 ^ (prefixWord ++ tailWord_1567991).sum := by decide
  have hdescent : baseEnd_1567991 < baseStart_1567991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568036 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1568036 : Nat := 118140960795 + 1568036 * 2 ^ 59
def prefixEnd_1568036 : Nat := 4983230072969 + 3 ^ 40 * 1568036 * 2
def baseEnd_1568036 : Nat := 536770767702354857092493

theorem tailTrace_1568036 : CollatzResearch.WordTrace tailWord_1568036 prefixEnd_1568036 536770767702354857092493 := by
  unfold tailWord_1568036
  simp only [CollatzResearch.WordTrace]
  refine ⟨28595485673640423036661981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38127314231520564048882641 28595485673640423036661981)
  ·
    refine ⟨10723307127615158638748243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28595485673640423036661981 10723307127615158638748243)
    ·
      refine ⟨16084960691422737958122365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10723307127615158638748243 16084960691422737958122365)
      ·
        refine ⟨6031860259283526734295887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16084960691422737958122365 6031860259283526734295887)
        ·
          refine ⟨9047790388925290101443831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031860259283526734295887 9047790388925290101443831)
          ·
            refine ⟨13571685583387935152165747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9047790388925290101443831 13571685583387935152165747)
            ·
              refine ⟨20357528375081902728248621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13571685583387935152165747 20357528375081902728248621)
              ·
                refine ⟨7634073140655713523093233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20357528375081902728248621 7634073140655713523093233)
                ·
                  refine ⟨5725554855491785142319925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7634073140655713523093233 5725554855491785142319925)
                  ·
                    refine ⟨536770767702354857092493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5725554855491785142319925 536770767702354857092493)
                    ·
                      rfl

theorem cell22_1568036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1568036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568036 prefixEnd_1568036 := by exact prefixLift 1568036
  have htrace : WordTrace (prefixWord ++ tailWord_1568036) baseStart_1568036 baseEnd_1568036 := by
    simpa [prefixWord, tailWord_1568036, baseEnd_1568036] using wordTrace_append hprefix tailTrace_1568036
  have hstable : (prefixWord ++ tailWord_1568036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568036).length < 2 ^ (prefixWord ++ tailWord_1568036).sum := by decide
  have hdescent : baseEnd_1568036 < baseStart_1568036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568098 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1568098 : Nat := 118140960795 + 1568098 * 2 ^ 59
def prefixEnd_1568098 : Nat := 4983230072969 + 3 ^ 40 * 1568098 * 2
def baseEnd_1568098 : Nat := 536791991569407362042303

theorem tailTrace_1568098 : CollatzResearch.WordTrace tailWord_1568098 prefixEnd_1568098 536791991569407362042303 := by
  unfold tailWord_1568098
  simp only [CollatzResearch.WordTrace]
  refine ⟨14298308168264057665520237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38128821782037487108053965 14298308168264057665520237)
  ·
    refine ⟨5361865563099021624570089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14298308168264057665520237 5361865563099021624570089)
    ·
      refine ⟨4021399172324266218427567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5361865563099021624570089 4021399172324266218427567)
      ·
        refine ⟨6032098758486399327641351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021399172324266218427567 6032098758486399327641351)
        ·
          refine ⟨9048148137729598991462027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032098758486399327641351 9048148137729598991462027)
          ·
            refine ⟨13572222206594398487193041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048148137729598991462027 13572222206594398487193041)
            ·
              refine ⟨10179166654945798865394781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13572222206594398487193041 10179166654945798865394781)
              ·
                refine ⟨3817187495604674574523043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10179166654945798865394781 3817187495604674574523043)
                ·
                  refine ⟨5725781243407011861784565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3817187495604674574523043 5725781243407011861784565)
                  ·
                    refine ⟨536791991569407362042303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5725781243407011861784565 536791991569407362042303)
                    ·
                      rfl

theorem cell22_1568098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1568098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568098 prefixEnd_1568098 := by exact prefixLift 1568098
  have htrace : WordTrace (prefixWord ++ tailWord_1568098) baseStart_1568098 baseEnd_1568098 := by
    simpa [prefixWord, tailWord_1568098, baseEnd_1568098] using wordTrace_append hprefix tailTrace_1568098
  have hstable : (prefixWord ++ tailWord_1568098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568098).length < 2 ^ (prefixWord ++ tailWord_1568098).sum := by decide
  have hdescent : baseEnd_1568098 < baseStart_1568098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568177 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 1, 3]
def baseStart_1568177 : Nat := 118140960795 + 1568177 * 2 ^ 59
def prefixEnd_1568177 : Nat := 4983230072969 + 3 ^ 40 * 1568177 * 2
def baseEnd_1568177 : Nat := 536819034883877489317061

theorem tailTrace_1568177 : CollatzResearch.WordTrace tailWord_1568177 prefixEnd_1568177 536819034883877489317061 := by
  unfold tailWord_1568177
  simp only [CollatzResearch.WordTrace]
  refine ⟨57196114039770027154206785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38130742693180018102804523 57196114039770027154206785)
  ·
    refine ⟨42897085529827520365655089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57196114039770027154206785 42897085529827520365655089)
    ·
      refine ⟨32172814147370640274241317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42897085529827520365655089 32172814147370640274241317)
      ·
        refine ⟨6032402652631995051420247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32172814147370640274241317 6032402652631995051420247)
        ·
          refine ⟨9048603978947992577130371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032402652631995051420247 9048603978947992577130371)
          ·
            refine ⟨13572905968421988865695557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048603978947992577130371 13572905968421988865695557)
            ·
              refine ⟨2544919869079122912317917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13572905968421988865695557 2544919869079122912317917)
              ·
                refine ⟨954344950904671092119219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2544919869079122912317917 954344950904671092119219)
                ·
                  refine ⟨1431517426357006638178829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954344950904671092119219 1431517426357006638178829)
                  ·
                    refine ⟨536819034883877489317061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431517426357006638178829 536819034883877489317061)
                    ·
                      rfl

theorem cell22_1568177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_1568177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568177 prefixEnd_1568177 := by exact prefixLift 1568177
  have htrace : WordTrace (prefixWord ++ tailWord_1568177) baseStart_1568177 baseEnd_1568177 := by
    simpa [prefixWord, tailWord_1568177, baseEnd_1568177] using wordTrace_append hprefix tailTrace_1568177
  have hstable : (prefixWord ++ tailWord_1568177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568177).length < 2 ^ (prefixWord ++ tailWord_1568177).sum := by decide
  have hdescent : baseEnd_1568177 < baseStart_1568177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568218 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_1568218 : Nat := 118140960795 + 1568218 * 2 ^ 59
def prefixEnd_1568218 : Nat := 4983230072969 + 3 ^ 40 * 1568218 * 2
def baseEnd_1568218 : Nat := 178944356673922349680645

theorem tailTrace_1568218 : CollatzResearch.WordTrace tailWord_1568218 prefixEnd_1568218 178944356673922349680645 := by
  unfold tailWord_1568218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299402358155372789112327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38131739621747660770966205 14299402358155372789112327)
  ·
    refine ⟨21449103537233059183668491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14299402358155372789112327 21449103537233059183668491)
    ·
      refine ⟨32173655305849588775502737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21449103537233059183668491 32173655305849588775502737)
      ·
        refine ⟨24130241479387191581627053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32173655305849588775502737 24130241479387191581627053)
        ·
          refine ⟨9048840554770196843110145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24130241479387191581627053 9048840554770196843110145)
          ·
            refine ⟨6786630416077647632332609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9048840554770196843110145 6786630416077647632332609)
            ·
              refine ⟨5089972812058235724249457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6786630416077647632332609 5089972812058235724249457)
              ·
                refine ⟨3817479609043676793187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5089972812058235724249457 3817479609043676793187093)
                ·
                  refine ⟨178944356673922349680645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3817479609043676793187093 178944356673922349680645)
                  ·
                    rfl

theorem cell22_1568218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_1568218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568218 prefixEnd_1568218 := by exact prefixLift 1568218
  have htrace : WordTrace (prefixWord ++ tailWord_1568218) baseStart_1568218 baseEnd_1568218 := by
    simpa [prefixWord, tailWord_1568218, baseEnd_1568218] using wordTrace_append hprefix tailTrace_1568218
  have hstable : (prefixWord ++ tailWord_1568218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568218).length < 2 ^ (prefixWord ++ tailWord_1568218).sum := by decide
  have hdescent : baseEnd_1568218 < baseStart_1568218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568248 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_1568248 : Nat := 118140960795 + 1568248 * 2 ^ 59
def prefixEnd_1568248 : Nat := 4983230072969 + 3 ^ 40 * 1568248 * 2
def baseEnd_1568248 : Nat := 536843339634856970791843

theorem tailTrace_1568248 : CollatzResearch.WordTrace tailWord_1568248 prefixEnd_1568248 536843339634856970791843 := by
  unfold tailWord_1568248
  simp only [CollatzResearch.WordTrace]
  refine ⟨28599351811256403140020699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38132469081675204186694265 28599351811256403140020699)
  ·
    refine ⟨42899027716884604710031049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28599351811256403140020699 42899027716884604710031049)
    ·
      refine ⟨32174270787663453532523287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42899027716884604710031049 32174270787663453532523287)
      ·
        refine ⟨48261406181495180298784931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32174270787663453532523287 48261406181495180298784931)
        ·
          refine ⟨72392109272242770448177397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48261406181495180298784931 72392109272242770448177397)
          ·
            refine ⟨6786760244272759729516631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72392109272242770448177397 6786760244272759729516631)
            ·
              refine ⟨10180140366409139594274947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786760244272759729516631 10180140366409139594274947)
              ·
                refine ⟨15270210549613709391412421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10180140366409139594274947 15270210549613709391412421)
                ·
                  refine ⟨2863164478052570510889829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15270210549613709391412421 2863164478052570510889829)
                  ·
                    refine ⟨536843339634856970791843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863164478052570510889829 536843339634856970791843)
                    ·
                      rfl

theorem cell22_1568248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_1568248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568248 prefixEnd_1568248 := by exact prefixLift 1568248
  have htrace : WordTrace (prefixWord ++ tailWord_1568248) baseStart_1568248 baseEnd_1568248 := by
    simpa [prefixWord, tailWord_1568248, baseEnd_1568248] using wordTrace_append hprefix tailTrace_1568248
  have hstable : (prefixWord ++ tailWord_1568248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568248).length < 2 ^ (prefixWord ++ tailWord_1568248).sum := by decide
  have hdescent : baseEnd_1568248 < baseStart_1568248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568250 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_1568250 : Nat := 118140960795 + 1568250 * 2 ^ 59
def prefixEnd_1568250 : Nat := 4983230072969 + 3 ^ 40 * 1568250 * 2
def baseEnd_1568250 : Nat := 536844024275729632241837

theorem tailTrace_1568250 : CollatzResearch.WordTrace tailWord_1568250 prefixEnd_1568250 536844024275729632241837 := by
  unfold tailWord_1568250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299694142126390155403551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38132517712337040414409469 14299694142126390155403551)
  ·
    refine ⟨21449541213189585233105327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14299694142126390155403551 21449541213189585233105327)
    ·
      refine ⟨32174311819784377849657991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21449541213189585233105327 32174311819784377849657991)
      ·
        refine ⟨48261467729676566774486987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32174311819784377849657991 48261467729676566774486987)
        ·
          refine ⟨72392201594514850161730481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48261467729676566774486987 72392201594514850161730481)
          ·
            refine ⟨54294151195886137621297861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72392201594514850161730481 54294151195886137621297861)
            ·
              refine ⟨10180153349228650803993349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54294151195886137621297861 10180153349228650803993349)
              ·
                refine ⟨1908778752980372025748753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10180153349228650803993349 1908778752980372025748753)
                ·
                  refine ⟨1431584064735279019311565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908778752980372025748753 1431584064735279019311565)
                  ·
                    refine ⟨536844024275729632241837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431584064735279019311565 536844024275729632241837)
                    ·
                      rfl

theorem cell22_1568250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_1568250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568250 prefixEnd_1568250 := by exact prefixLift 1568250
  have htrace : WordTrace (prefixWord ++ tailWord_1568250) baseStart_1568250 baseEnd_1568250 := by
    simpa [prefixWord, tailWord_1568250, baseEnd_1568250] using wordTrace_append hprefix tailTrace_1568250
  have hstable : (prefixWord ++ tailWord_1568250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568250).length < 2 ^ (prefixWord ++ tailWord_1568250).sum := by decide
  have hdescent : baseEnd_1568250 < baseStart_1568250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568263 : List Nat := [1, 1, 4, 3, 2, 1, 1, 9]
def baseStart_1568263 : Nat := 118140960795 + 1568263 * 2 ^ 59
def prefixEnd_1568263 : Nat := 4983230072969 + 3 ^ 40 * 1568263 * 2
def baseEnd_1568263 : Nat := 59649830493489103518533

theorem tailTrace_1568263 : CollatzResearch.WordTrace tailWord_1568263 prefixEnd_1568263 59649830493489103518533 := by
  unfold tailWord_1568263
  simp only [CollatzResearch.WordTrace]
  refine ⟨57199250717458463841837443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38132833811638975894558295 57199250717458463841837443)
  ·
    refine ⟨85798876076187695762756165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57199250717458463841837443 85798876076187695762756165)
    ·
      refine ⟨16087289264285192955516781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85798876076187695762756165 16087289264285192955516781)
      ·
        refine ⟨6032733474106947358318793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16087289264285192955516781 6032733474106947358318793)
        ·
          refine ⟨4524550105580210518739095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6032733474106947358318793 4524550105580210518739095)
          ·
            refine ⟨6786825158370315778108643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524550105580210518739095 6786825158370315778108643)
            ·
              refine ⟨10180237737555473667162965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786825158370315778108643 10180237737555473667162965)
              ·
                refine ⟨59649830493489103518533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10180237737555473667162965 59649830493489103518533)
                ·
                  rfl

theorem cell22_1568263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 9].length) (baseStart_1568263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568263 prefixEnd_1568263 := by exact prefixLift 1568263
  have htrace : WordTrace (prefixWord ++ tailWord_1568263) baseStart_1568263 baseEnd_1568263 := by
    simpa [prefixWord, tailWord_1568263, baseEnd_1568263] using wordTrace_append hprefix tailTrace_1568263
  have hstable : (prefixWord ++ tailWord_1568263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568263).length < 2 ^ (prefixWord ++ tailWord_1568263).sum := by decide
  have hdescent : baseEnd_1568263 < baseStart_1568263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568267 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 2, 3]
def baseStart_1568267 : Nat := 118140960795 + 1568267 * 2 ^ 59
def prefixEnd_1568267 : Nat := 4983230072969 + 3 ^ 40 * 1568267 * 2
def baseEnd_1568267 : Nat := 536849843723147254566785

theorem tailTrace_1568267 : CollatzResearch.WordTrace tailWord_1568267 prefixEnd_1568267 536849843723147254566785 := by
  unfold tailWord_1568267
  simp only [CollatzResearch.WordTrace]
  refine ⟨57199396609443972524983055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38132931072962648349988703 57199396609443972524983055)
  ·
    refine ⟨85799094914165958787474583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57199396609443972524983055 85799094914165958787474583)
    ·
      refine ⟨128698642371248938181211875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85799094914165958787474583 128698642371248938181211875)
      ·
        refine ⟨193047963556873407271817813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128698642371248938181211875 193047963556873407271817813)
        ·
          refine ⟨2262280822932110241466615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 193047963556873407271817813 2262280822932110241466615)
          ·
            refine ⟨3393421234398165362199923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262280822932110241466615 3393421234398165362199923)
            ·
              refine ⟨5090131851597248043299885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393421234398165362199923 5090131851597248043299885)
              ·
                refine ⟨1908799444348968016237457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5090131851597248043299885 1908799444348968016237457)
                ·
                  refine ⟨1431599583261726012178093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908799444348968016237457 1431599583261726012178093)
                  ·
                    refine ⟨536849843723147254566785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431599583261726012178093 536849843723147254566785)
                    ·
                      rfl

theorem cell22_1568267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 3].length) (baseStart_1568267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568267 prefixEnd_1568267 := by exact prefixLift 1568267
  have htrace : WordTrace (prefixWord ++ tailWord_1568267) baseStart_1568267 baseEnd_1568267 := by
    simpa [prefixWord, tailWord_1568267, baseEnd_1568267] using wordTrace_append hprefix tailTrace_1568267
  have hstable : (prefixWord ++ tailWord_1568267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568267).length < 2 ^ (prefixWord ++ tailWord_1568267).sum := by decide
  have hdescent : baseEnd_1568267 < baseStart_1568267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568353 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 8]
def baseStart_1568353 : Nat := 118140960795 + 1568353 * 2 ^ 59
def prefixEnd_1568353 : Nat := 4983230072969 + 3 ^ 40 * 1568353 * 2
def baseEnd_1568353 : Nat := 178959761093557232305507

theorem tailTrace_1568353 : CollatzResearch.WordTrace tailWord_1568353 prefixEnd_1568353 178959761093557232305507 := by
  unfold tailWord_1568353
  simp only [CollatzResearch.WordTrace]
  refine ⟨57202533287132409212613713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38135022191421606141742475 57202533287132409212613713)
  ·
    refine ⟨42901899965349306909460285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57202533287132409212613713 42901899965349306909460285)
    ·
      refine ⟨16088212487005990091047607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42901899965349306909460285 16088212487005990091047607)
      ·
        refine ⟨24132318730508985136571411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16088212487005990091047607 24132318730508985136571411)
        ·
          refine ⟨36198478095763477704857117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24132318730508985136571411 36198478095763477704857117)
          ·
            refine ⟨13574429285911304139321419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36198478095763477704857117 13574429285911304139321419)
            ·
              refine ⟨20361643928866956208982129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13574429285911304139321419 20361643928866956208982129)
              ·
                refine ⟨15271232946650217156736597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20361643928866956208982129 15271232946650217156736597)
                ·
                  refine ⟨178959761093557232305507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15271232946650217156736597 178959761093557232305507)
                  ·
                    rfl

theorem cell22_1568353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_1568353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568353 prefixEnd_1568353 := by exact prefixLift 1568353
  have htrace : WordTrace (prefixWord ++ tailWord_1568353) baseStart_1568353 baseEnd_1568353 := by
    simpa [prefixWord, tailWord_1568353, baseEnd_1568353] using wordTrace_append hprefix tailTrace_1568353
  have hstable : (prefixWord ++ tailWord_1568353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568353).length < 2 ^ (prefixWord ++ tailWord_1568353).sum := by decide
  have hdescent : baseEnd_1568353 < baseStart_1568353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568370 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1568370 : Nat := 118140960795 + 1568370 * 2 ^ 59
def prefixEnd_1568370 : Nat := 4983230072969 + 3 ^ 40 * 1568370 * 2
def baseEnd_1568370 : Nat := 178961700909363106413823

theorem tailTrace_1568370 : CollatzResearch.WordTrace tailWord_1568370 prefixEnd_1568370 178961700909363106413823 := by
  unfold tailWord_1568370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14300788332017705278995641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38135435552047214077321709 14300788332017705278995641)
  ·
    refine ⟨10725591249013278959246731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14300788332017705278995641 10725591249013278959246731)
    ·
      refine ⟨16088386873519918438870097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10725591249013278959246731 16088386873519918438870097)
      ·
        refine ⟨12066290155139938829152573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16088386873519918438870097 12066290155139938829152573)
        ·
          refine ⟨4524858808177477060932215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12066290155139938829152573 4524858808177477060932215)
          ·
            refine ⟨6787288212266215591398323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524858808177477060932215 6787288212266215591398323)
            ·
              refine ⟨10180932318399323387097485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787288212266215591398323 10180932318399323387097485)
              ·
                refine ⟨3817849619399746270161557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10180932318399323387097485 3817849619399746270161557)
                ·
                  refine ⟨178961700909363106413823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3817849619399746270161557 178961700909363106413823)
                  ·
                    rfl

theorem cell22_1568370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1568370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568370 prefixEnd_1568370 := by exact prefixLift 1568370
  have htrace : WordTrace (prefixWord ++ tailWord_1568370) baseStart_1568370 baseEnd_1568370 := by
    simpa [prefixWord, tailWord_1568370, baseEnd_1568370] using wordTrace_append hprefix tailTrace_1568370
  have hstable : (prefixWord ++ tailWord_1568370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568370).length < 2 ^ (prefixWord ++ tailWord_1568370).sum := by decide
  have hdescent : baseEnd_1568370 < baseStart_1568370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568417 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1568417 : Nat := 118140960795 + 1568417 * 2 ^ 59
def prefixEnd_1568417 : Nat := 4983230072969 + 3 ^ 40 * 1568417 * 2
def baseEnd_1568417 : Nat := 536901191788596863316325

theorem tailTrace_1568417 : CollatzResearch.WordTrace tailWord_1568417 prefixEnd_1568417 536901191788596863316325 := by
  unfold tailWord_1568417
  simp only [CollatzResearch.WordTrace]
  refine ⟨57204867558900548142943505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38136578372600365428629003 57204867558900548142943505)
  ·
    refine ⟨42903650669175411107207629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57204867558900548142943505 42903650669175411107207629)
    ·
      refine ⟨16088869000940779165202861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42903650669175411107207629 16088869000940779165202861)
      ·
        refine ⟨6033325875352792186951073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16088869000940779165202861 6033325875352792186951073)
        ·
          refine ⟨4524994406514594140213305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6033325875352792186951073 4524994406514594140213305)
          ·
            refine ⟨3393745804885945605159979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524994406514594140213305 3393745804885945605159979)
            ·
              refine ⟨5090618707328918407739969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393745804885945605159979 5090618707328918407739969)
              ·
                refine ⟨3817964030496688805804977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5090618707328918407739969 3817964030496688805804977)
                ·
                  refine ⟨2863473022872516604353733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3817964030496688805804977 2863473022872516604353733)
                  ·
                    refine ⟨536901191788596863316325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863473022872516604353733 536901191788596863316325)
                    ·
                      rfl

theorem cell22_1568417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1568417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568417 prefixEnd_1568417 := by exact prefixLift 1568417
  have htrace : WordTrace (prefixWord ++ tailWord_1568417) baseStart_1568417 baseEnd_1568417 := by
    simpa [prefixWord, tailWord_1568417, baseEnd_1568417] using wordTrace_append hprefix tailTrace_1568417
  have hstable : (prefixWord ++ tailWord_1568417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568417).length < 2 ^ (prefixWord ++ tailWord_1568417).sum := by decide
  have hdescent : baseEnd_1568417 < baseStart_1568417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568481 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1568481 : Nat := 118140960795 + 1568481 * 2 ^ 59
def prefixEnd_1568481 : Nat := 4983230072969 + 3 ^ 40 * 1568481 * 2
def baseEnd_1568481 : Nat := 536923100296522029716129

theorem tailTrace_1568481 : CollatzResearch.WordTrace tailWord_1568481 prefixEnd_1568481 536923100296522029716129 := by
  unfold tailWord_1568481
  simp only [CollatzResearch.WordTrace]
  refine ⟨57207201830668687073273297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38138134553779124715515531 57207201830668687073273297)
  ·
    refine ⟨42905401373001515304954973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57207201830668687073273297 42905401373001515304954973)
    ·
      refine ⟨16089525514875568239358115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42905401373001515304954973 16089525514875568239358115)
      ·
        refine ⟨24134288272313352359037173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16089525514875568239358115 24134288272313352359037173)
        ·
          refine ⟨2262589525529376783659735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24134288272313352359037173 2262589525529376783659735)
          ·
            refine ⟨3393884288294065175489603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262589525529376783659735 3393884288294065175489603)
            ·
              refine ⟨5090826432441097763234405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393884288294065175489603 5090826432441097763234405)
              ·
                refine ⟨954529956082705830606451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5090826432441097763234405 954529956082705830606451)
                ·
                  refine ⟨1431794934124058745909677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954529956082705830606451 1431794934124058745909677)
                  ·
                    refine ⟨536923100296522029716129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431794934124058745909677 536923100296522029716129)
                    ·
                      rfl

theorem cell22_1568481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1568481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568481 prefixEnd_1568481 := by exact prefixLift 1568481
  have htrace : WordTrace (prefixWord ++ tailWord_1568481) baseStart_1568481 baseEnd_1568481 := by
    simpa [prefixWord, tailWord_1568481, baseEnd_1568481] using wordTrace_append hprefix tailTrace_1568481
  have hstable : (prefixWord ++ tailWord_1568481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568481).length < 2 ^ (prefixWord ++ tailWord_1568481).sum := by decide
  have hdescent : baseEnd_1568481 < baseStart_1568481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568524 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_1568524 : Nat := 118140960795 + 1568524 * 2 ^ 59
def prefixEnd_1568524 : Nat := 4983230072969 + 3 ^ 40 * 1568524 * 2
def baseEnd_1568524 : Nat := 536937820075284250890997

theorem tailTrace_1568524 : CollatzResearch.WordTrace tailWord_1568524 prefixEnd_1568524 536937820075284250890997 := by
  unfold tailWord_1568524
  simp only [CollatzResearch.WordTrace]
  refine ⟨28604385084756452708544313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38139180113008603611392417 28604385084756452708544313)
  ·
    refine ⟨21453288813567339531408235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28604385084756452708544313 21453288813567339531408235)
    ·
      refine ⟨32179933220351009297112353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21453288813567339531408235 32179933220351009297112353)
      ·
        refine ⟨24134949915263256972834265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32179933220351009297112353 24134949915263256972834265)
        ·
          refine ⟨18101212436447442729625699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24134949915263256972834265 18101212436447442729625699)
          ·
            refine ⟨27151818654671164094438549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18101212436447442729625699 27151818654671164094438549)
            ·
              refine ⟨1272741499437710816926807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27151818654671164094438549 1272741499437710816926807)
              ·
                refine ⟨1909112249156566225390211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272741499437710816926807 1909112249156566225390211)
                ·
                  refine ⟨2863668373734849338085317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909112249156566225390211 2863668373734849338085317)
                  ·
                    refine ⟨536937820075284250890997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863668373734849338085317 536937820075284250890997)
                    ·
                      rfl

theorem cell22_1568524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_1568524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568524 prefixEnd_1568524 := by exact prefixLift 1568524
  have htrace : WordTrace (prefixWord ++ tailWord_1568524) baseStart_1568524 baseEnd_1568524 := by
    simpa [prefixWord, tailWord_1568524, baseEnd_1568524] using wordTrace_append hprefix tailTrace_1568524
  have hstable : (prefixWord ++ tailWord_1568524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568524).length < 2 ^ (prefixWord ++ tailWord_1568524).sum := by decide
  have hdescent : baseEnd_1568524 < baseStart_1568524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568552 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1568552 : Nat := 118140960795 + 1568552 * 2 ^ 59
def prefixEnd_1568552 : Nat := 4983230072969 + 3 ^ 40 * 1568552 * 2
def baseEnd_1568552 : Nat := 536947405047501511190911

theorem tailTrace_1568552 : CollatzResearch.WordTrace tailWord_1568552 prefixEnd_1568552 536947405047501511190911 := by
  unfold tailWord_1568552
  simp only [CollatzResearch.WordTrace]
  refine ⟨28604895706705733099553955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38139860942274310799405273 28604895706705733099553955)
  ·
    refine ⟨42907343560058599649330933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28604895706705733099553955 42907343560058599649330933)
    ·
      refine ⟨4022563458755493717124775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42907343560058599649330933 4022563458755493717124775)
      ·
        refine ⟨6033845188133240575687163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4022563458755493717124775 6033845188133240575687163)
        ·
          refine ⟨9050767782199860863530745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033845188133240575687163 9050767782199860863530745)
          ·
            refine ⟨6788075836649895647648059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9050767782199860863530745 6788075836649895647648059)
            ·
              refine ⟨10182113754974843471472089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788075836649895647648059 10182113754974843471472089)
              ·
                refine ⟨7636585316231132603604067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10182113754974843471472089 7636585316231132603604067)
                ·
                  refine ⟨11454877974346698905406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7636585316231132603604067 11454877974346698905406101)
                  ·
                    refine ⟨536947405047501511190911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11454877974346698905406101 536947405047501511190911)
                    ·
                      rfl

theorem cell22_1568552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1568552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568552 prefixEnd_1568552 := by exact prefixLift 1568552
  have htrace : WordTrace (prefixWord ++ tailWord_1568552) baseStart_1568552 baseEnd_1568552 := by
    simpa [prefixWord, tailWord_1568552, baseEnd_1568552] using wordTrace_append hprefix tailTrace_1568552
  have hstable : (prefixWord ++ tailWord_1568552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568552).length < 2 ^ (prefixWord ++ tailWord_1568552).sum := by decide
  have hdescent : baseEnd_1568552 < baseStart_1568552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568687 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 1, 6]
def baseStart_1568687 : Nat := 118140960795 + 1568687 * 2 ^ 59
def prefixEnd_1568687 : Nat := 4983230072969 + 3 ^ 40 * 1568687 * 2
def baseEnd_1568687 : Nat := 536993618306406159065497

theorem tailTrace_1568687 : CollatzResearch.WordTrace tailWord_1568687 prefixEnd_1568687 536993618306406159065497 := by
  unfold tailWord_1568687
  simp only [CollatzResearch.WordTrace]
  refine ⟨57214715267922384255272315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38143143511948256170181543 57214715267922384255272315)
  ·
    refine ⟨85822072901883576382908473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57214715267922384255272315 85822072901883576382908473)
    ·
      refine ⟨64366554676412682287181355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85822072901883576382908473 64366554676412682287181355)
      ·
        refine ⟨96549832014619023430772033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64366554676412682287181355 96549832014619023430772033)
        ·
          refine ⟨72412374010964267573079025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96549832014619023430772033 72412374010964267573079025)
          ·
            refine ⟨54309280508223200679809269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72412374010964267573079025 54309280508223200679809269)
            ·
              refine ⟨5091495047645925063732119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54309280508223200679809269 5091495047645925063732119)
              ·
                refine ⟨7637242571468887595598179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091495047645925063732119 7637242571468887595598179)
                ·
                  refine ⟨11455863857203331393397269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7637242571468887595598179 11455863857203331393397269)
                  ·
                    refine ⟨536993618306406159065497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11455863857203331393397269 536993618306406159065497)
                    ·
                      rfl

theorem cell22_1568687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_1568687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568687 prefixEnd_1568687 := by exact prefixLift 1568687
  have htrace : WordTrace (prefixWord ++ tailWord_1568687) baseStart_1568687 baseEnd_1568687 := by
    simpa [prefixWord, tailWord_1568687, baseEnd_1568687] using wordTrace_append hprefix tailTrace_1568687
  have hstable : (prefixWord ++ tailWord_1568687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568687).length < 2 ^ (prefixWord ++ tailWord_1568687).sum := by decide
  have hdescent : baseEnd_1568687 < baseStart_1568687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568689 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_1568689 : Nat := 118140960795 + 1568689 * 2 ^ 59
def prefixEnd_1568689 : Nat := 4983230072969 + 3 ^ 40 * 1568689 * 2
def baseEnd_1568689 : Nat := 536994302947278820515491

theorem tailTrace_1568689 : CollatzResearch.WordTrace tailWord_1568689 prefixEnd_1568689 536994302947278820515491 := by
  unfold tailWord_1568689
  simp only [CollatzResearch.WordTrace]
  refine ⟨57214788213915138596845121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38143192142610092397896747 57214788213915138596845121)
  ·
    refine ⟨42911091160436353947633841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57214788213915138596845121 42911091160436353947633841)
    ·
      refine ⟨32183318370327265460725381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42911091160436353947633841 32183318370327265460725381)
      ·
        refine ⟨6034372194436362273886009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32183318370327265460725381 6034372194436362273886009)
        ·
          refine ⟨4525779145827271705414507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6034372194436362273886009 4525779145827271705414507)
          ·
            refine ⟨6788668718740907558121761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4525779145827271705414507 6788668718740907558121761)
            ·
              refine ⟨5091501539055680668591321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6788668718740907558121761 5091501539055680668591321)
              ·
                refine ⟨3818626154291760501443491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091501539055680668591321 3818626154291760501443491)
                ·
                  refine ⟨5727939231437640752165237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818626154291760501443491 5727939231437640752165237)
                  ·
                    refine ⟨536994302947278820515491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5727939231437640752165237 536994302947278820515491)
                    ·
                      rfl

theorem cell22_1568689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_1568689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568689 prefixEnd_1568689 := by exact prefixLift 1568689
  have htrace : WordTrace (prefixWord ++ tailWord_1568689) baseStart_1568689 baseEnd_1568689 := by
    simpa [prefixWord, tailWord_1568689, baseEnd_1568689] using wordTrace_append hprefix tailTrace_1568689
  have hstable : (prefixWord ++ tailWord_1568689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568689).length < 2 ^ (prefixWord ++ tailWord_1568689).sum := by decide
  have hdescent : baseEnd_1568689 < baseStart_1568689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568693 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1568693 : Nat := 118140960795 + 1568693 * 2 ^ 59
def prefixEnd_1568693 : Nat := 4983230072969 + 3 ^ 40 * 1568693 * 2
def baseEnd_1568693 : Nat := 536995672229024143415479

theorem tailTrace_1568693 : CollatzResearch.WordTrace tailWord_1568693 prefixEnd_1568693 536995672229024143415479 := by
  unfold tailWord_1568693
  simp only [CollatzResearch.WordTrace]
  refine ⟨57214934105900647279990733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38143289403933764853327155 57214934105900647279990733)
  ·
    refine ⟨21455600289712742729996525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57214934105900647279990733 21455600289712742729996525)
    ·
      refine ⟨8045850108642278523748697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21455600289712742729996525 8045850108642278523748697)
      ·
        refine ⟨6034387581481708892811523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045850108642278523748697 6034387581481708892811523)
        ·
          refine ⟨9051581372222563339217285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034387581481708892811523 9051581372222563339217285)
          ·
            refine ⟨1697171507291730626103241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9051581372222563339217285 1697171507291730626103241)
            ·
              refine ⟨1272878630468797969577431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697171507291730626103241 1272878630468797969577431)
              ·
                refine ⟨1909317945703196954366147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272878630468797969577431 1909317945703196954366147)
                ·
                  refine ⟨2863976918554795431549221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909317945703196954366147 2863976918554795431549221)
                  ·
                    refine ⟨536995672229024143415479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863976918554795431549221 536995672229024143415479)
                    ·
                      rfl

theorem cell22_1568693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1568693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568693 prefixEnd_1568693 := by exact prefixLift 1568693
  have htrace : WordTrace (prefixWord ++ tailWord_1568693) baseStart_1568693 baseEnd_1568693 := by
    simpa [prefixWord, tailWord_1568693, baseEnd_1568693] using wordTrace_append hprefix tailTrace_1568693
  have hstable : (prefixWord ++ tailWord_1568693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568693).length < 2 ^ (prefixWord ++ tailWord_1568693).sum := by decide
  have hdescent : baseEnd_1568693 < baseStart_1568693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568764 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_1568764 : Nat := 118140960795 + 1568764 * 2 ^ 59
def prefixEnd_1568764 : Nat := 4983230072969 + 3 ^ 40 * 1568764 * 2
def baseEnd_1568764 : Nat := 179006658993334541630087

theorem tailTrace_1568764 : CollatzResearch.WordTrace tailWord_1568764 prefixEnd_1568764 179006658993334541630087 := by
  unfold tailWord_1568764
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608761844321713202912673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38145015792428950937216897 28608761844321713202912673)
  ·
    refine ⟨21456571383241284902184505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28608761844321713202912673 21456571383241284902184505)
    ·
      refine ⟨16092428537430963676638379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21456571383241284902184505 16092428537430963676638379)
      ·
        refine ⟨24138642806146445514957569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092428537430963676638379 24138642806146445514957569)
        ·
          refine ⟨18103982104609834136218177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24138642806146445514957569 18103982104609834136218177)
          ·
            refine ⟨13577986578457375602163633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18103982104609834136218177 13577986578457375602163633)
            ·
              refine ⟨10183489933843031701622725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13577986578457375602163633 10183489933843031701622725)
              ·
                refine ⟨1909404362595568444054261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10183489933843031701622725 1909404362595568444054261)
                ·
                  refine ⟨179006658993334541630087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1909404362595568444054261 179006658993334541630087)
                  ·
                    rfl

theorem cell22_1568764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_1568764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568764 prefixEnd_1568764 := by exact prefixLift 1568764
  have htrace : WordTrace (prefixWord ++ tailWord_1568764) baseStart_1568764 baseEnd_1568764 := by
    simpa [prefixWord, tailWord_1568764, baseEnd_1568764] using wordTrace_append hprefix tailTrace_1568764
  have hstable : (prefixWord ++ tailWord_1568764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568764).length < 2 ^ (prefixWord ++ tailWord_1568764).sum := by decide
  have hdescent : baseEnd_1568764 < baseStart_1568764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568774 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1568774 : Nat := 118140960795 + 1568774 * 2 ^ 59
def prefixEnd_1568774 : Nat := 4983230072969 + 3 ^ 40 * 1568774 * 2
def baseEnd_1568774 : Nat := 537023400184366932140231

theorem tailTrace_1568774 : CollatzResearch.WordTrace tailWord_1568774 prefixEnd_1568774 537023400184366932140231 := by
  unfold tailWord_1568774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788059013081474941052793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38145258945738132075792917 1788059013081474941052793)
  ·
    refine ⟨1341044259811106205789595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1788059013081474941052793 1341044259811106205789595)
    ·
      refine ⟨2011566389716659308684393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341044259811106205789595 2011566389716659308684393)
      ·
        refine ⟨1508674792287494481513295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2011566389716659308684393 1508674792287494481513295)
        ·
          refine ⟨2263012188431241722269943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508674792287494481513295 2263012188431241722269943)
          ·
            refine ⟨3394518282646862583404915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263012188431241722269943 3394518282646862583404915)
            ·
              refine ⟨5091777423970293875107373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394518282646862583404915 5091777423970293875107373)
              ·
                refine ⟨1909416533988860203165265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5091777423970293875107373 1909416533988860203165265)
                ·
                  refine ⟨1432062400491645152373949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1909416533988860203165265 1432062400491645152373949)
                  ·
                    refine ⟨537023400184366932140231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432062400491645152373949 537023400184366932140231)
                    ·
                      rfl

theorem cell22_1568774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1568774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568774 prefixEnd_1568774 := by exact prefixLift 1568774
  have htrace : WordTrace (prefixWord ++ tailWord_1568774) baseStart_1568774 baseEnd_1568774 := by
    simpa [prefixWord, tailWord_1568774, baseEnd_1568774] using wordTrace_append hprefix tailTrace_1568774
  have hstable : (prefixWord ++ tailWord_1568774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568774).length < 2 ^ (prefixWord ++ tailWord_1568774).sum := by decide
  have hdescent : baseEnd_1568774 < baseStart_1568774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568777 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_1568777 : Nat := 118140960795 + 1568777 * 2 ^ 59
def prefixEnd_1568777 : Nat := 4983230072969 + 3 ^ 40 * 1568777 * 2
def baseEnd_1568777 : Nat := 537024427145675924315221

theorem tailTrace_1568777 : CollatzResearch.WordTrace tailWord_1568777 prefixEnd_1568777 537024427145675924315221 := by
  unfold tailWord_1568777
  simp only [CollatzResearch.WordTrace]
  refine ⟨57217997837596329626048585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38145331891730886417365723 57217997837596329626048585)
  ·
    refine ⟨42913498378197247219536439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57217997837596329626048585 42913498378197247219536439)
    ·
      refine ⟨64370247567295870829304659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42913498378197247219536439 64370247567295870829304659)
      ·
        refine ⟨96555371350943806243956989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64370247567295870829304659 96555371350943806243956989)
        ·
          refine ⟨36208264256603927341483871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96555371350943806243956989 36208264256603927341483871)
          ·
            refine ⟨54312396384905891012225807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36208264256603927341483871 54312396384905891012225807)
            ·
              refine ⟨81468594577358836518338711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54312396384905891012225807 81468594577358836518338711)
              ·
                refine ⟨122202891866038254777508067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81468594577358836518338711 122202891866038254777508067)
                ·
                  refine ⟨183304337799057382166262101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122202891866038254777508067 183304337799057382166262101)
                  ·
                    refine ⟨537024427145675924315221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 183304337799057382166262101 537024427145675924315221)
                    ·
                      rfl

theorem cell22_1568777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_1568777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568777 prefixEnd_1568777 := by exact prefixLift 1568777
  have htrace : WordTrace (prefixWord ++ tailWord_1568777) baseStart_1568777 baseEnd_1568777 := by
    simpa [prefixWord, tailWord_1568777, baseEnd_1568777] using wordTrace_append hprefix tailTrace_1568777
  have hstable : (prefixWord ++ tailWord_1568777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568777).length < 2 ^ (prefixWord ++ tailWord_1568777).sum := by decide
  have hdescent : baseEnd_1568777 < baseStart_1568777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568839 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1568839 : Nat := 118140960795 + 1568839 * 2 ^ 59
def prefixEnd_1568839 : Nat := 4983230072969 + 3 ^ 40 * 1568839 * 2
def baseEnd_1568839 : Nat := 537045651012728429265031

theorem tailTrace_1568839 : CollatzResearch.WordTrace tailWord_1568839 prefixEnd_1568839 537045651012728429265031 := by
  unfold tailWord_1568839
  simp only [CollatzResearch.WordTrace]
  refine ⟨57220259163371714214805571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38146839442247809476537047 57220259163371714214805571)
  ·
    refine ⟨85830388745057571322208357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57220259163371714214805571 85830388745057571322208357)
    ·
      refine ⟨16093197889698294622914067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85830388745057571322208357 16093197889698294622914067)
      ·
        refine ⟨24139796834547441934371101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16093197889698294622914067 24139796834547441934371101)
        ·
          refine ⟨9052423812955290725389163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24139796834547441934371101 9052423812955290725389163)
          ·
            refine ⟨13578635719432936088083745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052423812955290725389163 13578635719432936088083745)
            ·
              refine ⟨10183976789574702066062809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13578635719432936088083745 10183976789574702066062809)
              ·
                refine ⟨7637982592181026549547107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183976789574702066062809 7637982592181026549547107)
                ·
                  refine ⟨11456973888271539824320661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7637982592181026549547107 11456973888271539824320661)
                  ·
                    refine ⟨537045651012728429265031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11456973888271539824320661 537045651012728429265031)
                    ·
                      rfl

theorem cell22_1568839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1568839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568839 prefixEnd_1568839 := by exact prefixLift 1568839
  have htrace : WordTrace (prefixWord ++ tailWord_1568839) baseStart_1568839 baseEnd_1568839 := by
    simpa [prefixWord, tailWord_1568839, baseEnd_1568839] using wordTrace_append hprefix tailTrace_1568839
  have hstable : (prefixWord ++ tailWord_1568839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568839).length < 2 ^ (prefixWord ++ tailWord_1568839).sum := by decide
  have hdescent : baseEnd_1568839 < baseStart_1568839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568841 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_1568841 : Nat := 118140960795 + 1568841 * 2 ^ 59
def prefixEnd_1568841 : Nat := 4983230072969 + 3 ^ 40 * 1568841 * 2
def baseEnd_1568841 : Nat := 537046335653601090715025

theorem tailTrace_1568841 : CollatzResearch.WordTrace tailWord_1568841 prefixEnd_1568841 537046335653601090715025 := by
  unfold tailWord_1568841
  simp only [CollatzResearch.WordTrace]
  refine ⟨57220332109364468556378377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38146888072909645704252251 57220332109364468556378377)
  ·
    refine ⟨42915249082023351417283783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57220332109364468556378377 42915249082023351417283783)
    ·
      refine ⟨64372873623035027125925675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42915249082023351417283783 64372873623035027125925675)
      ·
        refine ⟨96559310434552540688888513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64372873623035027125925675 96559310434552540688888513)
        ·
          refine ⟨72419482825914405516666385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96559310434552540688888513 72419482825914405516666385)
          ·
            refine ⟨54314612119435804137499789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72419482825914405516666385 54314612119435804137499789)
            ·
              refine ⟨20367979544788426551562421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54314612119435804137499789 20367979544788426551562421)
              ·
                refine ⟨1909498082323914989208977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20367979544788426551562421 1909498082323914989208977)
                ·
                  refine ⟨1432123561742936241906733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1909498082323914989208977 1432123561742936241906733)
                  ·
                    refine ⟨537046335653601090715025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432123561742936241906733 537046335653601090715025)
                    ·
                      rfl

theorem cell22_1568841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_1568841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568841 prefixEnd_1568841 := by exact prefixLift 1568841
  have htrace : WordTrace (prefixWord ++ tailWord_1568841) baseStart_1568841 baseEnd_1568841 := by
    simpa [prefixWord, tailWord_1568841, baseEnd_1568841] using wordTrace_append hprefix tailTrace_1568841
  have hstable : (prefixWord ++ tailWord_1568841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568841).length < 2 ^ (prefixWord ++ tailWord_1568841).sum := by decide
  have hdescent : baseEnd_1568841 < baseStart_1568841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568856 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_1568856 : Nat := 118140960795 + 1568856 * 2 ^ 59
def prefixEnd_1568856 : Nat := 4983230072969 + 3 ^ 40 * 1568856 * 2
def baseEnd_1568856 : Nat := 537051470460146051589979

theorem tailTrace_1568856 : CollatzResearch.WordTrace tailWord_1568856 prefixEnd_1568856 537051470460146051589979 := by
  unfold tailWord_1568856
  simp only [CollatzResearch.WordTrace]
  refine ⟨28610439602155063059087211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38147252802873417412116281 28610439602155063059087211)
  ·
    refine ⟨42915659403232594588630817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28610439602155063059087211 42915659403232594588630817)
    ·
      refine ⟨32186744552424445941473113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42915659403232594588630817 32186744552424445941473113)
      ·
        refine ⟨24140058414318334456104835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32186744552424445941473113 24140058414318334456104835)
        ·
          refine ⟨36210087621477501684157253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24140058414318334456104835 36210087621477501684157253)
          ·
            refine ⟨6789391429027031565779485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36210087621477501684157253 6789391429027031565779485)
            ·
              refine ⟨2546021785885136837167307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6789391429027031565779485 2546021785885136837167307)
              ·
                refine ⟨3819032678827705255750961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546021785885136837167307 3819032678827705255750961)
                ·
                  refine ⟨2864274509120778941813221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819032678827705255750961 2864274509120778941813221)
                  ·
                    refine ⟨537051470460146051589979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864274509120778941813221 537051470460146051589979)
                    ·
                      rfl

theorem cell22_1568856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_1568856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568856 prefixEnd_1568856 := by exact prefixLift 1568856
  have htrace : WordTrace (prefixWord ++ tailWord_1568856) baseStart_1568856 baseEnd_1568856 := by
    simpa [prefixWord, tailWord_1568856, baseEnd_1568856] using wordTrace_append hprefix tailTrace_1568856
  have hstable : (prefixWord ++ tailWord_1568856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568856).length < 2 ^ (prefixWord ++ tailWord_1568856).sum := by decide
  have hdescent : baseEnd_1568856 < baseStart_1568856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568862 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1568862 : Nat := 118140960795 + 1568862 * 2 ^ 59
def prefixEnd_1568862 : Nat := 4983230072969 + 3 ^ 40 * 1568862 * 2
def baseEnd_1568862 : Nat := 537053524382764035939961

theorem tailTrace_1568862 : CollatzResearch.WordTrace tailWord_1568862 prefixEnd_1568862 537053524382764035939961 := by
  unfold tailWord_1568862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152637255286048642861605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38147398694858926095261893 7152637255286048642861605)
  ·
    refine ⟨1341119485366134120536551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7152637255286048642861605 1341119485366134120536551)
    ·
      refine ⟨2011679228049201180804827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341119485366134120536551 2011679228049201180804827)
      ·
        refine ⟨3017518842073801771207241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011679228049201180804827 3017518842073801771207241)
        ·
          refine ⟨2263139131555351328405431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3017518842073801771207241 2263139131555351328405431)
          ·
            refine ⟨3394708697333026992608147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263139131555351328405431 3394708697333026992608147)
            ·
              refine ⟨5092063045999540488912221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394708697333026992608147 5092063045999540488912221)
              ·
                refine ⟨1909523642249827683342083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5092063045999540488912221 1909523642249827683342083)
                ·
                  refine ⟨2864285463374741525013125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909523642249827683342083 2864285463374741525013125)
                  ·
                    refine ⟨537053524382764035939961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864285463374741525013125 537053524382764035939961)
                    ·
                      rfl

theorem cell22_1568862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1568862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568862 prefixEnd_1568862 := by exact prefixLift 1568862
  have htrace : WordTrace (prefixWord ++ tailWord_1568862) baseStart_1568862 baseEnd_1568862 := by
    simpa [prefixWord, tailWord_1568862, baseEnd_1568862] using wordTrace_append hprefix tailTrace_1568862
  have hstable : (prefixWord ++ tailWord_1568862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568862).length < 2 ^ (prefixWord ++ tailWord_1568862).sum := by decide
  have hdescent : baseEnd_1568862 < baseStart_1568862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568946 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1568946 : Nat := 118140960795 + 1568946 * 2 ^ 59
def prefixEnd_1568946 : Nat := 4983230072969 + 3 ^ 40 * 1568946 * 2
def baseEnd_1568946 : Nat := 537082279299415816839703

theorem tailTrace_1568946 : CollatzResearch.WordTrace tailWord_1568946 prefixEnd_1568946 537082279299415816839703 := by
  unfold tailWord_1568946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306040443496017872237673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38149441182656047659300461 14306040443496017872237673)
  ·
    refine ⟨10729530332622013404178255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14306040443496017872237673 10729530332622013404178255)
    ·
      refine ⟨16094295498933020106267383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10729530332622013404178255 16094295498933020106267383)
      ·
        refine ⟨24141443248399530159401075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16094295498933020106267383 24141443248399530159401075)
        ·
          refine ⟨36212164872599295239101613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24141443248399530159401075 36212164872599295239101613)
          ·
            refine ⟨13579561827224735714663105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36212164872599295239101613 13579561827224735714663105)
            ·
              refine ⟨10184671370418551785997329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13579561827224735714663105 10184671370418551785997329)
              ·
                refine ⟨7638503527813913839497997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10184671370418551785997329 7638503527813913839497997)
                ·
                  refine ⟨2864438822930217689811749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7638503527813913839497997 2864438822930217689811749)
                  ·
                    refine ⟨537082279299415816839703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864438822930217689811749 537082279299415816839703)
                    ·
                      rfl

theorem cell22_1568946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1568946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568946 prefixEnd_1568946 := by exact prefixLift 1568946
  have htrace : WordTrace (prefixWord ++ tailWord_1568946) baseStart_1568946 baseEnd_1568946 := by
    simpa [prefixWord, tailWord_1568946, baseEnd_1568946] using wordTrace_append hprefix tailTrace_1568946
  have hstable : (prefixWord ++ tailWord_1568946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568946).length < 2 ^ (prefixWord ++ tailWord_1568946).sum := by decide
  have hdescent : baseEnd_1568946 < baseStart_1568946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568988 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1568988 : Nat := 118140960795 + 1568988 * 2 ^ 59
def prefixEnd_1568988 : Nat := 4983230072969 + 3 ^ 40 * 1568988 * 2
def baseEnd_1568988 : Nat := 537096656757741707289575

theorem tailTrace_1568988 : CollatzResearch.WordTrace tailWord_1568988 prefixEnd_1568988 537096656757741707289575 := by
  unfold tailWord_1568988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28612846819915956330989809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38150462426554608441319745 28612846819915956330989809)
  ·
    refine ⟨21459635114936967248242357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28612846819915956330989809 21459635114936967248242357)
    ·
      refine ⟨2011840792025340679522721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21459635114936967248242357 2011840792025340679522721)
      ·
        refine ⟨1508880594019005509642041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2011840792025340679522721 1508880594019005509642041)
        ·
          refine ⟨1131660445514254132231531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1508880594019005509642041 1131660445514254132231531)
          ·
            refine ⟨1697490668271381198347297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131660445514254132231531 1697490668271381198347297)
            ·
              refine ⟨1273118001203535898760473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697490668271381198347297 1273118001203535898760473)
              ·
                refine ⟨954838500902651924070355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273118001203535898760473 954838500902651924070355)
                ·
                  refine ⟨1432257751353977886105533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954838500902651924070355 1432257751353977886105533)
                  ·
                    refine ⟨537096656757741707289575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432257751353977886105533 537096656757741707289575)
                    ·
                      rfl

theorem cell22_1568988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1568988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1568988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1568988 prefixEnd_1568988 := by exact prefixLift 1568988
  have htrace : WordTrace (prefixWord ++ tailWord_1568988) baseStart_1568988 baseEnd_1568988 := by
    simpa [prefixWord, tailWord_1568988, baseEnd_1568988] using wordTrace_append hprefix tailTrace_1568988
  have hstable : (prefixWord ++ tailWord_1568988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568988).length < 2 ^ (prefixWord ++ tailWord_1568988).sum := by decide
  have hdescent : baseEnd_1568988 < baseStart_1568988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569010 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_1569010 : Nat := 118140960795 + 1569010 * 2 ^ 59
def prefixEnd_1569010 : Nat := 4983230072969 + 3 ^ 40 * 1569010 * 2
def baseEnd_1569010 : Nat := 537104187807340983239507

theorem tailTrace_1569010 : CollatzResearch.WordTrace tailWord_1569010 prefixEnd_1569010 537104187807340983239507 := by
  unfold tailWord_1569010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306624011438052604820121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38150997363834806946186989 14306624011438052604820121)
  ·
    refine ⟨10729968008578539453615091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14306624011438052604820121 10729968008578539453615091)
    ·
      refine ⟨16094952012867809180422637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10729968008578539453615091 16094952012867809180422637)
      ·
        refine ⟨6035607004825428442658489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16094952012867809180422637 6035607004825428442658489)
        ·
          refine ⟨4526705253619071331993867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6035607004825428442658489 4526705253619071331993867)
          ·
            refine ⟨6790057880428606997990801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526705253619071331993867 6790057880428606997990801)
            ·
              refine ⟨5092543410321455248493101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6790057880428606997990801 5092543410321455248493101)
              ·
                refine ⟨1909703778870545718184913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5092543410321455248493101 1909703778870545718184913)
                ·
                  refine ⟨1432277834152909288638685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1909703778870545718184913 1432277834152909288638685)
                  ·
                    refine ⟨537104187807340983239507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432277834152909288638685 537104187807340983239507)
                    ·
                      rfl

theorem cell22_1569010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_1569010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569010 prefixEnd_1569010 := by exact prefixLift 1569010
  have htrace : WordTrace (prefixWord ++ tailWord_1569010) baseStart_1569010 baseEnd_1569010 := by
    simpa [prefixWord, tailWord_1569010, baseEnd_1569010] using wordTrace_append hprefix tailTrace_1569010
  have hstable : (prefixWord ++ tailWord_1569010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569010).length < 2 ^ (prefixWord ++ tailWord_1569010).sum := by decide
  have hdescent : baseEnd_1569010 < baseStart_1569010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569038 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1569038 : Nat := 118140960795 + 1569038 * 2 ^ 59
def prefixEnd_1569038 : Nat := 4983230072969 + 3 ^ 40 * 1569038 * 2
def baseEnd_1569038 : Nat := 537113772779558243539421

theorem tailTrace_1569038 : CollatzResearch.WordTrace tailWord_1569038 prefixEnd_1569038 537113772779558243539421 := by
  unfold tailWord_1569038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153439661206346400162471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38151678193100514134199845 7153439661206346400162471)
  ·
    refine ⟨10730159491809519600243707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7153439661206346400162471 10730159491809519600243707)
    ·
      refine ⟨16095239237714279400365561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10730159491809519600243707 16095239237714279400365561)
      ·
        refine ⟨12071429428285709550274171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16095239237714279400365561 12071429428285709550274171)
        ·
          refine ⟨18107144142428564325411257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12071429428285709550274171 18107144142428564325411257)
          ·
            refine ⟨13580358106821423244058443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18107144142428564325411257 13580358106821423244058443)
            ·
              refine ⟨20370537160232134866087665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13580358106821423244058443 20370537160232134866087665)
              ·
                refine ⟨15277902870174101149565749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20370537160232134866087665 15277902870174101149565749)
                ·
                  refine ⟨1432303394078821982771789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15277902870174101149565749 1432303394078821982771789)
                  ·
                    refine ⟨537113772779558243539421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432303394078821982771789 537113772779558243539421)
                    ·
                      rfl

theorem cell22_1569038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1569038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569038 prefixEnd_1569038 := by exact prefixLift 1569038
  have htrace : WordTrace (prefixWord ++ tailWord_1569038) baseStart_1569038 baseEnd_1569038 := by
    simpa [prefixWord, tailWord_1569038, baseEnd_1569038] using wordTrace_append hprefix tailTrace_1569038
  have hstable : (prefixWord ++ tailWord_1569038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569038).length < 2 ^ (prefixWord ++ tailWord_1569038).sum := by decide
  have hdescent : baseEnd_1569038 < baseStart_1569038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569055 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 3, 3]
def baseStart_1569055 : Nat := 118140960795 + 1569055 * 2 ^ 59
def prefixEnd_1569055 : Nat := 4983230072969 + 3 ^ 40 * 1569055 * 2
def baseEnd_1569055 : Nat := 537119592226975865864369

theorem tailTrace_1569055 : CollatzResearch.WordTrace tailWord_1569055 prefixEnd_1569055 537119592226975865864369 := by
  unfold tailWord_1569055
  simp only [CollatzResearch.WordTrace]
  refine ⟨57228137330589183104668619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38152091553726122069779079 57228137330589183104668619)
  ·
    refine ⟨85842205995883774657002929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57228137330589183104668619 85842205995883774657002929)
    ·
      refine ⟨64381654496912830992752197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85842205995883774657002929 64381654496912830992752197)
      ·
        refine ⟨12071560218171155811141037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64381654496912830992752197 12071560218171155811141037)
        ·
          refine ⟨4526835081814183429177889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12071560218171155811141037 4526835081814183429177889)
          ·
            refine ⟨3395126311360637571883417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4526835081814183429177889 3395126311360637571883417)
            ·
              refine ⟨2546344733520478178912563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395126311360637571883417 2546344733520478178912563)
              ·
                refine ⟨3819517100280717268368845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546344733520478178912563 3819517100280717268368845)
                ·
                  refine ⟨1432318912605268975638317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3819517100280717268368845 1432318912605268975638317)
                  ·
                    refine ⟨537119592226975865864369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432318912605268975638317 537119592226975865864369)
                    ·
                      rfl

theorem cell22_1569055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_1569055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569055 prefixEnd_1569055 := by exact prefixLift 1569055
  have htrace : WordTrace (prefixWord ++ tailWord_1569055) baseStart_1569055 baseEnd_1569055 := by
    simpa [prefixWord, tailWord_1569055, baseEnd_1569055] using wordTrace_append hprefix tailTrace_1569055
  have hstable : (prefixWord ++ tailWord_1569055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569055).length < 2 ^ (prefixWord ++ tailWord_1569055).sum := by decide
  have hdescent : baseEnd_1569055 < baseStart_1569055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569096 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_1569096 : Nat := 118140960795 + 1569096 * 2 ^ 59
def prefixEnd_1569096 : Nat := 4983230072969 + 3 ^ 40 * 1569096 * 2
def baseEnd_1569096 : Nat := 179044542454955141863081

theorem tailTrace_1569096 : CollatzResearch.WordTrace tailWord_1569096 prefixEnd_1569096 179044542454955141863081 := by
  unfold tailWord_1569096
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614816361720323553455571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38153088482293764737940761 28614816361720323553455571)
  ·
    refine ⟨42922224542580485330183357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28614816361720323553455571 42922224542580485330183357)
    ·
      refine ⟨16095834203467681998818759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42922224542580485330183357 16095834203467681998818759)
      ·
        refine ⟨24143751305201522998228139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16095834203467681998818759 24143751305201522998228139)
        ·
          refine ⟨36215626957802284497342209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24143751305201522998228139 36215626957802284497342209)
          ·
            refine ⟨27161720218351713373006657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36215626957802284497342209 27161720218351713373006657)
            ·
              refine ⟨20371290163763785029754993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27161720218351713373006657 20371290163763785029754993)
              ·
                refine ⟨15278467622822838772316245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20371290163763785029754993 15278467622822838772316245)
                ·
                  refine ⟨179044542454955141863081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15278467622822838772316245 179044542454955141863081)
                  ·
                    rfl

theorem cell22_1569096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_1569096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569096 prefixEnd_1569096 := by exact prefixLift 1569096
  have htrace : WordTrace (prefixWord ++ tailWord_1569096) baseStart_1569096 baseEnd_1569096 := by
    simpa [prefixWord, tailWord_1569096, baseEnd_1569096] using wordTrace_append hprefix tailTrace_1569096
  have hstable : (prefixWord ++ tailWord_1569096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569096).length < 2 ^ (prefixWord ++ tailWord_1569096).sum := by decide
  have hdescent : baseEnd_1569096 < baseStart_1569096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569132 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1569132 : Nat := 118140960795 + 1569132 * 2 ^ 59
def prefixEnd_1569132 : Nat := 4983230072969 + 3 ^ 40 * 1569132 * 2
def baseEnd_1569132 : Nat := 537145950900573331689133

theorem tailTrace_1569132 : CollatzResearch.WordTrace tailWord_1569132 prefixEnd_1569132 537145950900573331689133 := by
  unfold tailWord_1569132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615472875655112627610825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38153963834206816836814433 28615472875655112627610825)
  ·
    refine ⟨21461604656741334470708119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28615472875655112627610825 21461604656741334470708119)
    ·
      refine ⟨32192406985112001706062179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21461604656741334470708119 32192406985112001706062179)
      ·
        refine ⟨48288610477668002559093269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32192406985112001706062179 48288610477668002559093269)
        ·
          refine ⟨2263528616140687619957497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48288610477668002559093269 2263528616140687619957497)
          ·
            refine ⟨1697646462105515714968123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263528616140687619957497 1697646462105515714968123)
            ·
              refine ⟨2546469693158273572452185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697646462105515714968123 2546469693158273572452185)
              ·
                refine ⟨1909852269868705179339139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546469693158273572452185 1909852269868705179339139)
                ·
                  refine ⟨2864778404803057769008709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909852269868705179339139 2864778404803057769008709)
                  ·
                    refine ⟨537145950900573331689133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864778404803057769008709 537145950900573331689133)
                    ·
                      rfl

theorem cell22_1569132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1569132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569132 prefixEnd_1569132 := by exact prefixLift 1569132
  have htrace : WordTrace (prefixWord ++ tailWord_1569132) baseStart_1569132 baseEnd_1569132 := by
    simpa [prefixWord, tailWord_1569132, baseEnd_1569132] using wordTrace_append hprefix tailTrace_1569132
  have hstable : (prefixWord ++ tailWord_1569132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569132).length < 2 ^ (prefixWord ++ tailWord_1569132).sum := by decide
  have hdescent : baseEnd_1569132 < baseStart_1569132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569192 : List Nat := [2, 1, 6, 1, 1, 2, 3, 6]
def baseStart_1569192 : Nat := 118140960795 + 1569192 * 2 ^ 59
def prefixEnd_1569192 : Nat := 4983230072969 + 3 ^ 40 * 1569192 * 2
def baseEnd_1569192 : Nat := 59685165569639241687661

theorem tailTrace_1569192 : CollatzResearch.WordTrace tailWord_1569192 prefixEnd_1569192 59685165569639241687661 := by
  unfold tailWord_1569192
  simp only [CollatzResearch.WordTrace]
  refine ⟨28616567065546427751202915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38155422754061903668270553 28616567065546427751202915)
  ·
    refine ⟨42924850598319641626804373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28616567065546427751202915 42924850598319641626804373)
    ·
      refine ⟨2012102371796233201256455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42924850598319641626804373 2012102371796233201256455)
      ·
        refine ⟨3018153557694349801884683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012102371796233201256455 3018153557694349801884683)
        ·
          refine ⟨4527230336541524702827025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018153557694349801884683 4527230336541524702827025)
          ·
            refine ⟨3395422752406143527120269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4527230336541524702827025 3395422752406143527120269)
            ·
              refine ⟨1273283532152303822670101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395422752406143527120269 1273283532152303822670101)
              ·
                refine ⟨59685165569639241687661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1273283532152303822670101 59685165569639241687661)
                ·
                  rfl

theorem cell22_1569192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_1569192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569192 prefixEnd_1569192 := by exact prefixLift 1569192
  have htrace : WordTrace (prefixWord ++ tailWord_1569192) baseStart_1569192 baseEnd_1569192 := by
    simpa [prefixWord, tailWord_1569192, baseEnd_1569192] using wordTrace_append hprefix tailTrace_1569192
  have hstable : (prefixWord ++ tailWord_1569192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569192).length < 2 ^ (prefixWord ++ tailWord_1569192).sum := by decide
  have hdescent : baseEnd_1569192 < baseStart_1569192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569194 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1569194 : Nat := 118140960795 + 1569194 * 2 ^ 59
def prefixEnd_1569194 : Nat := 4983230072969 + 3 ^ 40 * 1569194 * 2
def baseEnd_1569194 : Nat := 537167174767625836638943

theorem tailTrace_1569194 : CollatzResearch.WordTrace tailWord_1569194 prefixEnd_1569194 537167174767625836638943 := by
  unfold tailWord_1569194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14308301769271402460994659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38155471384723739895985757 14308301769271402460994659)
  ·
    refine ⟨21462452653907103691491989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14308301769271402460994659 21462452653907103691491989)
    ·
      refine ⟨1006052468151895485538687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21462452653907103691491989 1006052468151895485538687)
      ·
        refine ⟨1509078702227843228308031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006052468151895485538687 1509078702227843228308031)
        ·
          refine ⟨2263618053341764842462047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509078702227843228308031 2263618053341764842462047)
          ·
            refine ⟨3395427080012647263693071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263618053341764842462047 3395427080012647263693071)
            ·
              refine ⟨5093140620018970895539607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395427080012647263693071 5093140620018970895539607)
              ·
                refine ⟨7639710930028456343309411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093140620018970895539607 7639710930028456343309411)
                ·
                  refine ⟨11459566395042684514964117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7639710930028456343309411 11459566395042684514964117)
                  ·
                    refine ⟨537167174767625836638943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11459566395042684514964117 537167174767625836638943)
                    ·
                      rfl

theorem cell22_1569194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1569194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569194 prefixEnd_1569194 := by exact prefixLift 1569194
  have htrace : WordTrace (prefixWord ++ tailWord_1569194) baseStart_1569194 baseEnd_1569194 := by
    simpa [prefixWord, tailWord_1569194, baseEnd_1569194] using wordTrace_append hprefix tailTrace_1569194
  have hstable : (prefixWord ++ tailWord_1569194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569194).length < 2 ^ (prefixWord ++ tailWord_1569194).sum := by decide
  have hdescent : baseEnd_1569194 < baseStart_1569194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569207 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 1, 3]
def baseStart_1569207 : Nat := 118140960795 + 1569207 * 2 ^ 59
def prefixEnd_1569207 : Nat := 4983230072969 + 3 ^ 40 * 1569207 * 2
def baseEnd_1569207 : Nat := 537171624933298136063903

theorem tailTrace_1569207 : CollatzResearch.WordTrace tailWord_1569207 prefixEnd_1569207 537171624933298136063903 := by
  unfold tailWord_1569207
  simp only [CollatzResearch.WordTrace]
  refine ⟨57233681226038513064201875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38155787484025675376134583 57233681226038513064201875)
  ·
    refine ⟨85850521839057769596302813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57233681226038513064201875 85850521839057769596302813)
    ·
      refine ⟨32193945689646663598613555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85850521839057769596302813 32193945689646663598613555)
      ·
        refine ⟨48290918534469995397920333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32193945689646663598613555 48290918534469995397920333)
        ·
          refine ⟨18109094450426248274220125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48290918534469995397920333 18109094450426248274220125)
          ·
            refine ⟨6790910418909843102832547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18109094450426248274220125 6790910418909843102832547)
            ·
              refine ⟨10186365628364764654248821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790910418909843102832547 10186365628364764654248821)
              ·
                refine ⟨954971777659196686335827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10186365628364764654248821 954971777659196686335827)
                ·
                  refine ⟨1432457666488795029503741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954971777659196686335827 1432457666488795029503741)
                  ·
                    refine ⟨537171624933298136063903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432457666488795029503741 537171624933298136063903)
                    ·
                      rfl

theorem cell22_1569207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_1569207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569207 prefixEnd_1569207 := by exact prefixLift 1569207
  have htrace : WordTrace (prefixWord ++ tailWord_1569207) baseStart_1569207 baseEnd_1569207 := by
    simpa [prefixWord, tailWord_1569207, baseEnd_1569207] using wordTrace_append hprefix tailTrace_1569207
  have hstable : (prefixWord ++ tailWord_1569207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569207).length < 2 ^ (prefixWord ++ tailWord_1569207).sum := by decide
  have hdescent : baseEnd_1569207 < baseStart_1569207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569233 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_1569233 : Nat := 118140960795 + 1569233 * 2 ^ 59
def prefixEnd_1569233 : Nat := 4983230072969 + 3 ^ 40 * 1569233 * 2
def baseEnd_1569233 : Nat := 537180525264642734913823

theorem tailTrace_1569233 : CollatzResearch.WordTrace tailWord_1569233 prefixEnd_1569233 537180525264642734913823 := by
  unfold tailWord_1569233
  simp only [CollatzResearch.WordTrace]
  refine ⟨57234629523944319504648353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38156419682629546336432235 57234629523944319504648353)
  ·
    refine ⟨42925972142958239628486265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57234629523944319504648353 42925972142958239628486265)
    ·
      refine ⟨32194479107218679721364699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42925972142958239628486265 32194479107218679721364699)
      ·
        refine ⟨48291718660828019582047049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32194479107218679721364699 48291718660828019582047049)
        ·
          refine ⟨36218788995621014686535287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48291718660828019582047049 36218788995621014686535287)
          ·
            refine ⟨54328183493431522029802931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36218788995621014686535287 54328183493431522029802931)
            ·
              refine ⟨81492275240147283044704397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54328183493431522029802931 81492275240147283044704397)
              ·
                refine ⟨30559603215055231141764149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81492275240147283044704397 30559603215055231141764149)
                ·
                  refine ⟨2864962801411427919540389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30559603215055231141764149 2864962801411427919540389)
                  ·
                    refine ⟨537180525264642734913823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864962801411427919540389 537180525264642734913823)
                    ·
                      rfl

theorem cell22_1569233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_1569233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569233 prefixEnd_1569233 := by exact prefixLift 1569233
  have htrace : WordTrace (prefixWord ++ tailWord_1569233) baseStart_1569233 baseEnd_1569233 := by
    simpa [prefixWord, tailWord_1569233, baseEnd_1569233] using wordTrace_append hprefix tailTrace_1569233
  have hstable : (prefixWord ++ tailWord_1569233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569233).length < 2 ^ (prefixWord ++ tailWord_1569233).sum := by decide
  have hdescent : baseEnd_1569233 < baseStart_1569233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569237 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 5]
def baseStart_1569237 : Nat := 118140960795 + 1569237 * 2 ^ 59
def prefixEnd_1569237 : Nat := 4983230072969 + 3 ^ 40 * 1569237 * 2
def baseEnd_1569237 : Nat := 179060631515462685937937

theorem tailTrace_1569237 : CollatzResearch.WordTrace tailWord_1569237 prefixEnd_1569237 179060631515462685937937 := by
  unfold tailWord_1569237
  simp only [CollatzResearch.WordTrace]
  refine ⟨57234775415929828187793965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38156516943953218791862643 57234775415929828187793965)
  ·
    refine ⟨21463040780973685570422737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57234775415929828187793965 21463040780973685570422737)
    ·
      refine ⟨16097280585730264177817053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21463040780973685570422737 16097280585730264177817053)
      ·
        refine ⟨6036480219648849066681395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16097280585730264177817053 6036480219648849066681395)
        ·
          refine ⟨9054720329473273600022093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036480219648849066681395 9054720329473273600022093)
          ·
            refine ⟨3395520123552477600008285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9054720329473273600022093 3395520123552477600008285)
            ·
              refine ⟨1273320046332179100003107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395520123552477600008285 1273320046332179100003107)
              ·
                refine ⟨1909980069498268650004661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273320046332179100003107 1909980069498268650004661)
                ·
                  refine ⟨179060631515462685937937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1909980069498268650004661 179060631515462685937937)
                  ·
                    rfl

theorem cell22_1569237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_1569237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569237 prefixEnd_1569237 := by exact prefixLift 1569237
  have htrace : WordTrace (prefixWord ++ tailWord_1569237) baseStart_1569237 baseEnd_1569237 := by
    simpa [prefixWord, tailWord_1569237, baseEnd_1569237] using wordTrace_append hprefix tailTrace_1569237
  have hstable : (prefixWord ++ tailWord_1569237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569237).length < 2 ^ (prefixWord ++ tailWord_1569237).sum := by decide
  have hdescent : baseEnd_1569237 < baseStart_1569237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569248 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_1569248 : Nat := 118140960795 + 1569248 * 2 ^ 59
def prefixEnd_1569248 : Nat := 4983230072969 + 3 ^ 40 * 1569248 * 2
def baseEnd_1569248 : Nat := 179061886690395898596259

theorem tailTrace_1569248 : CollatzResearch.WordTrace tailWord_1569248 prefixEnd_1569248 179061886690395898596259 := by
  unfold tailWord_1569248
  simp only [CollatzResearch.WordTrace]
  refine ⟨28617588309444988533222199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38156784412593318044296265 28617588309444988533222199)
  ·
    refine ⟨42926382464167482799833299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28617588309444988533222199 42926382464167482799833299)
    ·
      refine ⟨64389573696251224199749949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42926382464167482799833299 64389573696251224199749949)
      ·
        refine ⟨24146090136094209074906231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64389573696251224199749949 24146090136094209074906231)
        ·
          refine ⟨36219135204141313612359347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24146090136094209074906231 36219135204141313612359347)
          ·
            refine ⟨54328702806211970418539021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36219135204141313612359347 54328702806211970418539021)
            ·
              refine ⟨20373263552329488906952133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54328702806211970418539021 20373263552329488906952133)
              ·
                refine ⟨3819986916061779170053525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20373263552329488906952133 3819986916061779170053525)
                ·
                  refine ⟨179061886690395898596259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3819986916061779170053525 179061886690395898596259)
                  ·
                    rfl

theorem cell22_1569248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_1569248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569248 prefixEnd_1569248 := by exact prefixLift 1569248
  have htrace : WordTrace (prefixWord ++ tailWord_1569248) baseStart_1569248 baseEnd_1569248 := by
    simpa [prefixWord, tailWord_1569248, baseEnd_1569248] using wordTrace_append hprefix tailTrace_1569248
  have hstable : (prefixWord ++ tailWord_1569248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569248).length < 2 ^ (prefixWord ++ tailWord_1569248).sum := by decide
  have hdescent : baseEnd_1569248 < baseStart_1569248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569263 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_1569263 : Nat := 118140960795 + 1569263 * 2 ^ 59
def prefixEnd_1569263 : Nat := 4983230072969 + 3 ^ 40 * 1569263 * 2
def baseEnd_1569263 : Nat := 537190794877732656663731

theorem tailTrace_1569263 : CollatzResearch.WordTrace tailWord_1569263 prefixEnd_1569263 537190794877732656663731 := by
  unfold tailWord_1569263
  simp only [CollatzResearch.WordTrace]
  refine ⟨57235723713835634628240443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38157149142557089752160295 57235723713835634628240443)
  ·
    refine ⟨85853585570753451942360665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57235723713835634628240443 85853585570753451942360665)
    ·
      refine ⟨64390189178065088956770499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85853585570753451942360665 64390189178065088956770499)
      ·
        refine ⟨96585283767097633435155749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64390189178065088956770499 96585283767097633435155749)
        ·
          refine ⟨18109740706330806269091703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96585283767097633435155749 18109740706330806269091703)
          ·
            refine ⟨27164611059496209403637555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18109740706330806269091703 27164611059496209403637555)
            ·
              refine ⟨40746916589244314105456333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27164611059496209403637555 40746916589244314105456333)
              ·
                refine ⟨15280093720966617789546125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40746916589244314105456333 15280093720966617789546125)
                ·
                  refine ⟨5730035145362481671079797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15280093720966617789546125 5730035145362481671079797)
                  ·
                    refine ⟨537190794877732656663731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5730035145362481671079797 537190794877732656663731)
                    ·
                      rfl

theorem cell22_1569263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_1569263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569263 prefixEnd_1569263 := by exact prefixLift 1569263
  have htrace : WordTrace (prefixWord ++ tailWord_1569263) baseStart_1569263 baseEnd_1569263 := by
    simpa [prefixWord, tailWord_1569263, baseEnd_1569263] using wordTrace_append hprefix tailTrace_1569263
  have hstable : (prefixWord ++ tailWord_1569263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569263).length < 2 ^ (prefixWord ++ tailWord_1569263).sum := by decide
  have hdescent : baseEnd_1569263 < baseStart_1569263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569323 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_1569323 : Nat := 118140960795 + 1569323 * 2 ^ 59
def prefixEnd_1569323 : Nat := 4983230072969 + 3 ^ 40 * 1569323 * 2
def baseEnd_1569323 : Nat := 537211334103912500163547

theorem tailTrace_1569323 : CollatzResearch.WordTrace tailWord_1569323 prefixEnd_1569323 537211334103912500163547 := by
  unfold tailWord_1569323
  simp only [CollatzResearch.WordTrace]
  refine ⟨57237912093618264875424623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38158608062412176583616415 57237912093618264875424623)
  ·
    refine ⟨85856868140427397313136935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57237912093618264875424623 85856868140427397313136935)
    ·
      refine ⟨128785302210641095969705403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85856868140427397313136935 128785302210641095969705403)
      ·
        refine ⟨193177953315961643954558105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128785302210641095969705403 193177953315961643954558105)
        ·
          refine ⟨144883464986971232965918579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193177953315961643954558105 144883464986971232965918579)
          ·
            refine ⟨217325197480456849448877869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144883464986971232965918579 217325197480456849448877869)
            ·
              refine ⟨81496949055171318543329201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217325197480456849448877869 81496949055171318543329201)
              ·
                refine ⟨61122711791378488907496901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81496949055171318543329201 61122711791378488907496901)
                ·
                  refine ⟨11460508460883466670155669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61122711791378488907496901 11460508460883466670155669)
                  ·
                    refine ⟨537211334103912500163547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11460508460883466670155669 537211334103912500163547)
                    ·
                      rfl

theorem cell22_1569323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_1569323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569323 prefixEnd_1569323 := by exact prefixLift 1569323
  have htrace : WordTrace (prefixWord ++ tailWord_1569323) baseStart_1569323 baseEnd_1569323 := by
    simpa [prefixWord, tailWord_1569323, baseEnd_1569323] using wordTrace_append hprefix tailTrace_1569323
  have hstable : (prefixWord ++ tailWord_1569323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569323).length < 2 ^ (prefixWord ++ tailWord_1569323).sum := by decide
  have hdescent : baseEnd_1569323 < baseStart_1569323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569340 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1569340 : Nat := 118140960795 + 1569340 * 2 ^ 59
def prefixEnd_1569340 : Nat := 4983230072969 + 3 ^ 40 * 1569340 * 2
def baseEnd_1569340 : Nat := 537217153551330122488495

theorem tailTrace_1569340 : CollatzResearch.WordTrace tailWord_1569340 prefixEnd_1569340 537217153551330122488495 := by
  unfold tailWord_1569340
  simp only [CollatzResearch.WordTrace]
  refine ⟨28619266067278338389396737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38159021423037784519195649 28619266067278338389396737)
  ·
    refine ⟨21464449550458753792047553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28619266067278338389396737 21464449550458753792047553)
    ·
      refine ⟨16098337162844065344035665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21464449550458753792047553 16098337162844065344035665)
      ·
        refine ⟨12073752872133049008026749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16098337162844065344035665 12073752872133049008026749)
        ·
          refine ⟨4527657327049893378010031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12073752872133049008026749 4527657327049893378010031)
          ·
            refine ⟨6791485990574840067015047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4527657327049893378010031 6791485990574840067015047)
            ·
              refine ⟨10187228985862260100522571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6791485990574840067015047 10187228985862260100522571)
              ·
                refine ⟨15280843478793390150783857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10187228985862260100522571 15280843478793390150783857)
                ·
                  refine ⟨11460632609095042613087893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15280843478793390150783857 11460632609095042613087893)
                  ·
                    refine ⟨537217153551330122488495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11460632609095042613087893 537217153551330122488495)
                    ·
                      rfl

theorem cell22_1569340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1569340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569340 prefixEnd_1569340 := by exact prefixLift 1569340
  have htrace : WordTrace (prefixWord ++ tailWord_1569340) baseStart_1569340 baseEnd_1569340 := by
    simpa [prefixWord, tailWord_1569340, baseEnd_1569340] using wordTrace_append hprefix tailTrace_1569340
  have hstable : (prefixWord ++ tailWord_1569340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569340).length < 2 ^ (prefixWord ++ tailWord_1569340).sum := by decide
  have hdescent : baseEnd_1569340 < baseStart_1569340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569355 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 5]
def baseStart_1569355 : Nat := 118140960795 + 1569355 * 2 ^ 59
def prefixEnd_1569355 : Nat := 4983230072969 + 3 ^ 40 * 1569355 * 2
def baseEnd_1569355 : Nat := 179074096119291694454483

theorem tailTrace_1569355 : CollatzResearch.WordTrace tailWord_1569355 prefixEnd_1569355 179074096119291694454483 := by
  unfold tailWord_1569355
  simp only [CollatzResearch.WordTrace]
  refine ⟨57239079229502334340589519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38159386153001556227059679 57239079229502334340589519)
  ·
    refine ⟨85858618844253501510884279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57239079229502334340589519 85858618844253501510884279)
    ·
      refine ⟨128787928266380252266326419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85858618844253501510884279 128787928266380252266326419)
      ·
        refine ⟨193181892399570378399489629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128787928266380252266326419 193181892399570378399489629)
        ·
          refine ⟨72443209649838891899808611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193181892399570378399489629 72443209649838891899808611)
          ·
            refine ⟨108664814474758337849712917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72443209649838891899808611 108664814474758337849712917)
            ·
              refine ⟨5093663178504297086705293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108664814474758337849712917 5093663178504297086705293)
              ·
                refine ⟨1910123691939111407514485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5093663178504297086705293 1910123691939111407514485)
                ·
                  refine ⟨179074096119291694454483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910123691939111407514485 179074096119291694454483)
                  ·
                    rfl

theorem cell22_1569355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 5].length) (baseStart_1569355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569355 prefixEnd_1569355 := by exact prefixLift 1569355
  have htrace : WordTrace (prefixWord ++ tailWord_1569355) baseStart_1569355 baseEnd_1569355 := by
    simpa [prefixWord, tailWord_1569355, baseEnd_1569355] using wordTrace_append hprefix tailTrace_1569355
  have hstable : (prefixWord ++ tailWord_1569355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569355).length < 2 ^ (prefixWord ++ tailWord_1569355).sum := by decide
  have hdescent : baseEnd_1569355 < baseStart_1569355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569389 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1569389 : Nat := 118140960795 + 1569389 * 2 ^ 59
def prefixEnd_1569389 : Nat := 4983230072969 + 3 ^ 40 * 1569389 * 2
def baseEnd_1569389 : Nat := 179077975750903442671115

theorem tailTrace_1569389 : CollatzResearch.WordTrace tailWord_1569389 prefixEnd_1569389 179077975750903442671115 := by
  unfold tailWord_1569389
  simp only [CollatzResearch.WordTrace]
  refine ⟨57240319311379158147327221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38160212874252772098218147 57240319311379158147327221)
  ·
    refine ⟨5366279935441796076311927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57240319311379158147327221 5366279935441796076311927)
    ·
      refine ⟨8049419903162694114467891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5366279935441796076311927 8049419903162694114467891)
      ·
        refine ⟨12074129854744041171701837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8049419903162694114467891 12074129854744041171701837)
        ·
          refine ⟨4527798695529015439388189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12074129854744041171701837 4527798695529015439388189)
          ·
            refine ⟨1697924510823380789770571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4527798695529015439388189 1697924510823380789770571)
            ·
              refine ⟨2546886766235071184655857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697924510823380789770571 2546886766235071184655857)
              ·
                refine ⟨1910165074676303388491893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546886766235071184655857 1910165074676303388491893)
                ·
                  refine ⟨179077975750903442671115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910165074676303388491893 179077975750903442671115)
                  ·
                    rfl

theorem cell22_1569389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1569389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569389 prefixEnd_1569389 := by exact prefixLift 1569389
  have htrace : WordTrace (prefixWord ++ tailWord_1569389) baseStart_1569389 baseEnd_1569389 := by
    simpa [prefixWord, tailWord_1569389, baseEnd_1569389] using wordTrace_append hprefix tailTrace_1569389
  have hstable : (prefixWord ++ tailWord_1569389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569389).length < 2 ^ (prefixWord ++ tailWord_1569389).sum := by decide
  have hdescent : baseEnd_1569389 < baseStart_1569389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569432 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_1569432 : Nat := 118140960795 + 1569432 * 2 ^ 59
def prefixEnd_1569432 : Nat := 4983230072969 + 3 ^ 40 * 1569432 * 2
def baseEnd_1569432 : Nat := 537248647031472549188213

theorem tailTrace_1569432 : CollatzResearch.WordTrace tailWord_1569432 prefixEnd_1569432 537248647031472549188213 := by
  unfold tailWord_1569432
  simp only [CollatzResearch.WordTrace]
  refine ⟨28620943825111688245571275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38161258433482250994095033 28620943825111688245571275)
  ·
    refine ⟨42931415737667532368356913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28620943825111688245571275 42931415737667532368356913)
    ·
      refine ⟨32198561803250649276267685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42931415737667532368356913 32198561803250649276267685)
      ·
        refine ⟨6037230338109496739300191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32198561803250649276267685 6037230338109496739300191)
        ·
          refine ⟨9055845507164245108950287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037230338109496739300191 9055845507164245108950287)
          ·
            refine ⟨13583768260746367663425431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9055845507164245108950287 13583768260746367663425431)
            ·
              refine ⟨20375652391119551495138147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13583768260746367663425431 20375652391119551495138147)
              ·
                refine ⟨30563478586679327242707221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20375652391119551495138147 30563478586679327242707221)
                ·
                  refine ⟨1432663058750593464501901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30563478586679327242707221 1432663058750593464501901)
                  ·
                    refine ⟨537248647031472549188213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432663058750593464501901 537248647031472549188213)
                    ·
                      rfl

theorem cell22_1569432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_1569432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569432 prefixEnd_1569432 := by exact prefixLift 1569432
  have htrace : WordTrace (prefixWord ++ tailWord_1569432) baseStart_1569432 baseEnd_1569432 := by
    simpa [prefixWord, tailWord_1569432, baseEnd_1569432] using wordTrace_append hprefix tailTrace_1569432
  have hstable : (prefixWord ++ tailWord_1569432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569432).length < 2 ^ (prefixWord ++ tailWord_1569432).sum := by decide
  have hdescent : baseEnd_1569432 < baseStart_1569432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569522 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1569522 : Nat := 118140960795 + 1569522 * 2 ^ 59
def prefixEnd_1569522 : Nat := 4983230072969 + 3 ^ 40 * 1569522 * 2
def baseEnd_1569522 : Nat := 537279455870742314437937

theorem tailTrace_1569522 : CollatzResearch.WordTrace tailWord_1569522 prefixEnd_1569522 537279455870742314437937 := by
  unfold tailWord_1569522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14311292554974330465479705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38163446813264881241279213 14311292554974330465479705)
  ·
    refine ⟨10733469416230747849109779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14311292554974330465479705 10733469416230747849109779)
    ·
      refine ⟨16100204124346121773664669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10733469416230747849109779 16100204124346121773664669)
      ·
        refine ⟨6037576546629795665124251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16100204124346121773664669 6037576546629795665124251)
        ·
          refine ⟨9056364819944693497686377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037576546629795665124251 9056364819944693497686377)
          ·
            refine ⟨6792273614958520123264783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9056364819944693497686377 6792273614958520123264783)
            ·
              refine ⟨10188410422437780184897175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792273614958520123264783 10188410422437780184897175)
              ·
                refine ⟨15282615633656670277345763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10188410422437780184897175 15282615633656670277345763)
                ·
                  refine ⟨22923923450485005416018645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15282615633656670277345763 22923923450485005416018645)
                  ·
                    refine ⟨537279455870742314437937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22923923450485005416018645 537279455870742314437937)
                    ·
                      rfl

theorem cell22_1569522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1569522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569522 prefixEnd_1569522 := by exact prefixLift 1569522
  have htrace : WordTrace (prefixWord ++ tailWord_1569522) baseStart_1569522 baseEnd_1569522 := by
    simpa [prefixWord, tailWord_1569522, baseEnd_1569522] using wordTrace_append hprefix tailTrace_1569522
  have hstable : (prefixWord ++ tailWord_1569522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569522).length < 2 ^ (prefixWord ++ tailWord_1569522).sum := by decide
  have hdescent : baseEnd_1569522 < baseStart_1569522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569569 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 4]
def baseStart_1569569 : Nat := 118140960795 + 1569569 * 2 ^ 59
def prefixEnd_1569569 : Nat := 4983230072969 + 3 ^ 40 * 1569569 * 2
def baseEnd_1569569 : Nat := 179098514977083286170931

theorem tailTrace_1569569 : CollatzResearch.WordTrace tailWord_1569569 prefixEnd_1569569 179098514977083286170931 := by
  unfold tailWord_1569569
  simp only [CollatzResearch.WordTrace]
  refine ⟨57246884450727048888879761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38164589633818032592586507 57246884450727048888879761)
  ·
    refine ⟨42935163338045286666659821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57246884450727048888879761 42935163338045286666659821)
    ·
      refine ⟨16100686251766982499997433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42935163338045286666659821 16100686251766982499997433)
      ·
        refine ⟨12075514688825236874998075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16100686251766982499997433 12075514688825236874998075)
        ·
          refine ⟨18113272033237855312497113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12075514688825236874998075 18113272033237855312497113)
          ·
            refine ⟨13584954024928391484372835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18113272033237855312497113 13584954024928391484372835)
            ·
              refine ⟨20377431037392587226559253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13584954024928391484372835 20377431037392587226559253)
              ·
                refine ⟨955192079877777526244965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20377431037392587226559253 955192079877777526244965)
                ·
                  refine ⟨179098514977083286170931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955192079877777526244965 179098514977083286170931)
                  ·
                    rfl

theorem cell22_1569569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_1569569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569569 prefixEnd_1569569 := by exact prefixLift 1569569
  have htrace : WordTrace (prefixWord ++ tailWord_1569569) baseStart_1569569 baseEnd_1569569 := by
    simpa [prefixWord, tailWord_1569569, baseEnd_1569569] using wordTrace_append hprefix tailTrace_1569569
  have hstable : (prefixWord ++ tailWord_1569569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569569).length < 2 ^ (prefixWord ++ tailWord_1569569).sum := by decide
  have hdescent : baseEnd_1569569 < baseStart_1569569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569584 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_1569584 : Nat := 118140960795 + 1569584 * 2 ^ 59
def prefixEnd_1569584 : Nat := 4983230072969 + 3 ^ 40 * 1569584 * 2
def baseEnd_1569584 : Nat := 537300679737794819387747

theorem tailTrace_1569584 : CollatzResearch.WordTrace tailWord_1569584 prefixEnd_1569584 537300679737794819387747 := by
  unfold tailWord_1569584
  simp only [CollatzResearch.WordTrace]
  refine ⟨28623715772836353225337903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38164954363781804300450537 28623715772836353225337903)
  ·
    refine ⟨42935573659254529838006855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28623715772836353225337903 42935573659254529838006855)
    ·
      refine ⟨64403360488881794757010283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42935573659254529838006855 64403360488881794757010283)
      ·
        refine ⟨96605040733322692135515425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64403360488881794757010283 96605040733322692135515425)
        ·
          refine ⟨72453780549992019101636569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96605040733322692135515425 72453780549992019101636569)
          ·
            refine ⟨54340335412494014326227427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72453780549992019101636569 54340335412494014326227427)
            ·
              refine ⟨81510503118741021489341141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54340335412494014326227427 81510503118741021489341141)
              ·
                refine ⟨1910402416845492691156433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81510503118741021489341141 1910402416845492691156433)
                ·
                  refine ⟨1432801812634119518367325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1910402416845492691156433 1432801812634119518367325)
                  ·
                    refine ⟨537300679737794819387747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432801812634119518367325 537300679737794819387747)
                    ·
                      rfl

theorem cell22_1569584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_1569584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569584 prefixEnd_1569584 := by exact prefixLift 1569584
  have htrace : WordTrace (prefixWord ++ tailWord_1569584) baseStart_1569584 baseEnd_1569584 := by
    simpa [prefixWord, tailWord_1569584, baseEnd_1569584] using wordTrace_append hprefix tailTrace_1569584
  have hstable : (prefixWord ++ tailWord_1569584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569584).length < 2 ^ (prefixWord ++ tailWord_1569584).sum := by decide
  have hdescent : baseEnd_1569584 < baseStart_1569584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569588 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1569588 : Nat := 118140960795 + 1569588 * 2 ^ 59
def prefixEnd_1569588 : Nat := 4983230072969 + 3 ^ 40 * 1569588 * 2
def baseEnd_1569588 : Nat := 537302049019540142287735

theorem tailTrace_1569588 : CollatzResearch.WordTrace tailWord_1569588 prefixEnd_1569588 537302049019540142287735 := by
  unfold tailWord_1569588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28623788718829107566910709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38165051625105476755880945 28623788718829107566910709)
  ·
    refine ⟨2683480192390228834397879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28623788718829107566910709 2683480192390228834397879)
    ·
      refine ⟨4025220288585343251596819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683480192390228834397879 4025220288585343251596819)
      ·
        refine ⟨6037830432878014877395229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025220288585343251596819 6037830432878014877395229)
        ·
          refine ⟨2264186412329255579023211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6037830432878014877395229 2264186412329255579023211)
          ·
            refine ⟨3396279618493883368534817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264186412329255579023211 3396279618493883368534817)
            ·
              refine ⟨2547209713870412526401113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396279618493883368534817 2547209713870412526401113)
              ·
                refine ⟨1910407285402809394800835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547209713870412526401113 1910407285402809394800835)
                ·
                  refine ⟨2865610928104214092201253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910407285402809394800835 2865610928104214092201253)
                  ·
                    refine ⟨537302049019540142287735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2865610928104214092201253 537302049019540142287735)
                    ·
                      rfl

theorem cell22_1569588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1569588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569588 prefixEnd_1569588 := by exact prefixLift 1569588
  have htrace : WordTrace (prefixWord ++ tailWord_1569588) baseStart_1569588 baseEnd_1569588 := by
    simpa [prefixWord, tailWord_1569588, baseEnd_1569588] using wordTrace_append hprefix tailTrace_1569588
  have hstable : (prefixWord ++ tailWord_1569588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569588).length < 2 ^ (prefixWord ++ tailWord_1569588).sum := by decide
  have hdescent : baseEnd_1569588 < baseStart_1569588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569719 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1569719 : Nat := 118140960795 + 1569719 * 2 ^ 59
def prefixEnd_1569719 : Nat := 4983230072969 + 3 ^ 40 * 1569719 * 2
def baseEnd_1569719 : Nat := 537346892996699467262333

theorem tailTrace_1569719 : CollatzResearch.WordTrace tailWord_1569719 prefixEnd_1569719 537346892996699467262333 := by
  unfold tailWord_1569719
  simp only [CollatzResearch.WordTrace]
  refine ⟨57252355400183624506840211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38168236933455749671226807 57252355400183624506840211)
  ·
    refine ⟨85878533100275436760260317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57252355400183624506840211 85878533100275436760260317)
    ·
      refine ⟨32204449912603288785097619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85878533100275436760260317 32204449912603288785097619)
      ·
        refine ⟨48306674868904933177646429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32204449912603288785097619 48306674868904933177646429)
        ·
          refine ⟨18115003075839349941617411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48306674868904933177646429 18115003075839349941617411)
          ·
            refine ⟨27172504613759024912426117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18115003075839349941617411 27172504613759024912426117)
            ·
              refine ⟨5094844615079817171079897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27172504613759024912426117 5094844615079817171079897)
              ·
                refine ⟨3821133461309862878309923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5094844615079817171079897 3821133461309862878309923)
                ·
                  refine ⟨5731700191964794317464885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821133461309862878309923 5731700191964794317464885)
                  ·
                    refine ⟨537346892996699467262333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5731700191964794317464885 537346892996699467262333)
                    ·
                      rfl

theorem cell22_1569719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1569719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569719 prefixEnd_1569719 := by exact prefixLift 1569719
  have htrace : WordTrace (prefixWord ++ tailWord_1569719) baseStart_1569719 baseEnd_1569719 := by
    simpa [prefixWord, tailWord_1569719, baseEnd_1569719] using wordTrace_append hprefix tailTrace_1569719
  have hstable : (prefixWord ++ tailWord_1569719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569719).length < 2 ^ (prefixWord ++ tailWord_1569719).sum := by decide
  have hdescent : baseEnd_1569719 < baseStart_1569719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569721 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 4]
def baseStart_1569721 : Nat := 118140960795 + 1569721 * 2 ^ 59
def prefixEnd_1569721 : Nat := 4983230072969 + 3 ^ 40 * 1569721 * 2
def baseEnd_1569721 : Nat := 179115859212524042904109

theorem tailTrace_1569721 : CollatzResearch.WordTrace tailWord_1569721 prefixEnd_1569721 179115859212524042904109 := by
  unfold tailWord_1569721
  simp only [CollatzResearch.WordTrace]
  refine ⟨57252428346176378848413017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38168285564117585898942011 57252428346176378848413017)
  ·
    refine ⟨42939321259632284136309763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57252428346176378848413017 42939321259632284136309763)
    ·
      refine ⟨64408981889448426204464645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42939321259632284136309763 64408981889448426204464645)
      ·
        refine ⟨12076684104271579913337121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64408981889448426204464645 12076684104271579913337121)
        ·
          refine ⟨9057513078203684935002841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12076684104271579913337121 9057513078203684935002841)
          ·
            refine ⟨6793134808652763701252131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9057513078203684935002841 6793134808652763701252131)
            ·
              refine ⟨10189702212979145551878197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793134808652763701252131 10189702212979145551878197)
              ·
                refine ⟨955284582466794895488581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10189702212979145551878197 955284582466794895488581)
                ·
                  refine ⟨179115859212524042904109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955284582466794895488581 179115859212524042904109)
                  ·
                    rfl

theorem cell22_1569721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_1569721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569721 prefixEnd_1569721 := by exact prefixLift 1569721
  have htrace : WordTrace (prefixWord ++ tailWord_1569721) baseStart_1569721 baseEnd_1569721 := by
    simpa [prefixWord, tailWord_1569721, baseEnd_1569721] using wordTrace_append hprefix tailTrace_1569721
  have hstable : (prefixWord ++ tailWord_1569721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569721).length < 2 ^ (prefixWord ++ tailWord_1569721).sum := by decide
  have hdescent : baseEnd_1569721 < baseStart_1569721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569809 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_1569809 : Nat := 118140960795 + 1569809 * 2 ^ 59
def prefixEnd_1569809 : Nat := 4983230072969 + 3 ^ 40 * 1569809 * 2
def baseEnd_1569809 : Nat := 537377701835969232512057

theorem tailTrace_1569809 : CollatzResearch.WordTrace tailWord_1569809 prefixEnd_1569809 537377701835969232512057 := by
  unfold tailWord_1569809
  simp only [CollatzResearch.WordTrace]
  refine ⟨57255637969857569877616481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38170425313238379918410987 57255637969857569877616481)
  ·
    refine ⟨42941728477393177408212361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57255637969857569877616481 42941728477393177408212361)
    ·
      refine ⟨32206296358044883056159271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42941728477393177408212361 32206296358044883056159271)
      ·
        refine ⟨48309444537067324584238907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32206296358044883056159271 48309444537067324584238907)
        ·
          refine ⟨72464166805600986876358361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48309444537067324584238907 72464166805600986876358361)
          ·
            refine ⟨54348125104200740157268771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72464166805600986876358361 54348125104200740157268771)
            ·
              refine ⟨81522187656301110235903157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54348125104200740157268771 81522187656301110235903157)
              ·
                refine ⟨7642705092778229084615921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81522187656301110235903157 7642705092778229084615921)
                ·
                  refine ⟨5732028819583671813461941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7642705092778229084615921 5732028819583671813461941)
                  ·
                    refine ⟨537377701835969232512057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5732028819583671813461941 537377701835969232512057)
                    ·
                      rfl

theorem cell22_1569809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_1569809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569809 prefixEnd_1569809 := by exact prefixLift 1569809
  have htrace : WordTrace (prefixWord ++ tailWord_1569809) baseStart_1569809 baseEnd_1569809 := by
    simpa [prefixWord, tailWord_1569809, baseEnd_1569809] using wordTrace_append hprefix tailTrace_1569809
  have hstable : (prefixWord ++ tailWord_1569809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569809).length < 2 ^ (prefixWord ++ tailWord_1569809).sum := by decide
  have hdescent : baseEnd_1569809 < baseStart_1569809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569890 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1569890 : Nat := 118140960795 + 1569890 * 2 ^ 59
def prefixEnd_1569890 : Nat := 4983230072969 + 3 ^ 40 * 1569890 * 2
def baseEnd_1569890 : Nat := 179135143263770673745603

theorem tailTrace_1569890 : CollatzResearch.WordTrace tailWord_1569890 prefixEnd_1569890 179135143263770673745603 := by
  unfold tailWord_1569890
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314648070641030177828781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38172394855042747140876749 14314648070641030177828781)
  ·
    refine ⟨5367993026490386316685793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14314648070641030177828781 5367993026490386316685793)
    ·
      refine ⟨4025994769867789737514345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5367993026490386316685793 4025994769867789737514345)
      ·
        refine ⟨3019496077400842303135759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4025994769867789737514345 3019496077400842303135759)
        ·
          refine ⟨4529244116101263454703639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019496077400842303135759 4529244116101263454703639)
          ·
            refine ⟨6793866174151895182055459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529244116101263454703639 6793866174151895182055459)
            ·
              refine ⟨10190799261227842773083189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793866174151895182055459 10190799261227842773083189)
              ·
                refine ⟨955387430740110259976549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10190799261227842773083189 955387430740110259976549)
                ·
                  refine ⟨179135143263770673745603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955387430740110259976549 179135143263770673745603)
                  ·
                    rfl

theorem cell22_1569890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1569890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569890 prefixEnd_1569890 := by exact prefixLift 1569890
  have htrace : WordTrace (prefixWord ++ tailWord_1569890) baseStart_1569890 baseEnd_1569890 := by
    simpa [prefixWord, tailWord_1569890, baseEnd_1569890] using wordTrace_append hprefix tailTrace_1569890
  have hstable : (prefixWord ++ tailWord_1569890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569890).length < 2 ^ (prefixWord ++ tailWord_1569890).sum := by decide
  have hdescent : baseEnd_1569890 < baseStart_1569890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569899 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_1569899 : Nat := 118140960795 + 1569899 * 2 ^ 59
def prefixEnd_1569899 : Nat := 4983230072969 + 3 ^ 40 * 1569899 * 2
def baseEnd_1569899 : Nat := 537408510675238997761781

theorem tailTrace_1569899 : CollatzResearch.WordTrace tailWord_1569899 prefixEnd_1569899 537408510675238997761781 := by
  unfold tailWord_1569899
  simp only [CollatzResearch.WordTrace]
  refine ⟨57258920539531515248392751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38172613693021010165595167 57258920539531515248392751)
  ·
    refine ⟨85888380809297272872589127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57258920539531515248392751 85888380809297272872589127)
    ·
      refine ⟨128832571213945909308883691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85888380809297272872589127 128832571213945909308883691)
      ·
        refine ⟨193248856820918863963325537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128832571213945909308883691 193248856820918863963325537)
        ·
          refine ⟨144936642615689147972494153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193248856820918863963325537 144936642615689147972494153)
          ·
            refine ⟨108702481961766860979370615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144936642615689147972494153 108702481961766860979370615)
            ·
              refine ⟨163053722942650291469055923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108702481961766860979370615 163053722942650291469055923)
              ·
                refine ⟨244580584413975437203583885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163053722942650291469055923 244580584413975437203583885)
                ·
                  refine ⟨91717719155240788951343957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244580584413975437203583885 91717719155240788951343957)
                  ·
                    refine ⟨537408510675238997761781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 91717719155240788951343957 537408510675238997761781)
                    ·
                      rfl

theorem cell22_1569899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_1569899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569899 prefixEnd_1569899 := by exact prefixLift 1569899
  have htrace : WordTrace (prefixWord ++ tailWord_1569899) baseStart_1569899 baseEnd_1569899 := by
    simpa [prefixWord, tailWord_1569899, baseEnd_1569899] using wordTrace_append hprefix tailTrace_1569899
  have hstable : (prefixWord ++ tailWord_1569899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569899).length < 2 ^ (prefixWord ++ tailWord_1569899).sum := by decide
  have hdescent : baseEnd_1569899 < baseStart_1569899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569901 : List Nat := [1, 5, 1, 1, 2, 3, 9]
def baseStart_1569901 : Nat := 118140960795 + 1569901 * 2 ^ 59
def prefixEnd_1569901 : Nat := 4983230072969 + 3 ^ 40 * 1569901 * 2
def baseEnd_1569901 : Nat := 19904044270967098489325

theorem tailTrace_1569901 : CollatzResearch.WordTrace tailWord_1569901 prefixEnd_1569901 19904044270967098489325 := by
  unfold tailWord_1569901
  simp only [CollatzResearch.WordTrace]
  refine ⟨57258993485524269589965557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38172662323682846393310371 57258993485524269589965557)
  ·
    refine ⟨5368030639267900274059271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57258993485524269589965557 5368030639267900274059271)
    ·
      refine ⟨8052045958901850411088907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5368030639267900274059271 8052045958901850411088907)
      ·
        refine ⟨12078068938352775616633361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8052045958901850411088907 12078068938352775616633361)
        ·
          refine ⟨9058551703764581712475021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12078068938352775616633361 9058551703764581712475021)
          ·
            refine ⟨3396956888911718142178133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9058551703764581712475021 3396956888911718142178133)
            ·
              refine ⟨19904044270967098489325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3396956888911718142178133 19904044270967098489325)
              ·
                rfl

theorem cell22_1569901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 9].length) (baseStart_1569901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569901 prefixEnd_1569901 := by exact prefixLift 1569901
  have htrace : WordTrace (prefixWord ++ tailWord_1569901) baseStart_1569901 baseEnd_1569901 := by
    simpa [prefixWord, tailWord_1569901, baseEnd_1569901] using wordTrace_append hprefix tailTrace_1569901
  have hstable : (prefixWord ++ tailWord_1569901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569901).length < 2 ^ (prefixWord ++ tailWord_1569901).sum := by decide
  have hdescent : baseEnd_1569901 < baseStart_1569901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569980 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 5]
def baseStart_1569980 : Nat := 118140960795 + 1569980 * 2 ^ 59
def prefixEnd_1569980 : Nat := 4983230072969 + 3 ^ 40 * 1569980 * 2
def baseEnd_1569980 : Nat := 179145412876860595495511

theorem tailTrace_1569980 : CollatzResearch.WordTrace tailWord_1569980 prefixEnd_1569980 179145412876860595495511 := by
  unfold tailWord_1569980
  simp only [CollatzResearch.WordTrace]
  refine ⟨28630937426119033041045697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38174583234825377388060929 28630937426119033041045697)
  ·
    refine ⟨21473203069589274780784273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28630937426119033041045697 21473203069589274780784273)
    ·
      refine ⟨16104902302191956085588205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21473203069589274780784273 16104902302191956085588205)
      ·
        refine ⟨6039338363321983532095577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16104902302191956085588205 6039338363321983532095577)
        ·
          refine ⟨4529503772491487649071683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6039338363321983532095577 4529503772491487649071683)
          ·
            refine ⟨6794255658737231473607525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529503772491487649071683 6794255658737231473607525)
            ·
              refine ⟨1273922936013230901301411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6794255658737231473607525 1273922936013230901301411)
              ·
                refine ⟨1910884404019846351952117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273922936013230901301411 1910884404019846351952117)
                ·
                  refine ⟨179145412876860595495511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910884404019846351952117 179145412876860595495511)
                  ·
                    rfl

theorem cell22_1569980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_1569980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569980 prefixEnd_1569980 := by exact prefixLift 1569980
  have htrace : WordTrace (prefixWord ++ tailWord_1569980) baseStart_1569980 baseEnd_1569980 := by
    simpa [prefixWord, tailWord_1569980, baseEnd_1569980] using wordTrace_append hprefix tailTrace_1569980
  have hstable : (prefixWord ++ tailWord_1569980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569980).length < 2 ^ (prefixWord ++ tailWord_1569980).sum := by decide
  have hdescent : baseEnd_1569980 < baseStart_1569980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569991 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 6]
def baseStart_1569991 : Nat := 118140960795 + 1569991 * 2 ^ 59
def prefixEnd_1569991 : Nat := 4983230072969 + 3 ^ 40 * 1569991 * 2
def baseEnd_1569991 : Nat := 179146668051793808153833

theorem tailTrace_1569991 : CollatzResearch.WordTrace tailWord_1569991 prefixEnd_1569991 179146668051793808153833 := by
  unfold tailWord_1569991
  simp only [CollatzResearch.WordTrace]
  refine ⟨57262276055198214960741827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38174850703465476640494551 57262276055198214960741827)
  ·
    refine ⟨85893414082797322441112741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57262276055198214960741827 85893414082797322441112741)
    ·
      refine ⟨16105015140524497957708639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85893414082797322441112741 16105015140524497957708639)
      ·
        refine ⟨24157522710786746936562959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16105015140524497957708639 24157522710786746936562959)
        ·
          refine ⟨36236284066180120404844439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24157522710786746936562959 36236284066180120404844439)
          ·
            refine ⟨54354426099270180607266659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36236284066180120404844439 54354426099270180607266659)
            ·
              refine ⟨81531639148905270910899989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54354426099270180607266659 81531639148905270910899989)
              ·
                refine ⟨3821795585104934573948437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81531639148905270910899989 3821795585104934573948437)
                ·
                  refine ⟨179146668051793808153833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3821795585104934573948437 179146668051793808153833)
                  ·
                    rfl

theorem cell22_1569991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 6].length) (baseStart_1569991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1569991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1569991 prefixEnd_1569991 := by exact prefixLift 1569991
  have htrace : WordTrace (prefixWord ++ tailWord_1569991) baseStart_1569991 baseEnd_1569991 := by
    simpa [prefixWord, tailWord_1569991, baseEnd_1569991] using wordTrace_append hprefix tailTrace_1569991
  have hstable : (prefixWord ++ tailWord_1569991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569991).length < 2 ^ (prefixWord ++ tailWord_1569991).sum := by decide
  have hdescent : baseEnd_1569991 < baseStart_1569991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570038 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1570038 : Nat := 118140960795 + 1570038 * 2 ^ 59
def prefixEnd_1570038 : Nat := 4983230072969 + 3 ^ 40 * 1570038 * 2
def baseEnd_1570038 : Nat := 537456093215888968536355

theorem tailTrace_1570038 : CollatzResearch.WordTrace tailWord_1570038 prefixEnd_1570038 537456093215888968536355 := by
  unfold tailWord_1570038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578999392876746374231423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38175993524018627991801845 3578999392876746374231423)
  ·
    refine ⟨5368499089315119561347135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578999392876746374231423 5368499089315119561347135)
    ·
      refine ⟨8052748633972679342020703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5368499089315119561347135 8052748633972679342020703)
      ·
        refine ⟨12079122950959019013031055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8052748633972679342020703 12079122950959019013031055)
        ·
          refine ⟨18118684426438528519546583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12079122950959019013031055 18118684426438528519546583)
          ·
            refine ⟨27178026639657792779319875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18118684426438528519546583 27178026639657792779319875)
            ·
              refine ⟨40767039959486689168979813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27178026639657792779319875 40767039959486689168979813)
              ·
                refine ⟨7643819992403754219183715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40767039959486689168979813 7643819992403754219183715)
                ·
                  refine ⟨11465729988605631328775573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643819992403754219183715 11465729988605631328775573)
                  ·
                    refine ⟨537456093215888968536355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11465729988605631328775573 537456093215888968536355)
                    ·
                      rfl

theorem cell22_1570038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1570038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570038 prefixEnd_1570038 := by exact prefixLift 1570038
  have htrace : WordTrace (prefixWord ++ tailWord_1570038) baseStart_1570038 baseEnd_1570038 := by
    simpa [prefixWord, tailWord_1570038, baseEnd_1570038] using wordTrace_append hprefix tailTrace_1570038
  have hstable : (prefixWord ++ tailWord_1570038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570038).length < 2 ^ (prefixWord ++ tailWord_1570038).sum := by decide
  have hdescent : baseEnd_1570038 < baseStart_1570038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570053 : List Nat := [1, 3, 1, 1, 2, 1, 7, 6]
def baseStart_1570053 : Nat := 118140960795 + 1570053 * 2 ^ 59
def prefixEnd_1570053 : Nat := 4983230072969 + 3 ^ 40 * 1570053 * 2
def baseEnd_1570053 : Nat := 59717914224714881045701

theorem tailTrace_1570053 : CollatzResearch.WordTrace tailWord_1570053 prefixEnd_1570053 59717914224714881045701 := by
  unfold tailWord_1570053
  simp only [CollatzResearch.WordTrace]
  refine ⟨57264537380973599549498813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38176358253982399699665875 57264537380973599549498813)
  ·
    refine ⟨21474201517865099831062055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57264537380973599549498813 21474201517865099831062055)
    ·
      refine ⟨32211302276797649746593083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21474201517865099831062055 32211302276797649746593083)
      ·
        refine ⟨48316953415196474619889625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32211302276797649746593083 48316953415196474619889625)
        ·
          refine ⟨36237715061397355964917219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48316953415196474619889625 36237715061397355964917219)
          ·
            refine ⟨54356572592096033947375829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36237715061397355964917219 54356572592096033947375829)
            ·
              refine ⟨1273982170127250795641621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54356572592096033947375829 1273982170127250795641621)
              ·
                refine ⟨59717914224714881045701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1273982170127250795641621 59717914224714881045701)
                ·
                  rfl

theorem cell22_1570053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 6].length) (baseStart_1570053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570053 prefixEnd_1570053 := by exact prefixLift 1570053
  have htrace : WordTrace (prefixWord ++ tailWord_1570053) baseStart_1570053 baseEnd_1570053 := by
    simpa [prefixWord, tailWord_1570053, baseEnd_1570053] using wordTrace_append hprefix tailTrace_1570053
  have hstable : (prefixWord ++ tailWord_1570053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570053).length < 2 ^ (prefixWord ++ tailWord_1570053).sum := by decide
  have hdescent : baseEnd_1570053 < baseStart_1570053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570085 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_1570085 : Nat := 118140960795 + 1570085 * 2 ^ 59
def prefixEnd_1570085 : Nat := 4983230072969 + 3 ^ 40 * 1570085 * 2
def baseEnd_1570085 : Nat := 537472182276396512611211

theorem tailTrace_1570085 : CollatzResearch.WordTrace tailWord_1570085 prefixEnd_1570085 537472182276396512611211 := by
  unfold tailWord_1570085
  simp only [CollatzResearch.WordTrace]
  refine ⟨57265704516857669014663709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38177136344571779343109139 57265704516857669014663709)
  ·
    refine ⟨21474639193821625880498891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57265704516857669014663709 21474639193821625880498891)
    ·
      refine ⟨32211958790732438820748337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21474639193821625880498891 32211958790732438820748337)
      ·
        refine ⟨24158969093049329115561253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32211958790732438820748337 24158969093049329115561253)
        ·
          refine ⟨4529806704946749209167735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24158969093049329115561253 4529806704946749209167735)
          ·
            refine ⟨6794710057420123813751603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529806704946749209167735 6794710057420123813751603)
            ·
              refine ⟨10192065086130185720627405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794710057420123813751603 10192065086130185720627405)
              ·
                refine ⟨3822024407298819645235277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10192065086130185720627405 3822024407298819645235277)
                ·
                  refine ⟨1433259152737057366963229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3822024407298819645235277 1433259152737057366963229)
                  ·
                    refine ⟨537472182276396512611211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433259152737057366963229 537472182276396512611211)
                    ·
                      rfl

theorem cell22_1570085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_1570085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570085 prefixEnd_1570085 := by exact prefixLift 1570085
  have htrace : WordTrace (prefixWord ++ tailWord_1570085) baseStart_1570085 baseEnd_1570085 := by
    simpa [prefixWord, tailWord_1570085, baseEnd_1570085] using wordTrace_append hprefix tailTrace_1570085
  have hstable : (prefixWord ++ tailWord_1570085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570085).length < 2 ^ (prefixWord ++ tailWord_1570085).sum := by decide
  have hdescent : baseEnd_1570085 < baseStart_1570085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570119 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 1, 3]
def baseStart_1570119 : Nat := 118140960795 + 1570119 * 2 ^ 59
def prefixEnd_1570119 : Nat := 4983230072969 + 3 ^ 40 * 1570119 * 2
def baseEnd_1570119 : Nat := 537483821171231757261107

theorem tailTrace_1570119 : CollatzResearch.WordTrace tailWord_1570119 prefixEnd_1570119 537483821171231757261107 := by
  unfold tailWord_1570119
  simp only [CollatzResearch.WordTrace]
  refine ⟨57266944598734492821401411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38177963065822995214267607 57266944598734492821401411)
  ·
    refine ⟨85900416898101739232102117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57266944598734492821401411 85900416898101739232102117)
    ·
      refine ⟨16106328168394076106019147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85900416898101739232102117 16106328168394076106019147)
      ·
        refine ⟨24159492252591114159028721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16106328168394076106019147 24159492252591114159028721)
        ·
          refine ⟨18119619189443335619271541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24159492252591114159028721 18119619189443335619271541)
          ·
            refine ⟨1698714299010312714306707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18119619189443335619271541 1698714299010312714306707)
            ·
              refine ⟨2548071448515469071460061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698714299010312714306707 2548071448515469071460061)
              ·
                refine ⟨955526793193300901797523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548071448515469071460061 955526793193300901797523)
                ·
                  refine ⟨1433290189789951352696285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955526793193300901797523 1433290189789951352696285)
                  ·
                    refine ⟨537483821171231757261107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433290189789951352696285 537483821171231757261107)
                    ·
                      rfl

theorem cell22_1570119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_1570119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570119 prefixEnd_1570119 := by exact prefixLift 1570119
  have htrace : WordTrace (prefixWord ++ tailWord_1570119) baseStart_1570119 baseEnd_1570119 := by
    simpa [prefixWord, tailWord_1570119, baseEnd_1570119] using wordTrace_append hprefix tailTrace_1570119
  have hstable : (prefixWord ++ tailWord_1570119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570119).length < 2 ^ (prefixWord ++ tailWord_1570119).sum := by decide
  have hdescent : baseEnd_1570119 < baseStart_1570119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570205 : List Nat := [1, 4, 2, 1, 3, 1, 3, 7]
def baseStart_1570205 : Nat := 118140960795 + 1570205 * 2 ^ 59
def prefixEnd_1570205 : Nat := 4983230072969 + 3 ^ 40 * 1570205 * 2
def baseEnd_1570205 : Nat := 59723695636528466623427

theorem tailTrace_1570205 : CollatzResearch.WordTrace tailWord_1570205 prefixEnd_1570205 59723695636528466623427 := by
  unfold tailWord_1570205
  simp only [CollatzResearch.WordTrace]
  refine ⟨57270081276422929509032069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38180054184281953006021379 57270081276422929509032069)
  ·
    refine ⟨10738140239329299282943513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57270081276422929509032069 10738140239329299282943513)
    ·
      refine ⟨8053605179496974462207635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10738140239329299282943513 8053605179496974462207635)
      ·
        refine ⟨12080407769245461693311453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8053605179496974462207635 12080407769245461693311453)
        ·
          refine ⟨4530152913467048134991795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12080407769245461693311453 4530152913467048134991795)
          ·
            refine ⟨6795229370200572202487693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530152913467048134991795 6795229370200572202487693)
            ·
              refine ⟨2548211013825214575932885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6795229370200572202487693 2548211013825214575932885)
              ·
                refine ⟨59723695636528466623427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2548211013825214575932885 59723695636528466623427)
                ·
                  rfl

theorem cell22_1570205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 7].length) (baseStart_1570205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570205 prefixEnd_1570205 := by exact prefixLift 1570205
  have htrace : WordTrace (prefixWord ++ tailWord_1570205) baseStart_1570205 baseEnd_1570205 := by
    simpa [prefixWord, tailWord_1570205, baseEnd_1570205] using wordTrace_append hprefix tailTrace_1570205
  have hstable : (prefixWord ++ tailWord_1570205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570205).length < 2 ^ (prefixWord ++ tailWord_1570205).sum := by decide
  have hdescent : baseEnd_1570205 < baseStart_1570205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570220 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_1570220 : Nat := 118140960795 + 1570220 * 2 ^ 59
def prefixEnd_1570220 : Nat := 4983230072969 + 3 ^ 40 * 1570220 * 2
def baseEnd_1570220 : Nat := 537518395535301160485797

theorem tailTrace_1570220 : CollatzResearch.WordTrace tailWord_1570220 prefixEnd_1570220 537518395535301160485797 := by
  unfold tailWord_1570220
  simp only [CollatzResearch.WordTrace]
  refine ⟨28635314185684293535414057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38180418914245724713885409 28635314185684293535414057)
  ·
    refine ⟨21476485639263220151560543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28635314185684293535414057 21476485639263220151560543)
    ·
      refine ⟨32214728458894830227340815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21476485639263220151560543 32214728458894830227340815)
      ·
        refine ⟨48322092688342245341011223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32214728458894830227340815 48322092688342245341011223)
        ·
          refine ⟨72483139032513368011516835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48322092688342245341011223 72483139032513368011516835)
          ·
            refine ⟨108724708548770052017275253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72483139032513368011516835 108724708548770052017275253)
            ·
              refine ⟨10192941426447192376619555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108724708548770052017275253 10192941426447192376619555)
              ·
                refine ⟨15289412139670788564929333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10192941426447192376619555 15289412139670788564929333)
                ·
                  refine ⟨1433382388094136427962125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15289412139670788564929333 1433382388094136427962125)
                  ·
                    refine ⟨537518395535301160485797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433382388094136427962125 537518395535301160485797)
                    ·
                      rfl

theorem cell22_1570220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_1570220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570220 prefixEnd_1570220 := by exact prefixLift 1570220
  have htrace : WordTrace (prefixWord ++ tailWord_1570220) baseStart_1570220 baseEnd_1570220 := by
    simpa [prefixWord, tailWord_1570220, baseEnd_1570220] using wordTrace_append hprefix tailTrace_1570220
  have hstable : (prefixWord ++ tailWord_1570220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570220).length < 2 ^ (prefixWord ++ tailWord_1570220).sum := by decide
  have hdescent : baseEnd_1570220 < baseStart_1570220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570250 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_1570250 : Nat := 118140960795 + 1570250 * 2 ^ 59
def prefixEnd_1570250 : Nat := 4983230072969 + 3 ^ 40 * 1570250 * 2
def baseEnd_1570250 : Nat := 179176221716130360745235

theorem tailTrace_1570250 : CollatzResearch.WordTrace tailWord_1570250 prefixEnd_1570250 179176221716130360745235 := by
  unfold tailWord_1570250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317930640314975548605051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38181148374173268129613469 14317930640314975548605051)
  ·
    refine ⟨21476895960472463322907577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14317930640314975548605051 21476895960472463322907577)
    ·
      refine ⟨16107671970354347492180683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21476895960472463322907577 16107671970354347492180683)
      ·
        refine ⟨24161507955531521238271025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16107671970354347492180683 24161507955531521238271025)
        ·
          refine ⟨18121130966648640928703269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24161507955531521238271025 18121130966648640928703269)
          ·
            refine ⟨3397712056246620174131863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18121130966648640928703269 3397712056246620174131863)
            ·
              refine ⟨5096568084369930261197795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397712056246620174131863 5096568084369930261197795)
              ·
                refine ⟨7644852126554895391796693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096568084369930261197795 7644852126554895391796693)
                ·
                  refine ⟨179176221716130360745235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7644852126554895391796693 179176221716130360745235)
                  ·
                    rfl

theorem cell22_1570250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_1570250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570250 prefixEnd_1570250 := by exact prefixLift 1570250
  have htrace : WordTrace (prefixWord ++ tailWord_1570250) baseStart_1570250 baseEnd_1570250 := by
    simpa [prefixWord, tailWord_1570250, baseEnd_1570250] using wordTrace_append hprefix tailTrace_1570250
  have hstable : (prefixWord ++ tailWord_1570250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570250).length < 2 ^ (prefixWord ++ tailWord_1570250).sum := by decide
  have hdescent : baseEnd_1570250 < baseStart_1570250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570254 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_1570254 : Nat := 118140960795 + 1570254 * 2 ^ 59
def prefixEnd_1570254 : Nat := 4983230072969 + 3 ^ 40 * 1570254 * 2
def baseEnd_1570254 : Nat := 537530034430136405135693

theorem tailTrace_1570254 : CollatzResearch.WordTrace tailWord_1570254 prefixEnd_1570254 537530034430136405135693 := by
  unfold tailWord_1570254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158983556655676359695727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38181245635496940585043877 7158983556655676359695727)
  ·
    refine ⟨10738475334983514539543591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7158983556655676359695727 10738475334983514539543591)
    ·
      refine ⟨16107713002475271809315387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10738475334983514539543591 16107713002475271809315387)
      ·
        refine ⟨24161569503712907713973081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16107713002475271809315387 24161569503712907713973081)
        ·
          refine ⟨18121177127784680785479811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24161569503712907713973081 18121177127784680785479811)
          ·
            refine ⟨27181765691677021178219717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18121177127784680785479811 27181765691677021178219717)
            ·
              refine ⟨5096581067189441470916197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27181765691677021178219717 5096581067189441470916197)
              ·
                refine ⟨955608950098020275796787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5096581067189441470916197 955608950098020275796787)
                ·
                  refine ⟨1433413425147030413695181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955608950098020275796787 1433413425147030413695181)
                  ·
                    refine ⟨537530034430136405135693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433413425147030413695181 537530034430136405135693)
                    ·
                      rfl

theorem cell22_1570254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_1570254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570254 prefixEnd_1570254 := by exact prefixLift 1570254
  have htrace : WordTrace (prefixWord ++ tailWord_1570254) baseStart_1570254 baseEnd_1570254 := by
    simpa [prefixWord, tailWord_1570254, baseEnd_1570254] using wordTrace_append hprefix tailTrace_1570254
  have hstable : (prefixWord ++ tailWord_1570254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570254).length < 2 ^ (prefixWord ++ tailWord_1570254).sum := by decide
  have hdescent : baseEnd_1570254 < baseStart_1570254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570265 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_1570265 : Nat := 118140960795 + 1570265 * 2 ^ 59
def prefixEnd_1570265 : Nat := 4983230072969 + 3 ^ 40 * 1570265 * 2
def baseEnd_1570265 : Nat := 537533799954936043110659

theorem tailTrace_1570265 : CollatzResearch.WordTrace tailWord_1570265 prefixEnd_1570265 537533799954936043110659 := by
  unfold tailWord_1570265
  simp only [CollatzResearch.WordTrace]
  refine ⟨57272269656205559756216249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38181513104137039837477499 57272269656205559756216249)
  ·
    refine ⟨42954202242154169817162187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57272269656205559756216249 42954202242154169817162187)
    ·
      refine ⟨64431303363231254725743281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42954202242154169817162187 64431303363231254725743281)
      ·
        refine ⟨48323477522423441044307461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64431303363231254725743281 48323477522423441044307461)
        ·
          refine ⟨9060652035454395195807649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48323477522423441044307461 9060652035454395195807649)
          ·
            refine ⟨6795489026590796396855737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9060652035454395195807649 6795489026590796396855737)
            ·
              refine ⟨5096616769943097297641803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6795489026590796396855737 5096616769943097297641803)
              ·
                refine ⟨7644925154914645946462705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096616769943097297641803 7644925154914645946462705)
                ·
                  refine ⟨5733693866185984459847029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7644925154914645946462705 5733693866185984459847029)
                  ·
                    refine ⟨537533799954936043110659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5733693866185984459847029 537533799954936043110659)
                    ·
                      rfl

theorem cell22_1570265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_1570265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570265 prefixEnd_1570265 := by exact prefixLift 1570265
  have htrace : WordTrace (prefixWord ++ tailWord_1570265) baseStart_1570265 baseEnd_1570265 := by
    simpa [prefixWord, tailWord_1570265, baseEnd_1570265] using wordTrace_append hprefix tailTrace_1570265
  have hstable : (prefixWord ++ tailWord_1570265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570265).length < 2 ^ (prefixWord ++ tailWord_1570265).sum := by decide
  have hdescent : baseEnd_1570265 < baseStart_1570265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570312 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 4]
def baseStart_1570312 : Nat := 118140960795 + 1570312 * 2 ^ 59
def prefixEnd_1570312 : Nat := 4983230072969 + 3 ^ 40 * 1570312 * 2
def baseEnd_1570312 : Nat := 179183296338481195728505

theorem tailTrace_1570312 : CollatzResearch.WordTrace tailWord_1570312 prefixEnd_1570312 179183296338481195728505 := by
  unfold tailWord_1570312
  simp only [CollatzResearch.WordTrace]
  refine ⟨28636991943517643391588595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38182655924690191188784793 28636991943517643391588595)
  ·
    refine ⟨42955487915276465087382893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28636991943517643391588595 42955487915276465087382893)
    ·
      refine ⟨16108307968228674407768585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42955487915276465087382893 16108307968228674407768585)
      ·
        refine ⟨12081230976171505805826439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16108307968228674407768585 12081230976171505805826439)
        ·
          refine ⟨18121846464257258708739659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12081230976171505805826439 18121846464257258708739659)
          ·
            refine ⟨27182769696385888063109489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18121846464257258708739659 27182769696385888063109489)
            ·
              refine ⟨20387077272289416047332117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27182769696385888063109489 20387077272289416047332117)
              ·
                refine ⟨955644247138566377218693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20387077272289416047332117 955644247138566377218693)
                ·
                  refine ⟨179183296338481195728505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955644247138566377218693 179183296338481195728505)
                  ·
                    rfl

theorem cell22_1570312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_1570312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570312 prefixEnd_1570312 := by exact prefixLift 1570312
  have htrace : WordTrace (prefixWord ++ tailWord_1570312) baseStart_1570312 baseEnd_1570312 := by
    simpa [prefixWord, tailWord_1570312, baseEnd_1570312] using wordTrace_append hprefix tailTrace_1570312
  have hstable : (prefixWord ++ tailWord_1570312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570312).length < 2 ^ (prefixWord ++ tailWord_1570312).sum := by decide
  have hdescent : baseEnd_1570312 < baseStart_1570312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570344 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1570344 : Nat := 118140960795 + 1570344 * 2 ^ 59
def prefixEnd_1570344 : Nat := 4983230072969 + 3 ^ 40 * 1570344 * 2
def baseEnd_1570344 : Nat := 537560843269406170385417

theorem tailTrace_1570344 : CollatzResearch.WordTrace tailWord_1570344 prefixEnd_1570344 537560843269406170385417 := by
  unfold tailWord_1570344
  simp only [CollatzResearch.WordTrace]
  refine ⟨28637575511459678124171043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38183434015279570832228057 28637575511459678124171043)
  ·
    refine ⟨42956363267189517186256565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28637575511459678124171043 42956363267189517186256565)
    ·
      refine ⟨4027159056299017236211553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42956363267189517186256565 4027159056299017236211553)
      ·
        refine ⟨3020369292224262927158665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4027159056299017236211553 3020369292224262927158665)
        ·
          refine ⟨2265276969168197195368999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3020369292224262927158665 2265276969168197195368999)
          ·
            refine ⟨3397915453752295793053499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265276969168197195368999 3397915453752295793053499)
            ·
              refine ⟨5096873180628443689580249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397915453752295793053499 5096873180628443689580249)
              ·
                refine ⟨3822654885471332767185187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5096873180628443689580249 3822654885471332767185187)
                ·
                  refine ⟨5733982328206999150777781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822654885471332767185187 5733982328206999150777781)
                  ·
                    refine ⟨537560843269406170385417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5733982328206999150777781 537560843269406170385417)
                    ·
                      rfl

theorem cell22_1570344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1570344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570344 prefixEnd_1570344 := by exact prefixLift 1570344
  have htrace : WordTrace (prefixWord ++ tailWord_1570344) baseStart_1570344 baseEnd_1570344 := by
    simpa [prefixWord, tailWord_1570344, baseEnd_1570344] using wordTrace_append hprefix tailTrace_1570344
  have hstable : (prefixWord ++ tailWord_1570344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570344).length < 2 ^ (prefixWord ++ tailWord_1570344).sum := by decide
  have hdescent : baseEnd_1570344 < baseStart_1570344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570400 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_1570400 : Nat := 118140960795 + 1570400 * 2 ^ 59
def prefixEnd_1570400 : Nat := 4983230072969 + 3 ^ 40 * 1570400 * 2
def baseEnd_1570400 : Nat := 537580013213840690985245

theorem tailTrace_1570400 : CollatzResearch.WordTrace tailWord_1570400 prefixEnd_1570400 537580013213840690985245 := by
  unfold tailWord_1570400
  simp only [CollatzResearch.WordTrace]
  refine ⟨28638596755358238906190327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38184795673810985208253769 28638596755358238906190327)
  ·
    refine ⟨42957895133037358359285491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28638596755358238906190327 42957895133037358359285491)
    ·
      refine ⟨64436842699556037538928237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42957895133037358359285491 64436842699556037538928237)
      ·
        refine ⟨24163816012333514077098089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64436842699556037538928237 24163816012333514077098089)
        ·
          refine ⟨18122862009250135557823567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24163816012333514077098089 18122862009250135557823567)
          ·
            refine ⟨27184293013875203336735351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18122862009250135557823567 27184293013875203336735351)
            ·
              refine ⟨40776439520812805005103027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27184293013875203336735351 40776439520812805005103027)
              ·
                refine ⟨61164659281219207507654541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40776439520812805005103027 61164659281219207507654541)
                ·
                  refine ⟨22936747230457202815370453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61164659281219207507654541 22936747230457202815370453)
                  ·
                    refine ⟨537580013213840690985245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22936747230457202815370453 537580013213840690985245)
                    ·
                      rfl

theorem cell22_1570400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_1570400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570400 prefixEnd_1570400 := by exact prefixLift 1570400
  have htrace : WordTrace (prefixWord ++ tailWord_1570400) baseStart_1570400 baseEnd_1570400 := by
    simpa [prefixWord, tailWord_1570400, baseEnd_1570400] using wordTrace_append hprefix tailTrace_1570400
  have hstable : (prefixWord ++ tailWord_1570400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570400).length < 2 ^ (prefixWord ++ tailWord_1570400).sum := by decide
  have hdescent : baseEnd_1570400 < baseStart_1570400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570436 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1570436 : Nat := 118140960795 + 1570436 * 2 ^ 59
def prefixEnd_1570436 : Nat := 4983230072969 + 3 ^ 40 * 1570436 * 2
def baseEnd_1570436 : Nat := 179197445583182865695045

theorem tailTrace_1570436 : CollatzResearch.WordTrace tailWord_1570436 prefixEnd_1570436 179197445583182865695045 := by
  unfold tailWord_1570436
  simp only [CollatzResearch.WordTrace]
  refine ⟨28639253269293027980345581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38185671025724037307127441 28639253269293027980345581)
  ·
    refine ⟨10739719975984885492629593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28639253269293027980345581 10739719975984885492629593)
    ·
      refine ⟨8054789981988664119472195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10739719975984885492629593 8054789981988664119472195)
      ·
        refine ⟨12082184972982996179208293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8054789981988664119472195 12082184972982996179208293)
        ·
          refine ⟨2265409682434311783601555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12082184972982996179208293 2265409682434311783601555)
          ·
            refine ⟨3398114523651467675402333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265409682434311783601555 3398114523651467675402333)
            ·
              refine ⟨1274292946369300378275875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3398114523651467675402333 1274292946369300378275875)
              ·
                refine ⟨1911439419553950567413813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274292946369300378275875 1911439419553950567413813)
                ·
                  refine ⟨179197445583182865695045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1911439419553950567413813 179197445583182865695045)
                  ·
                    rfl

theorem cell22_1570436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1570436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570436 prefixEnd_1570436 := by exact prefixLift 1570436
  have htrace : WordTrace (prefixWord ++ tailWord_1570436) baseStart_1570436 baseEnd_1570436 := by
    simpa [prefixWord, tailWord_1570436, baseEnd_1570436] using wordTrace_append hprefix tailTrace_1570436
  have hstable : (prefixWord ++ tailWord_1570436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570436).length < 2 ^ (prefixWord ++ tailWord_1570436).sum := by decide
  have hdescent : baseEnd_1570436 < baseStart_1570436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570479 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 2, 3]
def baseStart_1570479 : Nat := 118140960795 + 1570479 * 2 ^ 59
def prefixEnd_1570479 : Nat := 4983230072969 + 3 ^ 40 * 1570479 * 2
def baseEnd_1570479 : Nat := 537607056528310818260003

theorem tailTrace_1570479 : CollatzResearch.WordTrace tailWord_1570479 prefixEnd_1570479 537607056528310818260003 := by
  unfold tailWord_1570479
  simp only [CollatzResearch.WordTrace]
  refine ⟨57280074877430274304506491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38186716584953516203004327 57280074877430274304506491)
  ·
    refine ⟨85920112316145411456759737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57280074877430274304506491 85920112316145411456759737)
    ·
      refine ⟨64440084237109058592569803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85920112316145411456759737 64440084237109058592569803)
      ·
        refine ⟨96660126355663587888854705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64440084237109058592569803 96660126355663587888854705)
        ·
          refine ⟨72495094766747690916641029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96660126355663587888854705 72495094766747690916641029)
          ·
            refine ⟨13592830268765192046870193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72495094766747690916641029 13592830268765192046870193)
            ·
              refine ⟨10194622701573894035152645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13592830268765192046870193 10194622701573894035152645)
              ·
                refine ⟨1911491756545105131591121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10194622701573894035152645 1911491756545105131591121)
                ·
                  refine ⟨1433618817408828848693341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1911491756545105131591121 1433618817408828848693341)
                  ·
                    refine ⟨537607056528310818260003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433618817408828848693341 537607056528310818260003)
                    ·
                      rfl

theorem cell22_1570479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_1570479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570479 prefixEnd_1570479 := by exact prefixLift 1570479
  have htrace : WordTrace (prefixWord ++ tailWord_1570479) baseStart_1570479 baseEnd_1570479 := by
    simpa [prefixWord, tailWord_1570479, baseEnd_1570479] using wordTrace_append hprefix tailTrace_1570479
  have hstable : (prefixWord ++ tailWord_1570479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570479).length < 2 ^ (prefixWord ++ tailWord_1570479).sum := by decide
  have hdescent : baseEnd_1570479 < baseStart_1570479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570492 : List Nat := [2, 2, 2, 3, 1, 2, 1, 9]
def baseStart_1570492 : Nat := 118140960795 + 1570492 * 2 ^ 59
def prefixEnd_1570492 : Nat := 4983230072969 + 3 ^ 40 * 1570492 * 2
def baseEnd_1570492 : Nat := 59734611854887013076107

theorem tailTrace_1570492 : CollatzResearch.WordTrace tailWord_1570492 prefixEnd_1570492 59734611854887013076107 := by
  unfold tailWord_1570492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640274513191588762364865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38187032684255451683153153 28640274513191588762364865)
  ·
    refine ⟨21480205884893691571773649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28640274513191588762364865 21480205884893691571773649)
    ·
      refine ⟨16110154413670268678830237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21480205884893691571773649 16110154413670268678830237)
      ·
        refine ⟨6041307905126350754561339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16110154413670268678830237 6041307905126350754561339)
        ·
          refine ⟨9061961857689526131842009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041307905126350754561339 9061961857689526131842009)
          ·
            refine ⟨6796471393267144598881507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9061961857689526131842009 6796471393267144598881507)
            ·
              refine ⟨10194707089900716898322261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796471393267144598881507 10194707089900716898322261)
              ·
                refine ⟨59734611854887013076107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10194707089900716898322261 59734611854887013076107)
                ·
                  rfl

theorem cell22_1570492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_1570492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570492 prefixEnd_1570492 := by exact prefixLift 1570492
  have htrace : WordTrace (prefixWord ++ tailWord_1570492) baseStart_1570492 baseEnd_1570492 := by
    simpa [prefixWord, tailWord_1570492, baseEnd_1570492] using wordTrace_append hprefix tailTrace_1570492
  have hstable : (prefixWord ++ tailWord_1570492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570492).length < 2 ^ (prefixWord ++ tailWord_1570492).sum := by decide
  have hdescent : baseEnd_1570492 < baseStart_1570492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
