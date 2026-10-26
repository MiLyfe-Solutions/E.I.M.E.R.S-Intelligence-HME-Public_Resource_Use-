import V185TrunkScan23Chunk1380

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8179655 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 9]
def baseStart_8179655 : Nat := 118140960795 + 8179655 * 2 ^ 59
def prefixEnd_8179655 : Nat := 4983230072969 + 3 ^ 40 * 8179655 * 2
def baseEnd_8179655 : Nat := 466677178105811088432773

theorem tailTrace_8179655 : CollatzResearch.WordTrace tailWord_8179655 prefixEnd_8179655 466677178105811088432773 := by
  unfold tailWord_8179655
  simp only [CollatzResearch.WordTrace]
  refine ⟨298336527181514383700340419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198891018121009589133560279 298336527181514383700340419)
  ·
    refine ⟨447504790772271575550510629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298336527181514383700340419 447504790772271575550510629)
    ·
      refine ⟨83907148269800920415720743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447504790772271575550510629 83907148269800920415720743)
      ·
        refine ⟨125860722404701380623581115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83907148269800920415720743 125860722404701380623581115)
        ·
          refine ⟨188791083607052070935371673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125860722404701380623581115 188791083607052070935371673)
          ·
            refine ⟨141593312705289053201528755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188791083607052070935371673 141593312705289053201528755)
            ·
              refine ⟨212389969057933579802293133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141593312705289053201528755 212389969057933579802293133)
              ·
                refine ⟨79646238396725092425859925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212389969057933579802293133 79646238396725092425859925)
                ·
                  refine ⟨466677178105811088432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79646238396725092425859925 466677178105811088432773)
                  ·
                    rfl

theorem cell23_8179655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 9].length) (baseStart_8179655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179655 prefixEnd_8179655 := by exact prefixLift 8179655
  have htrace : WordTrace (prefixWord ++ tailWord_8179655) baseStart_8179655 baseEnd_8179655 := by
    simpa [prefixWord, tailWord_8179655, baseEnd_8179655] using wordTrace_append hprefix tailTrace_8179655
  have hstable : (prefixWord ++ tailWord_8179655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179655).length < 2 ^ (prefixWord ++ tailWord_8179655).sum := by decide
  have hdescent : baseEnd_8179655 < baseStart_8179655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179665 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_8179665 : Nat := 118140960795 + 8179665 * 2 ^ 59
def prefixEnd_8179665 : Nat := 4983230072969 + 3 ^ 40 * 8179665 * 2
def baseEnd_8179665 : Nat := 4200099737758844756769911

theorem tailTrace_8179665 : CollatzResearch.WordTrace tailWord_8179665 prefixEnd_8179665 4200099737758844756769911 := by
  unfold tailWord_8179665
  simp only [CollatzResearch.WordTrace]
  refine ⟨298336891911478155408204449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198891261274318770272136299 298336891911478155408204449)
  ·
    refine ⟨223752668933608616556153337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298336891911478155408204449 223752668933608616556153337)
    ·
      refine ⟨167814501700206462417115003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223752668933608616556153337 167814501700206462417115003)
      ·
        refine ⟨251721752550309693625672505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167814501700206462417115003 251721752550309693625672505)
        ·
          refine ⟨188791314412732270219254379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251721752550309693625672505 188791314412732270219254379)
          ·
            refine ⟨283186971619098405328881569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188791314412732270219254379 283186971619098405328881569)
            ·
              refine ⟨212390228714323803996661177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283186971619098405328881569 212390228714323803996661177)
              ·
                refine ⟨159292671535742852997495883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212390228714323803996661177 159292671535742852997495883)
                ·
                  refine ⟨238939007303614279496243825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159292671535742852997495883 238939007303614279496243825)
                  ·
                    refine ⟨179204255477710709622182869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238939007303614279496243825 179204255477710709622182869)
                    ·
                      refine ⟨4200099737758844756769911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179204255477710709622182869 4200099737758844756769911)
                      ·
                        rfl

theorem cell23_8179665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_8179665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179665 prefixEnd_8179665 := by exact prefixLift 8179665
  have htrace : WordTrace (prefixWord ++ tailWord_8179665) baseStart_8179665 baseEnd_8179665 := by
    simpa [prefixWord, tailWord_8179665, baseEnd_8179665] using wordTrace_append hprefix tailTrace_8179665
  have hstable : (prefixWord ++ tailWord_8179665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179665).length < 2 ^ (prefixWord ++ tailWord_8179665).sum := by decide
  have hdescent : baseEnd_8179665 < baseStart_8179665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179683 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 2, 2, 2]
def baseStart_8179683 : Nat := 118140960795 + 8179683 * 2 ^ 59
def prefixEnd_8179683 : Nat := 4983230072969 + 3 ^ 40 * 8179683 * 2
def baseEnd_8179683 : Nat := 4200108980410625686344829

theorem tailTrace_8179683 : CollatzResearch.WordTrace tailWord_8179683 prefixEnd_8179683 4200108980410625686344829 := by
  unfold tailWord_8179683
  simp only [CollatzResearch.WordTrace]
  refine ⟨298337548425412944482359703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198891698950275296321573135 298337548425412944482359703)
  ·
    refine ⟨447506322638119416723539555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298337548425412944482359703 447506322638119416723539555)
    ·
      refine ⟨671259483957179125085309333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447506322638119416723539555 671259483957179125085309333)
      ·
        refine ⟨31465288310492771488373875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 671259483957179125085309333 31465288310492771488373875)
        ·
          refine ⟨47197932465739157232560813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465288310492771488373875 47197932465739157232560813)
          ·
            refine ⟨17699224674652183962210305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47197932465739157232560813 17699224674652183962210305)
            ·
              refine ⟨13274418505989137971657729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17699224674652183962210305 13274418505989137971657729)
              ·
                refine ⟨9955813879491853478743297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274418505989137971657729 9955813879491853478743297)
                ·
                  refine ⟨7466860409618890109057473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9955813879491853478743297 7466860409618890109057473)
                  ·
                    refine ⟨5600145307214167581793105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7466860409618890109057473 5600145307214167581793105)
                    ·
                      refine ⟨4200108980410625686344829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600145307214167581793105 4200108980410625686344829)
                      ·
                        rfl

theorem cell23_8179683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_8179683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179683 prefixEnd_8179683 := by exact prefixLift 8179683
  have htrace : WordTrace (prefixWord ++ tailWord_8179683) baseStart_8179683 baseEnd_8179683 := by
    simpa [prefixWord, tailWord_8179683, baseEnd_8179683] using wordTrace_append hprefix tailTrace_8179683
  have hstable : (prefixWord ++ tailWord_8179683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179683).length < 2 ^ (prefixWord ++ tailWord_8179683).sum := by decide
  have hdescent : baseEnd_8179683 < baseStart_8179683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179719 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 2, 5]
def baseStart_8179719 : Nat := 118140960795 + 8179719 * 2 ^ 59
def prefixEnd_8179719 : Nat := 4983230072969 + 3 ^ 40 * 8179719 * 2
def baseEnd_8179719 : Nat := 1400042488571395848498221

theorem tailTrace_8179719 : CollatzResearch.WordTrace tailWord_8179719 prefixEnd_8179719 1400042488571395848498221 := by
  unfold tailWord_8179719
  simp only [CollatzResearch.WordTrace]
  refine ⟨298338861453282522630670211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198892574302188348420446807 298338861453282522630670211)
  ·
    refine ⟨447508292179923783946005317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298338861453282522630670211 447508292179923783946005317)
    ·
      refine ⟨83907804783735709489875997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447508292179923783946005317 83907804783735709489875997)
      ·
        refine ⟨31465426793900891058703499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83907804783735709489875997 31465426793900891058703499)
        ·
          refine ⟨47198140190851336588055249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465426793900891058703499 47198140190851336588055249)
          ·
            refine ⟨35398605143138502441041437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47198140190851336588055249 35398605143138502441041437)
            ·
              refine ⟨13274476928676938415390539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35398605143138502441041437 13274476928676938415390539)
              ·
                refine ⟨19911715393015407623085809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13274476928676938415390539 19911715393015407623085809)
                ·
                  refine ⟨14933786544761555717314357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19911715393015407623085809 14933786544761555717314357)
                  ·
                    refine ⟨1400042488571395848498221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14933786544761555717314357 1400042488571395848498221)
                    ·
                      rfl

theorem cell23_8179719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_8179719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179719 prefixEnd_8179719 := by exact prefixLift 8179719
  have htrace : WordTrace (prefixWord ++ tailWord_8179719) baseStart_8179719 baseEnd_8179719 := by
    simpa [prefixWord, tailWord_8179719, baseEnd_8179719] using wordTrace_append hprefix tailTrace_8179719
  have hstable : (prefixWord ++ tailWord_8179719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179719).length < 2 ^ (prefixWord ++ tailWord_8179719).sum := by decide
  have hdescent : baseEnd_8179719 < baseStart_8179719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179749 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_8179749 : Nat := 118140960795 + 8179749 * 2 ^ 59
def prefixEnd_8179749 : Nat := 4983230072969 + 3 ^ 40 * 8179749 * 2
def baseEnd_8179749 : Nat := 1400047623377940809373175

theorem tailTrace_8179749 : CollatzResearch.WordTrace tailWord_8179749 prefixEnd_8179749 1400047623377940809373175 := by
  unfold tailWord_8179749
  simp only [CollatzResearch.WordTrace]
  refine ⟨298339955643173837754262301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198893303762115891836174867 298339955643173837754262301)
  ·
    refine ⟨111877483366190189157848363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298339955643173837754262301 111877483366190189157848363)
    ·
      refine ⟨167816225049285283736772545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111877483366190189157848363 167816225049285283736772545)
      ·
        refine ⟨125862168786963962802579409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167816225049285283736772545 125862168786963962802579409)
        ·
          refine ⟨94396626590222972101934557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125862168786963962802579409 94396626590222972101934557)
          ·
            refine ⟨35398734971333614538225459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94396626590222972101934557 35398734971333614538225459)
            ·
              refine ⟨53098102457000421807338189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35398734971333614538225459 53098102457000421807338189)
              ·
                refine ⟨19911788421375158177751821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53098102457000421807338189 19911788421375158177751821)
                ·
                  refine ⟨7466920658015684316656933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19911788421375158177751821 7466920658015684316656933)
                  ·
                    refine ⟨1400047623377940809373175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466920658015684316656933 1400047623377940809373175)
                    ·
                      rfl

theorem cell23_8179749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_8179749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179749 prefixEnd_8179749 := by exact prefixLift 8179749
  have htrace : WordTrace (prefixWord ++ tailWord_8179749) baseStart_8179749 baseEnd_8179749 := by
    simpa [prefixWord, tailWord_8179749, baseEnd_8179749] using wordTrace_append hprefix tailTrace_8179749
  have hstable : (prefixWord ++ tailWord_8179749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179749).length < 2 ^ (prefixWord ++ tailWord_8179749).sum := by decide
  have hdescent : baseEnd_8179749 < baseStart_8179749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179766 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_8179766 : Nat := 118140960795 + 8179766 * 2 ^ 59
def prefixEnd_8179766 : Nat := 4983230072969 + 3 ^ 40 * 8179766 * 2
def baseEnd_8179766 : Nat := 1400050533101649620535649

theorem tailTrace_8179766 : CollatzResearch.WordTrace tailWord_8179766 prefixEnd_8179766 1400050533101649620535649 := by
  unfold tailWord_8179766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646285980257015603601947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198893717122741499771754101 18646285980257015603601947)
  ·
    refine ⟨27969428970385523405402921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18646285980257015603601947 27969428970385523405402921)
    ·
      refine ⟨20977071727789142554052191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27969428970385523405402921 20977071727789142554052191)
      ·
        refine ⟨31465607591683713831078287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20977071727789142554052191 31465607591683713831078287)
        ·
          refine ⟨47198411387525570746617431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465607591683713831078287 47198411387525570746617431)
          ·
            refine ⟨70797617081288356119926147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47198411387525570746617431 70797617081288356119926147)
            ·
              refine ⟨106196425621932534179889221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70797617081288356119926147 106196425621932534179889221)
              ·
                refine ⟨19911829804112350158729229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106196425621932534179889221 19911829804112350158729229)
                ·
                  refine ⟨7466936176542131309523461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19911829804112350158729229 7466936176542131309523461)
                  ·
                    refine ⟨1400050533101649620535649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466936176542131309523461 1400050533101649620535649)
                    ·
                      rfl

theorem cell23_8179766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_8179766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179766 prefixEnd_8179766 := by exact prefixLift 8179766
  have htrace : WordTrace (prefixWord ++ tailWord_8179766) baseStart_8179766 baseEnd_8179766 := by
    simpa [prefixWord, tailWord_8179766, baseEnd_8179766] using wordTrace_append hprefix tailTrace_8179766
  have hstable : (prefixWord ++ tailWord_8179766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179766).length < 2 ^ (prefixWord ++ tailWord_8179766).sum := by decide
  have hdescent : baseEnd_8179766 < baseStart_8179766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179792 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_8179792 : Nat := 118140960795 + 8179792 * 2 ^ 59
def prefixEnd_8179792 : Nat := 4983230072969 + 3 ^ 40 * 8179792 * 2
def baseEnd_8179792 : Nat := 1400054983267321919960609

theorem tailTrace_8179792 : CollatzResearch.WordTrace tailWord_8179792 prefixEnd_8179792 1400054983267321919960609 := by
  unfold tailWord_8179792
  simp only [CollatzResearch.WordTrace]
  refine ⟨149170761991009028049038815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198894349321345370732051753 149170761991009028049038815)
  ·
    refine ⟨223756142986513542073558223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149170761991009028049038815 223756142986513542073558223)
    ·
      refine ⟨335634214479770313110337335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223756142986513542073558223 335634214479770313110337335)
      ·
        refine ⟨503451321719655469665506003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335634214479770313110337335 503451321719655469665506003)
        ·
          refine ⟨755176982579483204498259005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503451321719655469665506003 755176982579483204498259005)
          ·
            refine ⟨283191368467306201686847127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 755176982579483204498259005 283191368467306201686847127)
            ·
              refine ⟨424787052700959302530270691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283191368467306201686847127 424787052700959302530270691)
              ·
                refine ⟨637180579051438953795406037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424787052700959302530270691 637180579051438953795406037)
                ·
                  refine ⟨14933919821518100479579829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 637180579051438953795406037 14933919821518100479579829)
                  ·
                    refine ⟨1400054983267321919960609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14933919821518100479579829 1400054983267321919960609)
                    ·
                      rfl

theorem cell23_8179792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_8179792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179792 prefixEnd_8179792 := by exact prefixLift 8179792
  have htrace : WordTrace (prefixWord ++ tailWord_8179792) baseStart_8179792 baseEnd_8179792 := by
    simpa [prefixWord, tailWord_8179792, baseEnd_8179792] using wordTrace_append hprefix tailTrace_8179792
  have hstable : (prefixWord ++ tailWord_8179792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179792).length < 2 ^ (prefixWord ++ tailWord_8179792).sum := by decide
  have hdescent : baseEnd_8179792 < baseStart_8179792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179826 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_8179826 : Nat := 118140960795 + 8179826 * 2 ^ 59
def prefixEnd_8179826 : Nat := 4983230072969 + 3 ^ 40 * 8179826 * 2
def baseEnd_8179826 : Nat := 1400060802714739542285557

theorem tailTrace_8179826 : CollatzResearch.WordTrace tailWord_8179826 prefixEnd_8179826 1400060802714739542285557 := by
  unfold tailWord_8179826
  simp only [CollatzResearch.WordTrace]
  refine ⟨74585691015973719976203833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198895176042596586603210221 74585691015973719976203833)
  ·
    refine ⟨55939268261980289982152875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74585691015973719976203833 55939268261980289982152875)
    ·
      refine ⟨83908902392970434973229313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55939268261980289982152875 83908902392970434973229313)
      ·
        refine ⟨62931676794727826229921985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83908902392970434973229313 62931676794727826229921985)
        ·
          refine ⟨47198757596045869672441489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62931676794727826229921985 47198757596045869672441489)
          ·
            refine ⟨35399068197034402254331117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47198757596045869672441489 35399068197034402254331117)
            ·
              refine ⟨13274650573887900845374169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35399068197034402254331117 13274650573887900845374169)
              ·
                refine ⟨9955987930415925634030627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274650573887900845374169 9955987930415925634030627)
                ·
                  refine ⟨14933981895623888451045941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955987930415925634030627 14933981895623888451045941)
                  ·
                    refine ⟨1400060802714739542285557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14933981895623888451045941 1400060802714739542285557)
                    ·
                      rfl

theorem cell23_8179826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_8179826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179826 prefixEnd_8179826 := by exact prefixLift 8179826
  have htrace : WordTrace (prefixWord ++ tailWord_8179826) baseStart_8179826 baseEnd_8179826 := by
    simpa [prefixWord, tailWord_8179826, baseEnd_8179826] using wordTrace_append hprefix tailTrace_8179826
  have hstable : (prefixWord ++ tailWord_8179826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179826).length < 2 ^ (prefixWord ++ tailWord_8179826).sum := by decide
  have hdescent : baseEnd_8179826 < baseStart_8179826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179833 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 2, 3, 2]
def baseStart_8179833 : Nat := 118140960795 + 8179833 * 2 ^ 59
def prefixEnd_8179833 : Nat := 4983230072969 + 3 ^ 40 * 8179833 * 2
def baseEnd_8179833 : Nat := 4200186002508800099469139

theorem tailTrace_8179833 : CollatzResearch.WordTrace tailWord_8179833 prefixEnd_8179833 4200186002508800099469139 := by
  unfold tailWord_8179833
  simp only [CollatzResearch.WordTrace]
  refine ⟨298343019374869520100320153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198895346249913013400213435 298343019374869520100320153)
  ·
    refine ⟨223757264531152140075240115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298343019374869520100320153 223757264531152140075240115)
    ·
      refine ⟨335635896796728210112860173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223757264531152140075240115 335635896796728210112860173)
      ·
        refine ⟨125863461298773078792322565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335635896796728210112860173 125863461298773078792322565)
        ·
          refine ⟨23599398993519952273560481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125863461298773078792322565 23599398993519952273560481)
          ·
            refine ⟨17699549245139964205170361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23599398993519952273560481 17699549245139964205170361)
            ·
              refine ⟨13274661933854973153877771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17699549245139964205170361 13274661933854973153877771)
              ·
                refine ⟨19911992900782459730816657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13274661933854973153877771 19911992900782459730816657)
                ·
                  refine ⟨14933994675586844798112493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19911992900782459730816657 14933994675586844798112493)
                  ·
                    refine ⟨5600248003345066799292185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14933994675586844798112493 5600248003345066799292185)
                    ·
                      refine ⟨4200186002508800099469139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600248003345066799292185 4200186002508800099469139)
                      ·
                        rfl

theorem cell23_8179833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_8179833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179833 prefixEnd_8179833 := by exact prefixLift 8179833
  have htrace : WordTrace (prefixWord ++ tailWord_8179833) baseStart_8179833 baseEnd_8179833 := by
    simpa [prefixWord, tailWord_8179833, baseEnd_8179833] using wordTrace_append hprefix tailTrace_8179833
  have hstable : (prefixWord ++ tailWord_8179833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179833).length < 2 ^ (prefixWord ++ tailWord_8179833).sum := by decide
  have hdescent : baseEnd_8179833 < baseStart_8179833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179856 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 2, 4]
def baseStart_8179856 : Nat := 118140960795 + 8179856 * 2 ^ 59
def prefixEnd_8179856 : Nat := 4983230072969 + 3 ^ 40 * 8179856 * 2
def baseEnd_8179856 : Nat := 1400065937521284503160511

theorem tailTrace_8179856 : CollatzResearch.WordTrace tailWord_8179856 prefixEnd_8179856 1400065937521284503160511 := by
  unfold tailWord_8179856
  simp only [CollatzResearch.WordTrace]
  refine ⟨149171929126893097514203711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198895905502524130018938281 149171929126893097514203711)
  ·
    refine ⟨223757893690339646271305567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149171929126893097514203711 223757893690339646271305567)
    ·
      refine ⟨335636840535509469406958351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223757893690339646271305567 335636840535509469406958351)
      ·
        refine ⟨503455260803264204110437527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335636840535509469406958351 503455260803264204110437527)
        ·
          refine ⟨755182891204896306165656291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503455260803264204110437527 755182891204896306165656291)
          ·
            refine ⟨1132774336807344459248484437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755182891204896306165656291 1132774336807344459248484437)
            ·
              refine ⟨13274699259461067881818177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1132774336807344459248484437 13274699259461067881818177)
              ·
                refine ⟨9956024444595800911363633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274699259461067881818177 9956024444595800911363633)
                ·
                  refine ⟨7467018333446850683522725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9956024444595800911363633 7467018333446850683522725)
                  ·
                    refine ⟨1400065937521284503160511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467018333446850683522725 1400065937521284503160511)
                    ·
                      rfl

theorem cell23_8179856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_8179856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179856 prefixEnd_8179856 := by exact prefixLift 8179856
  have htrace : WordTrace (prefixWord ++ tailWord_8179856) baseStart_8179856 baseEnd_8179856 := by
    simpa [prefixWord, tailWord_8179856, baseEnd_8179856] using wordTrace_append hprefix tailTrace_8179856
  have hstable : (prefixWord ++ tailWord_8179856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179856).length < 2 ^ (prefixWord ++ tailWord_8179856).sum := by decide
  have hdescent : baseEnd_8179856 < baseStart_8179856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179869 : List Nat := [1, 4, 2, 1, 1, 3, 3, 8]
def baseStart_8179869 : Nat := 118140960795 + 8179869 * 2 ^ 59
def prefixEnd_8179869 : Nat := 4983230072969 + 3 ^ 40 * 8179869 * 2
def baseEnd_8179869 : Nat := 155563129178235628096999

theorem tailTrace_8179869 : CollatzResearch.WordTrace tailWord_8179869 prefixEnd_8179869 155563129178235628096999 := by
  unfold tailWord_8179869
  simp only [CollatzResearch.WordTrace]
  refine ⟨298344332402739098248630661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198896221601826065499087107 298344332402739098248630661)
  ·
    refine ⟨55939562325513580921618249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298344332402739098248630661 55939562325513580921618249)
    ·
      refine ⟨41954671744135185691213687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55939562325513580921618249 41954671744135185691213687)
      ·
        refine ⟨62932007616202778536820531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41954671744135185691213687 62932007616202778536820531)
        ·
          refine ⟨94398011424304167805230797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62932007616202778536820531 94398011424304167805230797)
          ·
            refine ⟨35399254284114062926961549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94398011424304167805230797 35399254284114062926961549)
            ·
              refine ⟨13274720356542773597610581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35399254284114062926961549 13274720356542773597610581)
              ·
                refine ⟨155563129178235628096999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13274720356542773597610581 155563129178235628096999)
                ·
                  rfl

theorem cell23_8179869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 8].length) (baseStart_8179869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179869 prefixEnd_8179869 := by exact prefixLift 8179869
  have htrace : WordTrace (prefixWord ++ tailWord_8179869) baseStart_8179869 baseEnd_8179869 := by
    simpa [prefixWord, tailWord_8179869, baseEnd_8179869] using wordTrace_append hprefix tailTrace_8179869
  have hstable : (prefixWord ++ tailWord_8179869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179869).length < 2 ^ (prefixWord ++ tailWord_8179869).sum := by decide
  have hdescent : baseEnd_8179869 < baseStart_8179869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179896 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_8179896 : Nat := 118140960795 + 8179896 * 2 ^ 59
def prefixEnd_8179896 : Nat := 4983230072969 + 3 ^ 40 * 8179896 * 2
def baseEnd_8179896 : Nat := 4200218351790033352981349

theorem tailTrace_8179896 : CollatzResearch.WordTrace tailWord_8179896 prefixEnd_8179896 4200218351790033352981349 := by
  unfold tailWord_8179896
  simp only [CollatzResearch.WordTrace]
  refine ⟨149172658586820640929931771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198896878115760854573242361 149172658586820640929931771)
  ·
    refine ⟨223758987880230961394897657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149172658586820640929931771 223758987880230961394897657)
    ·
      refine ⟨167819240910173221046173243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223758987880230961394897657 167819240910173221046173243)
      ·
        refine ⟨251728861365259831569259865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167819240910173221046173243 251728861365259831569259865)
        ·
          refine ⟨188796646023944873676944899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251728861365259831569259865 188796646023944873676944899)
          ·
            refine ⟨283194969035917310515417349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188796646023944873676944899 283194969035917310515417349)
            ·
              refine ⟨53099056694234495721640753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283194969035917310515417349 53099056694234495721640753)
              ·
                refine ⟨39824292520675871791230565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53099056694234495721640753 39824292520675871791230565)
                ·
                  refine ⟨7467054847626725960855731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39824292520675871791230565 7467054847626725960855731)
                  ·
                    refine ⟨11200582271440088941283597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7467054847626725960855731 11200582271440088941283597)
                    ·
                      refine ⟨4200218351790033352981349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11200582271440088941283597 4200218351790033352981349)
                      ·
                        rfl

theorem cell23_8179896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_8179896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179896 prefixEnd_8179896 := by exact prefixLift 8179896
  have htrace : WordTrace (prefixWord ++ tailWord_8179896) baseStart_8179896 baseEnd_8179896 := by
    simpa [prefixWord, tailWord_8179896, baseEnd_8179896] using wordTrace_append hprefix tailTrace_8179896
  have hstable : (prefixWord ++ tailWord_8179896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179896).length < 2 ^ (prefixWord ++ tailWord_8179896).sum := by decide
  have hdescent : baseEnd_8179896 < baseStart_8179896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179929 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_8179929 : Nat := 118140960795 + 8179929 * 2 ^ 59
def prefixEnd_8179929 : Nat := 4983230072969 + 3 ^ 40 * 8179929 * 2
def baseEnd_8179929 : Nat := 1400078432217210574622899

theorem tailTrace_8179929 : CollatzResearch.WordTrace tailWord_8179929 prefixEnd_8179929 1400078432217210574622899 := by
  unfold tailWord_8179929
  simp only [CollatzResearch.WordTrace]
  refine ⟨298346520782521728495814841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198897680521681152330543227 298346520782521728495814841)
  ·
    refine ⟨223759890586891296371861131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298346520782521728495814841 223759890586891296371861131)
    ·
      refine ⟨335639835880336944557791697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223759890586891296371861131 335639835880336944557791697)
      ·
        refine ⟨251729876910252708418343773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335639835880336944557791697 251729876910252708418343773)
        ·
          refine ⟨94398703841344765656878915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251729876910252708418343773 94398703841344765656878915)
          ·
            refine ⟨141598055762017148485318373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94398703841344765656878915 141598055762017148485318373)
            ·
              refine ⟨26549635455378215340997195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141598055762017148485318373 26549635455378215340997195)
              ·
                refine ⟨39824453183067323011495793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26549635455378215340997195 39824453183067323011495793)
                ·
                  refine ⟨29868339887300492258621845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39824453183067323011495793 29868339887300492258621845)
                  ·
                    refine ⟨1400078432217210574622899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29868339887300492258621845 1400078432217210574622899)
                    ·
                      rfl

theorem cell23_8179929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_8179929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179929 prefixEnd_8179929 := by exact prefixLift 8179929
  have htrace : WordTrace (prefixWord ++ tailWord_8179929) baseStart_8179929 baseEnd_8179929 := by
    simpa [prefixWord, tailWord_8179929, baseEnd_8179929] using wordTrace_append hprefix tailTrace_8179929
  have hstable : (prefixWord ++ tailWord_8179929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179929).length < 2 ^ (prefixWord ++ tailWord_8179929).sum := by decide
  have hdescent : baseEnd_8179929 < baseStart_8179929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179953 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 4, 2, 2]
def baseStart_8179953 : Nat := 118140960795 + 8179953 * 2 ^ 59
def prefixEnd_8179953 : Nat := 4983230072969 + 3 ^ 40 * 8179953 * 2
def baseEnd_8179953 : Nat := 4200247620187339629968587

theorem tailTrace_8179953 : CollatzResearch.WordTrace tailWord_8179953 prefixEnd_8179953 4200247620187339629968587 := by
  unfold tailWord_8179953
  simp only [CollatzResearch.WordTrace]
  refine ⟨298347396134434780594688513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198898264089623187063125675 298347396134434780594688513)
  ·
    refine ⟨223760547100826085446016385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298347396134434780594688513 223760547100826085446016385)
    ·
      refine ⟨167820410325619564084512289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223760547100826085446016385 167820410325619564084512289)
      ·
        refine ⟨125865307744214673063384217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167820410325619564084512289 125865307744214673063384217)
        ·
          refine ⟨94398980808161004797538163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125865307744214673063384217 94398980808161004797538163)
          ·
            refine ⟨141598471212241507196307245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94398980808161004797538163 141598471212241507196307245)
            ·
              refine ⟨53099426704590565198615217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141598471212241507196307245 53099426704590565198615217)
              ·
                refine ⟨39824570028442923898961413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53099426704590565198615217 39824570028442923898961413)
                ·
                  refine ⟨7467106880333048231055265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39824570028442923898961413 7467106880333048231055265)
                  ·
                    refine ⟨5600330160249786173291449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7467106880333048231055265 5600330160249786173291449)
                    ·
                      refine ⟨4200247620187339629968587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600330160249786173291449 4200247620187339629968587)
                      ·
                        rfl

theorem cell23_8179953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_8179953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179953 prefixEnd_8179953 := by exact prefixLift 8179953
  have htrace : WordTrace (prefixWord ++ tailWord_8179953) baseStart_8179953 baseEnd_8179953 := by
    simpa [prefixWord, tailWord_8179953, baseEnd_8179953] using wordTrace_append hprefix tailTrace_8179953
  have hstable : (prefixWord ++ tailWord_8179953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179953).length < 2 ^ (prefixWord ++ tailWord_8179953).sum := by decide
  have hdescent : baseEnd_8179953 < baseStart_8179953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179969 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_8179969 : Nat := 118140960795 + 8179969 * 2 ^ 59
def prefixEnd_8179969 : Nat := 4983230072969 + 3 ^ 40 * 8179969 * 2
def baseEnd_8179969 : Nat := 4200255835877811567368513

theorem tailTrace_8179969 : CollatzResearch.WordTrace tailWord_8179969 prefixEnd_8179969 4200255835877811567368513 := by
  unfold tailWord_8179969
  simp only [CollatzResearch.WordTrace]
  refine ⟨298347979702376815327270961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198898653134917876884847307 298347979702376815327270961)
  ·
    refine ⟨223760984776782611495453221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298347979702376815327270961 223760984776782611495453221)
    ·
      refine ⟨41955184645646739655397479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223760984776782611495453221 41955184645646739655397479)
      ·
        refine ⟨62932776968470109483096219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41955184645646739655397479 62932776968470109483096219)
        ·
          refine ⟨94399165452705164224644329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62932776968470109483096219 94399165452705164224644329)
          ·
            refine ⟨70799374089528873168483247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94399165452705164224644329 70799374089528873168483247)
            ·
              refine ⟨106199061134293309752724871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70799374089528873168483247 106199061134293309752724871)
              ·
                refine ⟨159298591701439964629087307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106199061134293309752724871 159298591701439964629087307)
                ·
                  refine ⟨238947887552159946943630961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159298591701439964629087307 238947887552159946943630961)
                  ·
                    refine ⟨179210915664119960207723221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238947887552159946943630961 179210915664119960207723221)
                    ·
                      refine ⟨4200255835877811567368513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179210915664119960207723221 4200255835877811567368513)
                      ·
                        rfl

theorem cell23_8179969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_8179969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179969 prefixEnd_8179969 := by exact prefixLift 8179969
  have htrace : WordTrace (prefixWord ++ tailWord_8179969) baseStart_8179969 baseEnd_8179969 := by
    simpa [prefixWord, tailWord_8179969, baseEnd_8179969] using wordTrace_append hprefix tailTrace_8179969
  have hstable : (prefixWord ++ tailWord_8179969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179969).length < 2 ^ (prefixWord ++ tailWord_8179969).sum := by decide
  have hdescent : baseEnd_8179969 < baseStart_8179969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179976 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 7]
def baseStart_8179976 : Nat := 118140960795 + 8179976 * 2 ^ 59
def prefixEnd_8179976 : Nat := 4983230072969 + 3 ^ 40 * 8179976 * 2
def baseEnd_8179976 : Nat := 466695492249154782220109

theorem tailTrace_8179976 : CollatzResearch.WordTrace tailWord_8179976 prefixEnd_8179976 466695492249154782220109 := by
  unfold tailWord_8179976
  simp only [CollatzResearch.WordTrace]
  refine ⟨149174117506675727761387891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198898823342234303681850521 149174117506675727761387891)
  ·
    refine ⟨223761176260013591642081837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149174117506675727761387891 223761176260013591642081837)
    ·
      refine ⟨83910441097505096865780689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223761176260013591642081837 83910441097505096865780689)
      ·
        refine ⟨62932830823128822649335517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83910441097505096865780689 62932830823128822649335517)
        ·
          refine ⟨23599811558673308493500819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62932830823128822649335517 23599811558673308493500819)
          ·
            refine ⟨35399717338009962740251229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23599811558673308493500819 35399717338009962740251229)
            ·
              refine ⟨13274894001753736027594211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35399717338009962740251229 13274894001753736027594211)
              ·
                refine ⟨19912341002630604041391317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13274894001753736027594211 19912341002630604041391317)
                ·
                  refine ⟨466695492249154782220109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19912341002630604041391317 466695492249154782220109)
                  ·
                    rfl

theorem cell23_8179976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 7].length) (baseStart_8179976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179976 prefixEnd_8179976 := by exact prefixLift 8179976
  have htrace : WordTrace (prefixWord ++ tailWord_8179976) baseStart_8179976 baseEnd_8179976 := by
    simpa [prefixWord, tailWord_8179976, baseEnd_8179976] using wordTrace_append hprefix tailTrace_8179976
  have hstable : (prefixWord ++ tailWord_8179976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179976).length < 2 ^ (prefixWord ++ tailWord_8179976).sum := by decide
  have hdescent : baseEnd_8179976 < baseStart_8179976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179989 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_8179989 : Nat := 118140960795 + 8179989 * 2 ^ 59
def prefixEnd_8179989 : Nat := 4983230072969 + 3 ^ 40 * 8179989 * 2
def baseEnd_8179989 : Nat := 1400088701830300496372807

theorem tailTrace_8179989 : CollatzResearch.WordTrace tailWord_8179989 prefixEnd_8179989 1400088701830300496372807 := by
  unfold tailWord_8179989
  simp only [CollatzResearch.WordTrace]
  refine ⟨298348709162304358742999021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198899139441536239161999347 298348709162304358742999021)
  ·
    refine ⟨111880765935864134528624633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298348709162304358742999021 111880765935864134528624633)
    ·
      refine ⟨83910574451898100896468475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111880765935864134528624633 83910574451898100896468475)
      ·
        refine ⟨125865861677847151344702713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83910574451898100896468475 125865861677847151344702713)
        ·
          refine ⟨94399396258385363508527035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125865861677847151344702713 94399396258385363508527035)
          ·
            refine ⟨141599094387578045262790553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94399396258385363508527035 141599094387578045262790553)
            ·
              refine ⟨106199320790683533947092915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141599094387578045262790553 106199320790683533947092915)
              ·
                refine ⟨159298981186025300920639373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106199320790683533947092915 159298981186025300920639373)
                ·
                  refine ⟨59737117944759487845239765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159298981186025300920639373 59737117944759487845239765)
                  ·
                    refine ⟨1400088701830300496372807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59737117944759487845239765 1400088701830300496372807)
                    ·
                      rfl

theorem cell23_8179989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_8179989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179989 prefixEnd_8179989 := by exact prefixLift 8179989
  have htrace : WordTrace (prefixWord ++ tailWord_8179989) baseStart_8179989 baseEnd_8179989 := by
    simpa [prefixWord, tailWord_8179989, baseEnd_8179989] using wordTrace_append hprefix tailTrace_8179989
  have hstable : (prefixWord ++ tailWord_8179989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179989).length < 2 ^ (prefixWord ++ tailWord_8179989).sum := by decide
  have hdescent : baseEnd_8179989 < baseStart_8179989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180060 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_8180060 : Nat := 118140960795 + 8180060 * 2 ^ 59
def prefixEnd_8180060 : Nat := 4983230072969 + 3 ^ 40 * 8180060 * 2
def baseEnd_8180060 : Nat := 4200302562617370711330595

theorem tailTrace_8180060 : CollatzResearch.WordTrace tailWord_8180060 prefixEnd_8180060 4200302562617370711330595 := by
  unfold tailWord_8180060
  simp only [CollatzResearch.WordTrace]
  refine ⟨149175649372523568934416817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198900865830031425245889089 149175649372523568934416817)
  ·
    refine ⟨111881737029392676700812613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149175649372523568934416817 111881737029392676700812613)
    ·
      refine ⟨20977825693011126881402365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111881737029392676700812613 20977825693011126881402365)
      ·
        refine ⟨7866684634879172580525887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20977825693011126881402365 7866684634879172580525887)
        ·
          refine ⟨11800026952318758870788831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7866684634879172580525887 11800026952318758870788831)
          ·
            refine ⟨17700040428478138306183247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800026952318758870788831 17700040428478138306183247)
            ·
              refine ⟨26550060642717207459274871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17700040428478138306183247 26550060642717207459274871)
              ·
                refine ⟨39825090964075811188912307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26550060642717207459274871 39825090964075811188912307)
                ·
                  refine ⟨59737636446113716783368461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39825090964075811188912307 59737636446113716783368461)
                  ·
                    refine ⟨22401613667292643793763173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59737636446113716783368461 22401613667292643793763173)
                    ·
                      refine ⟨4200302562617370711330595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22401613667292643793763173 4200302562617370711330595)
                      ·
                        rfl

theorem cell23_8180060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_8180060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180060 prefixEnd_8180060 := by exact prefixLift 8180060
  have htrace : WordTrace (prefixWord ++ tailWord_8180060) baseStart_8180060 baseEnd_8180060 := by
    simpa [prefixWord, tailWord_8180060, baseEnd_8180060] using wordTrace_append hprefix tailTrace_8180060
  have hstable : (prefixWord ++ tailWord_8180060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180060).length < 2 ^ (prefixWord ++ tailWord_8180060).sum := by decide
  have hdescent : baseEnd_8180060 < baseStart_8180060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180063 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_8180063 : Nat := 118140960795 + 8180063 * 2 ^ 59
def prefixEnd_8180063 : Nat := 4983230072969 + 3 ^ 40 * 8180063 * 2
def baseEnd_8180063 : Nat := 4200304103059334199593081

theorem tailTrace_8180063 : CollatzResearch.WordTrace tailWord_8180063 prefixEnd_8180063 4200304103059334199593081 := by
  unfold tailWord_8180063
  simp only [CollatzResearch.WordTrace]
  refine ⟨298351408164036269381192843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198900938776024179587461895 298351408164036269381192843)
  ·
    refine ⟨447527112246054404071789265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298351408164036269381192843 447527112246054404071789265)
    ·
      refine ⟨335645334184540803053841949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447527112246054404071789265 335645334184540803053841949)
      ·
        refine ⟨125867000319202801145190731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335645334184540803053841949 125867000319202801145190731)
        ·
          refine ⟨188800500478804201717786097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125867000319202801145190731 188800500478804201717786097)
          ·
            refine ⟨141600375359103151288339573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188800500478804201717786097 141600375359103151288339573)
            ·
              refine ⟨13275035189915920433281835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141600375359103151288339573 13275035189915920433281835)
              ·
                refine ⟨19912552784873880649922753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13275035189915920433281835 19912552784873880649922753)
                ·
                  refine ⟨14934414588655410487442065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19912552784873880649922753 14934414588655410487442065)
                  ·
                    refine ⟨11200810941491557865581549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14934414588655410487442065 11200810941491557865581549)
                    ·
                      refine ⟨4200304103059334199593081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11200810941491557865581549 4200304103059334199593081)
                      ·
                        rfl

theorem cell23_8180063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_8180063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180063 prefixEnd_8180063 := by exact prefixLift 8180063
  have htrace : WordTrace (prefixWord ++ tailWord_8180063) baseStart_8180063 baseEnd_8180063 := by
    simpa [prefixWord, tailWord_8180063, baseEnd_8180063] using wordTrace_append hprefix tailTrace_8180063
  have hstable : (prefixWord ++ tailWord_8180063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180063).length < 2 ^ (prefixWord ++ tailWord_8180063).sum := by decide
  have hdescent : baseEnd_8180063 < baseStart_8180063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180103 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_8180103 : Nat := 118140960795 + 8180103 * 2 ^ 59
def prefixEnd_8180103 : Nat := 4983230072969 + 3 ^ 40 * 8180103 * 2
def baseEnd_8180103 : Nat := 4200324642285514043092897

theorem tailTrace_8180103 : CollatzResearch.WordTrace tailWord_8180103 prefixEnd_8180103 4200324642285514043092897 := by
  unfold tailWord_8180103
  simp only [CollatzResearch.WordTrace]
  refine ⟨298352867083891356212648963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198901911389260904141765975 298352867083891356212648963)
  ·
    refine ⟨447529300625837034318973445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298352867083891356212648963 447529300625837034318973445)
    ·
      refine ⟨83911743867344443934807521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447529300625837034318973445 83911743867344443934807521)
      ·
        refine ⟨62933807900508332951105641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83911743867344443934807521 62933807900508332951105641)
        ·
          refine ⟨47200355925381249713329231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62933807900508332951105641 47200355925381249713329231)
          ·
            refine ⟨70800533888071874569993847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47200355925381249713329231 70800533888071874569993847)
            ·
              refine ⟨106200800832107811854990771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70800533888071874569993847 106200800832107811854990771)
              ·
                refine ⟨159301201248161717782486157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106200800832107811854990771 159301201248161717782486157)
                ·
                  refine ⟨59737950468060644168432309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159301201248161717782486157 59737950468060644168432309)
                  ·
                    refine ⟨5600432856380685390790529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59737950468060644168432309 5600432856380685390790529)
                    ·
                      refine ⟨4200324642285514043092897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600432856380685390790529 4200324642285514043092897)
                      ·
                        rfl

theorem cell23_8180103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_8180103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180103 prefixEnd_8180103 := by exact prefixLift 8180103
  have htrace : WordTrace (prefixWord ++ tailWord_8180103) baseStart_8180103 baseEnd_8180103 := by
    simpa [prefixWord, tailWord_8180103, baseEnd_8180103] using wordTrace_append hprefix tailTrace_8180103
  have hstable : (prefixWord ++ tailWord_8180103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180103).length < 2 ^ (prefixWord ++ tailWord_8180103).sum := by decide
  have hdescent : baseEnd_8180103 < baseStart_8180103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180120 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 1, 5, 2]
def baseStart_8180120 : Nat := 118140960795 + 8180120 * 2 ^ 59
def prefixEnd_8180120 : Nat := 4983230072969 + 3 ^ 40 * 8180120 * 2
def baseEnd_8180120 : Nat := 4200333371456640476580319

theorem tailTrace_8180120 : CollatzResearch.WordTrace tailWord_8180120 prefixEnd_8180120 4200333371456640476580319 := by
  unfold tailWord_8180120
  simp only [CollatzResearch.WordTrace]
  refine ⟨149176743562414884058008907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198902324749886512077345209 149176743562414884058008907)
  ·
    refine ⟨223765115343622326087013361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149176743562414884058008907 223765115343622326087013361)
    ·
      refine ⟨167823836507716744565260021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223765115343622326087013361 167823836507716744565260021)
      ·
        refine ⟨15733484672598444802993127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167823836507716744565260021 15733484672598444802993127)
        ·
          refine ⟨23600227008897667204489691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15733484672598444802993127 23600227008897667204489691)
          ·
            refine ⟨35400340513346500806734537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23600227008897667204489691 35400340513346500806734537)
            ·
              refine ⟨26550255385009875605050903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35400340513346500806734537 26550255385009875605050903)
              ·
                refine ⟨39825383077514813407576355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26550255385009875605050903 39825383077514813407576355)
                ·
                  refine ⟨59738074616272220111364533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39825383077514813407576355 59738074616272220111364533)
                  ·
                    refine ⟨5600444495275520635440425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59738074616272220111364533 5600444495275520635440425)
                    ·
                      refine ⟨4200333371456640476580319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600444495275520635440425 4200333371456640476580319)
                      ·
                        rfl

theorem cell23_8180120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_8180120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180120 prefixEnd_8180120 := by exact prefixLift 8180120
  have htrace : WordTrace (prefixWord ++ tailWord_8180120) baseStart_8180120 baseEnd_8180120 := by
    simpa [prefixWord, tailWord_8180120, baseEnd_8180120] using wordTrace_append hprefix tailTrace_8180120
  have hstable : (prefixWord ++ tailWord_8180120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180120).length < 2 ^ (prefixWord ++ tailWord_8180120).sum := by decide
  have hdescent : baseEnd_8180120 < baseStart_8180120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180133 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_8180133 : Nat := 118140960795 + 8180133 * 2 ^ 59
def prefixEnd_8180133 : Nat := 4983230072969 + 3 ^ 40 * 8180133 * 2
def baseEnd_8180133 : Nat := 4200340046705148925717759

theorem tailTrace_8180133 : CollatzResearch.WordTrace tailWord_8180133 prefixEnd_8180133 4200340046705148925717759 := by
  unfold tailWord_8180133
  simp only [CollatzResearch.WordTrace]
  refine ⟨298353961273782671336241053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198902640849188447557494035 298353961273782671336241053)
  ·
    refine ⟨111882735477668501751090395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298353961273782671336241053 111882735477668501751090395)
    ·
      refine ⟨167824103216502752626635593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111882735477668501751090395 167824103216502752626635593)
      ·
        refine ⟨125868077412377064469976695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167824103216502752626635593 125868077412377064469976695)
        ·
          refine ⟨188802116118565596704965043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125868077412377064469976695 188802116118565596704965043)
          ·
            refine ⟨283203174177848395057447565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188802116118565596704965043 283203174177848395057447565)
            ·
              refine ⟨106201190316693148146542837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283203174177848395057447565 106201190316693148146542837)
              ·
                refine ⟨9956361592189982638738391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106201190316693148146542837 9956361592189982638738391)
                ·
                  refine ⟨14934542388284973958107587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956361592189982638738391 14934542388284973958107587)
                  ·
                    refine ⟨22401813582427460937161381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14934542388284973958107587 22401813582427460937161381)
                    ·
                      refine ⟨4200340046705148925717759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22401813582427460937161381 4200340046705148925717759)
                      ·
                        rfl

theorem cell23_8180133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_8180133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180133 prefixEnd_8180133 := by exact prefixLift 8180133
  have htrace : WordTrace (prefixWord ++ tailWord_8180133) baseStart_8180133 baseEnd_8180133 := by
    simpa [prefixWord, tailWord_8180133, baseEnd_8180133] using wordTrace_append hprefix tailTrace_8180133
  have hstable : (prefixWord ++ tailWord_8180133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180133).length < 2 ^ (prefixWord ++ tailWord_8180133).sum := by decide
  have hdescent : baseEnd_8180133 < baseStart_8180133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180138 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8180138 : Nat := 118140960795 + 8180138 * 2 ^ 59
def prefixEnd_8180138 : Nat := 4983230072969 + 3 ^ 40 * 8180138 * 2
def baseEnd_8180138 : Nat := 1400114204702807135385079

theorem tailTrace_8180138 : CollatzResearch.WordTrace tailWord_8180138 prefixEnd_8180138 1400114204702807135385079 := by
  unfold tailWord_8180138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74588535909691139297543267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198902762425843038126782045 74588535909691139297543267)
  ·
    refine ⟨111882803864536708946314901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74588535909691139297543267 111882803864536708946314901)
    ·
      refine ⟨5244506431150158231858511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111882803864536708946314901 5244506431150158231858511)
      ·
        refine ⟨7866759646725237347787767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244506431150158231858511 7866759646725237347787767)
        ·
          refine ⟨11800139470087856021681651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7866759646725237347787767 11800139470087856021681651)
          ·
            refine ⟨17700209205131784032522477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800139470087856021681651 17700209205131784032522477)
            ·
              refine ⟨6637578451924419012195929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17700209205131784032522477 6637578451924419012195929)
              ·
                refine ⟨4978183838943314259146947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637578451924419012195929 4978183838943314259146947)
                ·
                  refine ⟨7467275758414971388720421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978183838943314259146947 7467275758414971388720421)
                  ·
                    refine ⟨1400114204702807135385079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467275758414971388720421 1400114204702807135385079)
                    ·
                      rfl

theorem cell23_8180138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8180138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180138 prefixEnd_8180138 := by exact prefixLift 8180138
  have htrace : WordTrace (prefixWord ++ tailWord_8180138) baseStart_8180138 baseEnd_8180138 := by
    simpa [prefixWord, tailWord_8180138, baseEnd_8180138] using wordTrace_append hprefix tailTrace_8180138
  have hstable : (prefixWord ++ tailWord_8180138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180138).length < 2 ^ (prefixWord ++ tailWord_8180138).sum := by decide
  have hdescent : baseEnd_8180138 < baseStart_8180138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180146 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_8180146 : Nat := 118140960795 + 8180146 * 2 ^ 59
def prefixEnd_8180146 : Nat := 4983230072969 + 3 ^ 40 * 8180146 * 2
def baseEnd_8180146 : Nat := 4200346721953657374855199

theorem tailTrace_8180146 : CollatzResearch.WordTrace tailWord_8180146 prefixEnd_8180146 4200346721953657374855199 := by
  unfold tailWord_8180146
  simp only [CollatzResearch.WordTrace]
  refine ⟨74588608855683893639116073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198902956948490383037642861 74588608855683893639116073)
  ·
    refine ⟨55941456641762920229337055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74588608855683893639116073 55941456641762920229337055)
    ·
      refine ⟨83912184962644380344005583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55941456641762920229337055 83912184962644380344005583)
      ·
        refine ⟨125868277443966570516008375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83912184962644380344005583 125868277443966570516008375)
        ·
          refine ⟨188802416165949855774012563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125868277443966570516008375 188802416165949855774012563)
          ·
            refine ⟨283203624248924783661018845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188802416165949855774012563 283203624248924783661018845)
            ·
              refine ⟨106201359093346793872882067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283203624248924783661018845 106201359093346793872882067)
              ·
                refine ⟨159302038640020190809323101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106201359093346793872882067 159302038640020190809323101)
                ·
                  refine ⟨59738264490007571553496163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159302038640020190809323101 59738264490007571553496163)
                  ·
                    refine ⟨89607396735011357330244245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59738264490007571553496163 89607396735011357330244245)
                    ·
                      refine ⟨4200346721953657374855199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89607396735011357330244245 4200346721953657374855199)
                      ·
                        rfl

theorem cell23_8180146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_8180146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180146 prefixEnd_8180146 := by exact prefixLift 8180146
  have htrace : WordTrace (prefixWord ++ tailWord_8180146) baseStart_8180146 baseEnd_8180146 := by
    simpa [prefixWord, tailWord_8180146, baseEnd_8180146] using wordTrace_append hprefix tailTrace_8180146
  have hstable : (prefixWord ++ tailWord_8180146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180146).length < 2 ^ (prefixWord ++ tailWord_8180146).sum := by decide
  have hdescent : baseEnd_8180146 < baseStart_8180146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180153 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_8180153 : Nat := 118140960795 + 8180153 * 2 ^ 59
def prefixEnd_8180153 : Nat := 4983230072969 + 3 ^ 40 * 8180153 * 2
def baseEnd_8180153 : Nat := 4200350316318238847467667

theorem tailTrace_8180153 : CollatzResearch.WordTrace tailWord_8180153 prefixEnd_8180153 4200350316318238847467667 := by
  unfold tailWord_8180153
  simp only [CollatzResearch.WordTrace]
  refine ⟨298354690733710214751969113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198903127155806809834646075 298354690733710214751969113)
  ·
    refine ⟨223766018050282661063976835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298354690733710214751969113 223766018050282661063976835)
    ·
      refine ⟨335649027075423991595965253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223766018050282661063976835 335649027075423991595965253)
      ·
        refine ⟨62934192576641998424243485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335649027075423991595965253 62934192576641998424243485)
        ·
          refine ⟨23600322216240749409091307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62934192576641998424243485 23600322216240749409091307)
          ·
            refine ⟨35400483324361124113636961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23600322216240749409091307 35400483324361124113636961)
            ·
              refine ⟨26550362493270843085227721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35400483324361124113636961 26550362493270843085227721)
              ·
                refine ⟨19912771869953132313920791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26550362493270843085227721 19912771869953132313920791)
                ·
                  refine ⟨29869157804929698470881187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19912771869953132313920791 29869157804929698470881187)
                  ·
                    refine ⟨44803736707394547706321781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29869157804929698470881187 44803736707394547706321781)
                    ·
                      refine ⟨4200350316318238847467667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44803736707394547706321781 4200350316318238847467667)
                      ·
                        rfl

theorem cell23_8180153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_8180153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180153 prefixEnd_8180153 := by exact prefixLift 8180153
  have htrace : WordTrace (prefixWord ++ tailWord_8180153) baseStart_8180153 baseEnd_8180153 := by
    simpa [prefixWord, tailWord_8180153, baseEnd_8180153] using wordTrace_append hprefix tailTrace_8180153
  have hstable : (prefixWord ++ tailWord_8180153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180153).length < 2 ^ (prefixWord ++ tailWord_8180153).sum := by decide
  have hdescent : baseEnd_8180153 < baseStart_8180153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180164 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_8180164 : Nat := 118140960795 + 8180164 * 2 ^ 59
def prefixEnd_8180164 : Nat := 4983230072969 + 3 ^ 40 * 8180164 * 2
def baseEnd_8180164 : Nat := 1400118654868479434810039

theorem tailTrace_8180164 : CollatzResearch.WordTrace tailWord_8180164 prefixEnd_8180164 1400118654868479434810039 := by
  unfold tailWord_8180164
  simp only [CollatzResearch.WordTrace]
  refine ⟨149177545968335181815309773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198903394624446909087079697 149177545968335181815309773)
  ·
    refine ⟨55941579738125693180741165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149177545968335181815309773 55941579738125693180741165)
    ·
      refine ⟨20978092401797134942777937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55941579738125693180741165 20978092401797134942777937)
      ·
        refine ⟨15733569301347851207083453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20978092401797134942777937 15733569301347851207083453)
        ·
          refine ⟨5900088488005444202656295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15733569301347851207083453 5900088488005444202656295)
          ·
            refine ⟨8850132732008166303984443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900088488005444202656295 8850132732008166303984443)
            ·
              refine ⟨13275199098012249455976665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850132732008166303984443 13275199098012249455976665)
              ·
                refine ⟨9956399323509187091982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13275199098012249455976665 9956399323509187091982499)
                ·
                  refine ⟨14934598985263780637973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956399323509187091982499 14934598985263780637973749)
                  ·
                    refine ⟨1400118654868479434810039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14934598985263780637973749 1400118654868479434810039)
                    ·
                      rfl

theorem cell23_8180164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_8180164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180164 prefixEnd_8180164 := by exact prefixLift 8180164
  have htrace : WordTrace (prefixWord ++ tailWord_8180164) baseStart_8180164 baseEnd_8180164 := by
    simpa [prefixWord, tailWord_8180164, baseEnd_8180164] using wordTrace_append hprefix tailTrace_8180164
  have hstable : (prefixWord ++ tailWord_8180164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180164).length < 2 ^ (prefixWord ++ tailWord_8180164).sum := by decide
  have hdescent : baseEnd_8180164 < baseStart_8180164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180180 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_8180180 : Nat := 118140960795 + 8180180 * 2 ^ 59
def prefixEnd_8180180 : Nat := 4983230072969 + 3 ^ 40 * 8180180 * 2
def baseEnd_8180180 : Nat := 4200364180295910241830043

theorem tailTrace_8180180 : CollatzResearch.WordTrace tailWord_8180180 prefixEnd_8180180 4200364180295910241830043 := by
  unfold tailWord_8180180
  simp only [CollatzResearch.WordTrace]
  refine ⟨149177837752306199181600997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198903783669741598908801329 149177837752306199181600997)
  ·
    refine ⟨27970844578557412346550187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149177837752306199181600997 27970844578557412346550187)
    ·
      refine ⟨41956266867836118519825281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27970844578557412346550187 41956266867836118519825281)
      ·
        refine ⟨31467200150877088889868961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41956266867836118519825281 31467200150877088889868961)
        ·
          refine ⟨23600400113157816667401721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31467200150877088889868961 23600400113157816667401721)
          ·
            refine ⟨17700300084868362500551291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23600400113157816667401721 17700300084868362500551291)
            ·
              refine ⟨26550450127302543750826937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17700300084868362500551291 26550450127302543750826937)
              ·
                refine ⟨19912837595476907813120203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26550450127302543750826937 19912837595476907813120203)
                ·
                  refine ⟨29869256393215361719680305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19912837595476907813120203 29869256393215361719680305)
                  ·
                    refine ⟨22401942294911521289760229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29869256393215361719680305 22401942294911521289760229)
                    ·
                      refine ⟨4200364180295910241830043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22401942294911521289760229 4200364180295910241830043)
                      ·
                        rfl

theorem cell23_8180180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_8180180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180180 prefixEnd_8180180 := by exact prefixLift 8180180
  have htrace : WordTrace (prefixWord ++ tailWord_8180180) baseStart_8180180 baseEnd_8180180 := by
    simpa [prefixWord, tailWord_8180180, baseEnd_8180180] using wordTrace_append hprefix tailTrace_8180180
  have hstable : (prefixWord ++ tailWord_8180180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180180).length < 2 ^ (prefixWord ++ tailWord_8180180).sum := by decide
  have hdescent : baseEnd_8180180 < baseStart_8180180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180196 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_8180196 : Nat := 118140960795 + 8180196 * 2 ^ 59
def prefixEnd_8180196 : Nat := 4983230072969 + 3 ^ 40 * 8180196 * 2
def baseEnd_8180196 : Nat := 4200372395986382179229969

theorem tailTrace_8180196 : CollatzResearch.WordTrace tailWord_8180196 prefixEnd_8180196 4200372395986382179229969 := by
  unfold tailWord_8180196
  simp only [CollatzResearch.WordTrace]
  refine ⟨149178129536277216547892221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198904172715036288730522961 149178129536277216547892221)
  ·
    refine ⟨55941798576103956205459583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149178129536277216547892221 55941798576103956205459583)
    ·
      refine ⟨83912697864155934308189375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55941798576103956205459583 83912697864155934308189375)
      ·
        refine ⟨125869046796233901462284063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83912697864155934308189375 125869046796233901462284063)
        ·
          refine ⟨188803570194350852193426095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125869046796233901462284063 188803570194350852193426095)
          ·
            refine ⟨283205355291526278290139143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188803570194350852193426095 283205355291526278290139143)
            ·
              refine ⟨424808032937289417435208715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283205355291526278290139143 424808032937289417435208715)
              ·
                refine ⟨637212049405934126152813073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424808032937289417435208715 637212049405934126152813073)
                ·
                  refine ⟨477909037054450594614609805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637212049405934126152813073 477909037054450594614609805)
                  ·
                    refine ⟨179215888895418972980478677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477909037054450594614609805 179215888895418972980478677)
                    ·
                      refine ⟨4200372395986382179229969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179215888895418972980478677 4200372395986382179229969)
                      ·
                        rfl

theorem cell23_8180196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_8180196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180196 prefixEnd_8180196 := by exact prefixLift 8180196
  have htrace : WordTrace (prefixWord ++ tailWord_8180196) baseStart_8180196 baseEnd_8180196 := by
    simpa [prefixWord, tailWord_8180196, baseEnd_8180196] using wordTrace_append hprefix tailTrace_8180196
  have hstable : (prefixWord ++ tailWord_8180196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180196).length < 2 ^ (prefixWord ++ tailWord_8180196).sum := by decide
  have hdescent : baseEnd_8180196 < baseStart_8180196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180257 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_8180257 : Nat := 118140960795 + 8180257 * 2 ^ 59
def prefixEnd_8180257 : Nat := 4983230072969 + 3 ^ 40 * 8180257 * 2
def baseEnd_8180257 : Nat := 4200403718306306440567189

theorem tailTrace_8180257 : CollatzResearch.WordTrace tailWord_8180257 prefixEnd_8180257 4200403718306306440567189 := by
  unfold tailWord_8180257
  simp only [CollatzResearch.WordTrace]
  refine ⟨298358483925333440513755025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198905655950222293675836683 298358483925333440513755025)
  ·
    refine ⟨223768862944000080385316269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298358483925333440513755025 223768862944000080385316269)
    ·
      refine ⟨83913323604000030144493601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223768862944000080385316269 83913323604000030144493601)
      ·
        refine ⟨62934992703000022608370201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83913323604000030144493601 62934992703000022608370201)
        ·
          refine ⟨47201244527250016956277651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62934992703000022608370201 47201244527250016956277651)
          ·
            refine ⟨70801866790875025434416477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47201244527250016956277651 70801866790875025434416477)
            ·
              refine ⟨26550700046578134537906179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70801866790875025434416477 26550700046578134537906179)
              ·
                refine ⟨39826050069867201806859269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26550700046578134537906179 39826050069867201806859269)
                ·
                  refine ⟨7467384388100100338786113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39826050069867201806859269 7467384388100100338786113)
                  ·
                    refine ⟨5600538291075075254089585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7467384388100100338786113 5600538291075075254089585)
                    ·
                      refine ⟨4200403718306306440567189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600538291075075254089585 4200403718306306440567189)
                      ·
                        rfl

theorem cell23_8180257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_8180257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180257 prefixEnd_8180257 := by exact prefixLift 8180257
  have htrace : WordTrace (prefixWord ++ tailWord_8180257) baseStart_8180257 baseEnd_8180257 := by
    simpa [prefixWord, tailWord_8180257, baseEnd_8180257] using wordTrace_append hprefix tailTrace_8180257
  have hstable : (prefixWord ++ tailWord_8180257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180257).length < 2 ^ (prefixWord ++ tailWord_8180257).sum := by decide
  have hdescent : baseEnd_8180257 < baseStart_8180257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180293 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_8180293 : Nat := 118140960795 + 8180293 * 2 ^ 59
def prefixEnd_8180293 : Nat := 4983230072969 + 3 ^ 40 * 8180293 * 2
def baseEnd_8180293 : Nat := 1400140734536622766572341

theorem tailTrace_8180293 : CollatzResearch.WordTrace tailWord_8180293 prefixEnd_8180293 1400140734536622766572341 := by
  unfold tailWord_8180293
  simp only [CollatzResearch.WordTrace]
  refine ⟨298359796953203018662065533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198906531302135345774710355 298359796953203018662065533)
  ·
    refine ⟨111884923857451131998274575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298359796953203018662065533 111884923857451131998274575)
    ·
      refine ⟨167827385786176697997411863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111884923857451131998274575 167827385786176697997411863)
      ·
        refine ⟨251741078679265046996117795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167827385786176697997411863 251741078679265046996117795)
        ·
          refine ⟨377611618018897570494176693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251741078679265046996117795 377611618018897570494176693)
          ·
            refine ⟨35401089189271647233829065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377611618018897570494176693 35401089189271647233829065)
            ·
              refine ⟨26550816891953735425371799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35401089189271647233829065 26550816891953735425371799)
              ·
                refine ⟨39826225337930603138057699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26550816891953735425371799 39826225337930603138057699)
                ·
                  refine ⟨59739338006895904707086549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39826225337930603138057699 59739338006895904707086549)
                  ·
                    refine ⟨1400140734536622766572341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59739338006895904707086549 1400140734536622766572341)
                    ·
                      rfl

theorem cell23_8180293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_8180293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180293 prefixEnd_8180293 := by exact prefixLift 8180293
  have htrace : WordTrace (prefixWord ++ tailWord_8180293) baseStart_8180293 baseEnd_8180293 := by
    simpa [prefixWord, tailWord_8180293, baseEnd_8180293] using wordTrace_append hprefix tailTrace_8180293
  have hstable : (prefixWord ++ tailWord_8180293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180293).length < 2 ^ (prefixWord ++ tailWord_8180293).sum := by decide
  have hdescent : baseEnd_8180293 < baseStart_8180293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180330 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_8180330 : Nat := 118140960795 + 8180330 * 2 ^ 59
def prefixEnd_8180330 : Nat := 4983230072969 + 3 ^ 40 * 8180330 * 2
def baseEnd_8180330 : Nat := 4200441202394084654954353

theorem tailTrace_8180330 : CollatzResearch.WordTrace tailWord_8180330 prefixEnd_8180330 4200441202394084654954353 := by
  unfold tailWord_8180330
  simp only [CollatzResearch.WordTrace]
  refine ⟨74590286613517243495290611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198907430969379315987441629 74590286613517243495290611)
  ·
    refine ⟨111885429920275865242935917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74590286613517243495290611 111885429920275865242935917)
    ·
      refine ⟨41957036220103449466100969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111885429920275865242935917 41957036220103449466100969)
      ·
        refine ⟨31467777165077587099575727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41957036220103449466100969 31467777165077587099575727)
        ·
          refine ⟨47201665747616380649363591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31467777165077587099575727 47201665747616380649363591)
          ·
            refine ⟨70802498621424570974045387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47201665747616380649363591 70802498621424570974045387)
            ·
              refine ⟨106203747932136856461068081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70802498621424570974045387 106203747932136856461068081)
              ·
                refine ⟨79652810949102642345801061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106203747932136856461068081 79652810949102642345801061)
                ·
                  refine ⟨14934902052956745439837699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79652810949102642345801061 14934902052956745439837699)
                  ·
                    refine ⟨22402353079435118159756549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14934902052956745439837699 22402353079435118159756549)
                    ·
                      refine ⟨4200441202394084654954353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22402353079435118159756549 4200441202394084654954353)
                      ·
                        rfl

theorem cell23_8180330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_8180330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180330 prefixEnd_8180330 := by exact prefixLift 8180330
  have htrace : WordTrace (prefixWord ++ tailWord_8180330) baseStart_8180330 baseEnd_8180330 := by
    simpa [prefixWord, tailWord_8180330, baseEnd_8180330] using wordTrace_append hprefix tailTrace_8180330
  have hstable : (prefixWord ++ tailWord_8180330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180330).length < 2 ^ (prefixWord ++ tailWord_8180330).sum := by decide
  have hdescent : baseEnd_8180330 < baseStart_8180330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180343 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_8180343 : Nat := 118140960795 + 8180343 * 2 ^ 59
def prefixEnd_8180343 : Nat := 4983230072969 + 3 ^ 40 * 8180343 * 2
def baseEnd_8180343 : Nat := 4200447877642593104091793

theorem tailTrace_8180343 : CollatzResearch.WordTrace tailWord_8180343 prefixEnd_8180343 4200447877642593104091793 := by
  unfold tailWord_8180343
  simp only [CollatzResearch.WordTrace]
  refine ⟨298361620603021877201385683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198907747068681251467590455 298361620603021877201385683)
  ·
    refine ⟨447542430904532815802078525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298361620603021877201385683 447542430904532815802078525)
    ·
      refine ⟨167828411589199805925779447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447542430904532815802078525 167828411589199805925779447)
      ·
        refine ⟨251742617383799708888669171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167828411589199805925779447 251742617383799708888669171)
        ·
          refine ⟨377613926075699563333003757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251742617383799708888669171 377613926075699563333003757)
          ·
            refine ⟨141605222278387336249876409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377613926075699563333003757 141605222278387336249876409)
            ·
              refine ⟨106203916708790502187407307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141605222278387336249876409 106203916708790502187407307)
              ·
                refine ⟨159305875063185753281110961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106203916708790502187407307 159305875063185753281110961)
                ·
                  refine ⟨119479406297389314960833221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159305875063185753281110961 119479406297389314960833221)
                  ·
                    refine ⟨22402388680760496555156229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119479406297389314960833221 22402388680760496555156229)
                    ·
                      refine ⟨4200447877642593104091793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22402388680760496555156229 4200447877642593104091793)
                      ·
                        rfl

theorem cell23_8180343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_8180343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180343 prefixEnd_8180343 := by exact prefixLift 8180343
  have htrace : WordTrace (prefixWord ++ tailWord_8180343) baseStart_8180343 baseEnd_8180343 := by
    simpa [prefixWord, tailWord_8180343, baseEnd_8180343] using wordTrace_append hprefix tailTrace_8180343
  have hstable : (prefixWord ++ tailWord_8180343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180343).length < 2 ^ (prefixWord ++ tailWord_8180343).sum := by decide
  have hdescent : baseEnd_8180343 < baseStart_8180343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180400 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 1, 5]
def baseStart_8180400 : Nat := 118140960795 + 8180400 * 2 ^ 59
def prefixEnd_8180400 : Nat := 4983230072969 + 3 ^ 40 * 8180400 * 2
def baseEnd_8180400 : Nat := 1400159048679966460359677

theorem tailTrace_8180400 : CollatzResearch.WordTrace tailWord_8180400 prefixEnd_8180400 1400159048679966460359677 := by
  unfold tailWord_8180400
  simp only [CollatzResearch.WordTrace]
  refine ⟨149181849781907687968105327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198909133042543583957473769 149181849781907687968105327)
  ·
    refine ⟨223772774672861531952157991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149181849781907687968105327 223772774672861531952157991)
    ·
      refine ⟨335659162009292297928236987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223772774672861531952157991 335659162009292297928236987)
      ·
        refine ⟨503488743013938446892355481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335659162009292297928236987 503488743013938446892355481)
        ·
          refine ⟨377616557260453835169266611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503488743013938446892355481 377616557260453835169266611)
          ·
            refine ⟨566424835890680752753899917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377616557260453835169266611 566424835890680752753899917)
            ·
              refine ⟨212409313459005282282712469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566424835890680752753899917 212409313459005282282712469)
              ·
                refine ⟨9956686568390872607002147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212409313459005282282712469 9956686568390872607002147)
                ·
                  refine ⟨14935029852586308910503221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956686568390872607002147 14935029852586308910503221)
                  ·
                    refine ⟨1400159048679966460359677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14935029852586308910503221 1400159048679966460359677)
                    ·
                      rfl

theorem cell23_8180400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_8180400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180400 prefixEnd_8180400 := by exact prefixLift 8180400
  have htrace : WordTrace (prefixWord ++ tailWord_8180400) baseStart_8180400 baseEnd_8180400 := by
    simpa [prefixWord, tailWord_8180400, baseEnd_8180400] using wordTrace_append hprefix tailTrace_8180400
  have hstable : (prefixWord ++ tailWord_8180400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180400).length < 2 ^ (prefixWord ++ tailWord_8180400).sum := by decide
  have hdescent : baseEnd_8180400 < baseStart_8180400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180401 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_8180401 : Nat := 118140960795 + 8180401 * 2 ^ 59
def prefixEnd_8180401 : Nat := 4983230072969 + 3 ^ 40 * 8180401 * 2
def baseEnd_8180401 : Nat := 4200477659520553877166527

theorem tailTrace_8180401 : CollatzResearch.WordTrace tailWord_8180401 prefixEnd_8180401 4200477659520553877166527 := by
  unfold tailWord_8180401
  simp only [CollatzResearch.WordTrace]
  refine ⟨298363736036811753106997057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198909157357874502071331371 298363736036811753106997057)
  ·
    refine ⟨223772802027608814830247793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298363736036811753106997057 223772802027608814830247793)
    ·
      refine ⟨167829601520706611122685845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223772802027608814830247793 167829601520706611122685845)
      ·
        refine ⟨7867012571283122396375899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167829601520706611122685845 7867012571283122396375899)
        ·
          refine ⟨11800518856924683594563849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7867012571283122396375899 11800518856924683594563849)
          ·
            refine ⟨8850389142693512695922887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11800518856924683594563849 8850389142693512695922887)
            ·
              refine ⟨13275583714040269043884331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850389142693512695922887 13275583714040269043884331)
              ·
                refine ⟨19913375571060403565826497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13275583714040269043884331 19913375571060403565826497)
                ·
                  refine ⟨14935031678295302674369873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19913375571060403565826497 14935031678295302674369873)
                  ·
                    refine ⟨11201273758721477005777405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14935031678295302674369873 11201273758721477005777405)
                    ·
                      refine ⟨4200477659520553877166527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11201273758721477005777405 4200477659520553877166527)
                      ·
                        rfl

theorem cell23_8180401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_8180401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180401 prefixEnd_8180401 := by exact prefixLift 8180401
  have htrace : WordTrace (prefixWord ++ tailWord_8180401) baseStart_8180401 baseEnd_8180401 := by
    simpa [prefixWord, tailWord_8180401, baseEnd_8180401] using wordTrace_append hprefix tailTrace_8180401
  have hstable : (prefixWord ++ tailWord_8180401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180401).length < 2 ^ (prefixWord ++ tailWord_8180401).sum := by decide
  have hdescent : baseEnd_8180401 < baseStart_8180401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180440 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_8180440 : Nat := 118140960795 + 8180440 * 2 ^ 59
def prefixEnd_8180440 : Nat := 4983230072969 + 3 ^ 40 * 8180440 * 2
def baseEnd_8180440 : Nat := 4200497685266079224578847

theorem tailTrace_8180440 : CollatzResearch.WordTrace tailWord_8180440 prefixEnd_8180440 4200497685266079224578847 := by
  unfold tailWord_8180440
  simp only [CollatzResearch.WordTrace]
  refine ⟨149182579241835231383833387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198910105655780308511777849 149182579241835231383833387)
  ·
    refine ⟨223773868862752847075750081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149182579241835231383833387 223773868862752847075750081)
    ·
      refine ⟨167830401647064635306812561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223773868862752847075750081 167830401647064635306812561)
      ·
        refine ⟨125872801235298476480109421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167830401647064635306812561 125872801235298476480109421)
        ·
          refine ⟨47202300463236928680041033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125872801235298476480109421 47202300463236928680041033)
          ·
            refine ⟨35401725347427696510030775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47202300463236928680041033 35401725347427696510030775)
            ·
              refine ⟨53102588021141544765046163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35401725347427696510030775 53102588021141544765046163)
              ·
                refine ⟨79653882031712317147569245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53102588021141544765046163 79653882031712317147569245)
                ·
                  refine ⟨29870205761892118930338467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79653882031712317147569245 29870205761892118930338467)
                  ·
                    refine ⟨44805308642838178395507701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29870205761892118930338467 44805308642838178395507701)
                    ·
                      refine ⟨4200497685266079224578847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44805308642838178395507701 4200497685266079224578847)
                      ·
                        rfl

theorem cell23_8180440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_8180440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180440 prefixEnd_8180440 := by exact prefixLift 8180440
  have htrace : WordTrace (prefixWord ++ tailWord_8180440) baseStart_8180440 baseEnd_8180440 := by
    simpa [prefixWord, tailWord_8180440, baseEnd_8180440] using wordTrace_append hprefix tailTrace_8180440
  have hstable : (prefixWord ++ tailWord_8180440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180440).length < 2 ^ (prefixWord ++ tailWord_8180440).sum := by decide
  have hdescent : baseEnd_8180440 < baseStart_8180440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180447 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 1, 6]
def baseStart_8180447 : Nat := 118140960795 + 8180447 * 2 ^ 59
def prefixEnd_8180447 : Nat := 4983230072969 + 3 ^ 40 * 8180447 * 2
def baseEnd_8180447 : Nat := 1400167093210220232397105

theorem tailTrace_8180447 : CollatzResearch.WordTrace tailWord_8180447 prefixEnd_8180447 1400167093210220232397105 := by
  unfold tailWord_8180447
  simp only [CollatzResearch.WordTrace]
  refine ⟨298365413794645102963171595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198910275863096735308781063 298365413794645102963171595)
  ·
    refine ⟨447548120691967654444757393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298365413794645102963171595 447548120691967654444757393)
    ·
      refine ⟨335661090518975740833568045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447548120691967654444757393 335661090518975740833568045)
      ·
        refine ⟨125872908944615902812588017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335661090518975740833568045 125872908944615902812588017)
        ·
          refine ⟨94404681708461927109441013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125872908944615902812588017 94404681708461927109441013)
          ·
            refine ⟨8850438910168305666510095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94404681708461927109441013 8850438910168305666510095)
            ·
              refine ⟨13275658365252458499765143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850438910168305666510095 13275658365252458499765143)
              ·
                refine ⟨19913487547878687749647715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13275658365252458499765143 19913487547878687749647715)
                ·
                  refine ⟨29870231321818031624471573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19913487547878687749647715 29870231321818031624471573)
                  ·
                    refine ⟨1400167093210220232397105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29870231321818031624471573 1400167093210220232397105)
                    ·
                      rfl

theorem cell23_8180447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_8180447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180447 prefixEnd_8180447 := by exact prefixLift 8180447
  have htrace : WordTrace (prefixWord ++ tailWord_8180447) baseStart_8180447 baseEnd_8180447 := by
    simpa [prefixWord, tailWord_8180447, baseEnd_8180447] using wordTrace_append hprefix tailTrace_8180447
  have hstable : (prefixWord ++ tailWord_8180447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180447).length < 2 ^ (prefixWord ++ tailWord_8180447).sum := by decide
  have hdescent : baseEnd_8180447 < baseStart_8180447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180457 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 3]
def baseStart_8180457 : Nat := 118140960795 + 8180457 * 2 ^ 59
def prefixEnd_8180457 : Nat := 4983230072969 + 3 ^ 40 * 8180457 * 2
def baseEnd_8180457 : Nat := 4200506414437205658066269

theorem tailTrace_8180457 : CollatzResearch.WordTrace tailWord_8180457 prefixEnd_8180457 4200506414437205658066269 := by
  unfold tailWord_8180457
  simp only [CollatzResearch.WordTrace]
  refine ⟨298365778524608874671035625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198910519016405916447357083 298365778524608874671035625)
  ·
    refine ⟨223774333893456656003276719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298365778524608874671035625 223774333893456656003276719)
    ·
      refine ⟨335661500840184984004915079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223774333893456656003276719 335661500840184984004915079)
      ·
        refine ⟨503492251260277476007372619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335661500840184984004915079 503492251260277476007372619)
        ·
          refine ⟨755238376890416214011058929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503492251260277476007372619 755238376890416214011058929)
          ·
            refine ⟨566428782667812160508294197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755238376890416214011058929 566428782667812160508294197)
            ·
              refine ⟨53102698375107390047652581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 566428782667812160508294197 53102698375107390047652581)
              ·
                refine ⟨9956755945332635633934859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53102698375107390047652581 9956755945332635633934859)
                ·
                  refine ⟨14935133917998953450902289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956755945332635633934859 14935133917998953450902289)
                  ·
                    refine ⟨11201350438499215088176717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14935133917998953450902289 11201350438499215088176717)
                    ·
                      refine ⟨4200506414437205658066269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11201350438499215088176717 4200506414437205658066269)
                      ·
                        rfl

theorem cell23_8180457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_8180457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180457 prefixEnd_8180457 := by exact prefixLift 8180457
  have htrace : WordTrace (prefixWord ++ tailWord_8180457) baseStart_8180457 baseEnd_8180457 := by
    simpa [prefixWord, tailWord_8180457, baseEnd_8180457] using wordTrace_append hprefix tailTrace_8180457
  have hstable : (prefixWord ++ tailWord_8180457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180457).length < 2 ^ (prefixWord ++ tailWord_8180457).sum := by decide
  have hdescent : baseEnd_8180457 < baseStart_8180457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180490 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_8180490 : Nat := 118140960795 + 8180490 * 2 ^ 59
def prefixEnd_8180490 : Nat := 4983230072969 + 3 ^ 40 * 8180490 * 2
def baseEnd_8180490 : Nat := 1400174453099601342984539

theorem tailTrace_8180490 : CollatzResearch.WordTrace tailWord_8180490 prefixEnd_8180490 1400174453099601342984539 := by
  unfold tailWord_8180490
  simp only [CollatzResearch.WordTrace]
  refine ⟨74591745533372330326746731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198911321422326214204657949 74591745533372330326746731)
  ·
    refine ⟨111887618300058495490120097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74591745533372330326746731 111887618300058495490120097)
    ·
      refine ⟨83915713725043871617590073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111887618300058495490120097 83915713725043871617590073)
      ·
        refine ⟨62936785293782903713192555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83915713725043871617590073 62936785293782903713192555)
        ·
          refine ⟨94405177940674355569788833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62936785293782903713192555 94405177940674355569788833)
          ·
            refine ⟨70803883455505766677341625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94405177940674355569788833 70803883455505766677341625)
            ·
              refine ⟨53102912591629325008006219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70803883455505766677341625 53102912591629325008006219)
              ·
                refine ⟨79654368887443987512009329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53102912591629325008006219 79654368887443987512009329)
                ·
                  refine ⟨59740776665582990634006997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79654368887443987512009329 59740776665582990634006997)
                  ·
                    refine ⟨1400174453099601342984539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59740776665582990634006997 1400174453099601342984539)
                    ·
                      rfl

theorem cell23_8180490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_8180490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180490 prefixEnd_8180490 := by exact prefixLift 8180490
  have htrace : WordTrace (prefixWord ++ tailWord_8180490) baseStart_8180490 baseEnd_8180490 := by
    simpa [prefixWord, tailWord_8180490, baseEnd_8180490] using wordTrace_append hprefix tailTrace_8180490
  have hstable : (prefixWord ++ tailWord_8180490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180490).length < 2 ^ (prefixWord ++ tailWord_8180490).sum := by decide
  have hdescent : baseEnd_8180490 < baseStart_8180490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180525 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_8180525 : Nat := 118140960795 + 8180525 * 2 ^ 59
def prefixEnd_8180525 : Nat := 4983230072969 + 3 ^ 40 * 8180525 * 2
def baseEnd_8180525 : Nat := 4200541331121711392015957

theorem tailTrace_8180525 : CollatzResearch.WordTrace tailWord_8180525 prefixEnd_8180525 4200541331121711392015957 := by
  unfold tailWord_8180525
  simp only [CollatzResearch.WordTrace]
  refine ⟨298368258688362522284511029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198912172458908348189674019 298368258688362522284511029)
  ·
    refine ⟨27972024252033986464172909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298368258688362522284511029 27972024252033986464172909)
    ·
      refine ⟨10489509094512744924064841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27972024252033986464172909 10489509094512744924064841)
      ·
        refine ⟨7867131820884558693048631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10489509094512744924064841 7867131820884558693048631)
        ·
          refine ⟨11800697731326838039572947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7867131820884558693048631 11800697731326838039572947)
          ·
            refine ⟨17701046596990257059359421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800697731326838039572947 17701046596990257059359421)
            ·
              refine ⟨6637892473871346397259783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17701046596990257059359421 6637892473871346397259783)
              ·
                refine ⟨9956838710807019595889675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637892473871346397259783 9956838710807019595889675)
                ·
                  refine ⟨14935258066210529393834513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956838710807019595889675 14935258066210529393834513)
                  ·
                    refine ⟨11201443549657897045375885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14935258066210529393834513 11201443549657897045375885)
                    ·
                      refine ⟨4200541331121711392015957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11201443549657897045375885 4200541331121711392015957)
                      ·
                        rfl

theorem cell23_8180525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_8180525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180525 prefixEnd_8180525 := by exact prefixLift 8180525
  have htrace : WordTrace (prefixWord ++ tailWord_8180525) baseStart_8180525 baseEnd_8180525 := by
    simpa [prefixWord, tailWord_8180525, baseEnd_8180525] using wordTrace_append hprefix tailTrace_8180525
  have hstable : (prefixWord ++ tailWord_8180525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180525).length < 2 ^ (prefixWord ++ tailWord_8180525).sum := by decide
  have hdescent : baseEnd_8180525 < baseStart_8180525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180540 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_8180540 : Nat := 118140960795 + 8180540 * 2 ^ 59
def prefixEnd_8180540 : Nat := 4983230072969 + 3 ^ 40 * 8180540 * 2
def baseEnd_8180540 : Nat := 4200549033331528833328387

theorem tailTrace_8180540 : CollatzResearch.WordTrace tailWord_8180540 prefixEnd_8180540 4200549033331528833328387 := by
  unfold tailWord_8180540
  simp only [CollatzResearch.WordTrace]
  refine ⟨149184402891654089923153537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198912537188872119897538049 149184402891654089923153537)
  ·
    refine ⟨111888302168740567442365153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149184402891654089923153537 111888302168740567442365153)
    ·
      refine ⟨83916226626555425581773865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111888302168740567442365153 83916226626555425581773865)
      ·
        refine ⟨62937169969916569186330399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83916226626555425581773865 62937169969916569186330399)
        ·
          refine ⟨94405754954874853779495599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62937169969916569186330399 94405754954874853779495599)
          ·
            refine ⟨141608632432312280669243399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94405754954874853779495599 141608632432312280669243399)
            ·
              refine ⟨212412948648468421003865099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141608632432312280669243399 212412948648468421003865099)
              ·
                refine ⟨318619422972702631505797649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212412948648468421003865099 318619422972702631505797649)
                ·
                  refine ⟨238964567229526973629348237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318619422972702631505797649 238964567229526973629348237)
                  ·
                    refine ⟨89611712711072615111005589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238964567229526973629348237 89611712711072615111005589)
                    ·
                      refine ⟨4200549033331528833328387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89611712711072615111005589 4200549033331528833328387)
                      ·
                        rfl

theorem cell23_8180540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_8180540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180540 prefixEnd_8180540 := by exact prefixLift 8180540
  have htrace : WordTrace (prefixWord ++ tailWord_8180540) baseStart_8180540 baseEnd_8180540 := by
    simpa [prefixWord, tailWord_8180540, baseEnd_8180540] using wordTrace_append hprefix tailTrace_8180540
  have hstable : (prefixWord ++ tailWord_8180540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180540).length < 2 ^ (prefixWord ++ tailWord_8180540).sum := by decide
  have hdescent : baseEnd_8180540 < baseStart_8180540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180544 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 4, 2, 2]
def baseStart_8180544 : Nat := 118140960795 + 8180544 * 2 ^ 59
def prefixEnd_8180544 : Nat := 4983230072969 + 3 ^ 40 * 8180544 * 2
def baseEnd_8180544 : Nat := 4200551087254146817678369

theorem tailTrace_8180544 : CollatzResearch.WordTrace tailWord_8180544 prefixEnd_8180544 4200551087254146817678369 := by
  unfold tailWord_8180544
  simp only [CollatzResearch.WordTrace]
  refine ⟨149184475837646844264726343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198912634450195792352968457 149184475837646844264726343)
  ·
    refine ⟨223776713756470266397089515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149184475837646844264726343 223776713756470266397089515)
    ·
      refine ⟨335665070634705399595634273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223776713756470266397089515 335665070634705399595634273)
      ·
        refine ⟨251748802976029049696725705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335665070634705399595634273 251748802976029049696725705)
        ·
          refine ⟨188811602232021787272544279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251748802976029049696725705 188811602232021787272544279)
          ·
            refine ⟨283217403348032680908816419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188811602232021787272544279 283217403348032680908816419)
            ·
              refine ⟨424826105022049021363224629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283217403348032680908816419 424826105022049021363224629)
              ·
                refine ⟨39827447345817095752802309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424826105022049021363224629 39827447345817095752802309)
                ·
                  refine ⟨7467646377340705453650433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39827447345817095752802309 7467646377340705453650433)
                  ·
                    refine ⟨5600734783005529090237825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7467646377340705453650433 5600734783005529090237825)
                    ·
                      refine ⟨4200551087254146817678369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600734783005529090237825 4200551087254146817678369)
                      ·
                        rfl

theorem cell23_8180544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_8180544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180544 prefixEnd_8180544 := by exact prefixLift 8180544
  have htrace : WordTrace (prefixWord ++ tailWord_8180544) baseStart_8180544 baseEnd_8180544 := by
    simpa [prefixWord, tailWord_8180544, baseEnd_8180544] using wordTrace_append hprefix tailTrace_8180544
  have hstable : (prefixWord ++ tailWord_8180544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180544).length < 2 ^ (prefixWord ++ tailWord_8180544).sum := by decide
  have hdescent : baseEnd_8180544 < baseStart_8180544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180561 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 1, 4, 2]
def baseStart_8180561 : Nat := 118140960795 + 8180561 * 2 ^ 59
def prefixEnd_8180561 : Nat := 4983230072969 + 3 ^ 40 * 8180561 * 2
def baseEnd_8180561 : Nat := 4200559816425273251165791

theorem tailTrace_8180561 : CollatzResearch.WordTrace tailWord_8180561 prefixEnd_8180561 4200559816425273251165791 := by
  unfold tailWord_8180561
  simp only [CollatzResearch.WordTrace]
  refine ⟨298369571716232100432821537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198913047810821400288547691 298369571716232100432821537)
  ·
    refine ⟨223777178787174075324616153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298369571716232100432821537 223777178787174075324616153)
    ·
      refine ⟨167832884090380556493462115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223777178787174075324616153 167832884090380556493462115)
      ·
        refine ⟨251749326135570834740193173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167832884090380556493462115 251749326135570834740193173)
        ·
          refine ⟨11800749662604882878446555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251749326135570834740193173 11800749662604882878446555)
          ·
            refine ⟨17701124493907324317669833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800749662604882878446555 17701124493907324317669833)
            ·
              refine ⟨13275843370430493238252375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17701124493907324317669833 13275843370430493238252375)
              ·
                refine ⟨19913765055645739857378563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13275843370430493238252375 19913765055645739857378563)
                ·
                  refine ⟨29870647583468609786067845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19913765055645739857378563 29870647583468609786067845)
                  ·
                    refine ⟨5600746421900364334887721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29870647583468609786067845 5600746421900364334887721)
                    ·
                      refine ⟨4200559816425273251165791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600746421900364334887721 4200559816425273251165791)
                      ·
                        rfl

theorem cell23_8180561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_8180561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180561 prefixEnd_8180561 := by exact prefixLift 8180561
  have htrace : WordTrace (prefixWord ++ tailWord_8180561) baseStart_8180561 baseEnd_8180561 := by
    simpa [prefixWord, tailWord_8180561, baseEnd_8180561] using wordTrace_append hprefix tailTrace_8180561
  have hstable : (prefixWord ++ tailWord_8180561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180561).length < 2 ^ (prefixWord ++ tailWord_8180561).sum := by decide
  have hdescent : baseEnd_8180561 < baseStart_8180561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180567 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 7]
def baseStart_8180567 : Nat := 118140960795 + 8180567 * 2 ^ 59
def prefixEnd_8180567 : Nat := 4983230072969 + 3 ^ 40 * 8180567 * 2
def baseEnd_8180567 : Nat := 466729210812133358632307

theorem tailTrace_8180567 : CollatzResearch.WordTrace tailWord_8180567 prefixEnd_8180567 466729210812133358632307 := by
  unfold tailWord_8180567
  simp only [CollatzResearch.WordTrace]
  refine ⟨298369790554210363457539955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198913193702806908971693303 298369790554210363457539955)
  ·
    refine ⟨447554685831315545186309933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298369790554210363457539955 447554685831315545186309933)
    ·
      refine ⟨167833007186743329444866225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447554685831315545186309933 167833007186743329444866225)
      ·
        refine ⟨125874755390057497083649669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167833007186743329444866225 125874755390057497083649669)
        ·
          refine ⟨23601516635635780703184313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125874755390057497083649669 23601516635635780703184313)
          ·
            refine ⟨17701137476726835527388235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23601516635635780703184313 17701137476726835527388235)
            ·
              refine ⟨26551706215090253291082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17701137476726835527388235 26551706215090253291082353)
              ·
                refine ⟨19913779661317689968311765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26551706215090253291082353 19913779661317689968311765)
                ·
                  refine ⟨466729210812133358632307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19913779661317689968311765 466729210812133358632307)
                  ·
                    rfl

theorem cell23_8180567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 7].length) (baseStart_8180567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180567 prefixEnd_8180567 := by exact prefixLift 8180567
  have htrace : WordTrace (prefixWord ++ tailWord_8180567) baseStart_8180567 baseEnd_8180567 := by
    simpa [prefixWord, tailWord_8180567, baseEnd_8180567] using wordTrace_append hprefix tailTrace_8180567
  have hstable : (prefixWord ++ tailWord_8180567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180567).length < 2 ^ (prefixWord ++ tailWord_8180567).sum := by decide
  have hdescent : baseEnd_8180567 < baseStart_8180567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180584 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 5]
def baseStart_8180584 : Nat := 118140960795 + 8180584 * 2 ^ 59
def prefixEnd_8180584 : Nat := 4983230072969 + 3 ^ 40 * 8180584 * 2
def baseEnd_8180584 : Nat := 466730180720036295686465

theorem tailTrace_8180584 : CollatzResearch.WordTrace tailWord_8180584 prefixEnd_8180584 466730180720036295686465 := by
  unfold tailWord_8180584
  simp only [CollatzResearch.WordTrace]
  refine ⟨149185205297574387680454403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198913607063432516907272537 149185205297574387680454403)
  ·
    refine ⟨223777807946361581520681605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149185205297574387680454403 223777807946361581520681605)
    ·
      refine ⟨41958338989942796535127801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223777807946361581520681605 41958338989942796535127801)
      ·
        refine ⟨31468754242457097401345851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41958338989942796535127801 31468754242457097401345851)
        ·
          refine ⟨47203131363685646102018777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31468754242457097401345851 47203131363685646102018777)
          ·
            refine ⟨35402348522764234576514083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47203131363685646102018777 35402348522764234576514083)
            ·
              refine ⟨53103522784146351864771125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35402348522764234576514083 53103522784146351864771125)
              ·
                refine ⟨4978455261013720487322293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53103522784146351864771125 4978455261013720487322293)
                ·
                  refine ⟨466730180720036295686465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4978455261013720487322293 466730180720036295686465)
                  ·
                    rfl

theorem cell23_8180584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 5].length) (baseStart_8180584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180584 prefixEnd_8180584 := by exact prefixLift 8180584
  have htrace : WordTrace (prefixWord ++ tailWord_8180584) baseStart_8180584 baseEnd_8180584 := by
    simpa [prefixWord, tailWord_8180584, baseEnd_8180584] using wordTrace_append hprefix tailTrace_8180584
  have hstable : (prefixWord ++ tailWord_8180584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180584).length < 2 ^ (prefixWord ++ tailWord_8180584).sum := by decide
  have hdescent : baseEnd_8180584 < baseStart_8180584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180617 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_8180617 : Nat := 118140960795 + 8180617 * 2 ^ 59
def prefixEnd_8180617 : Nat := 4983230072969 + 3 ^ 40 * 8180617 * 2
def baseEnd_8180617 : Nat := 4200588571341925032065533

theorem tailTrace_8180617 : CollatzResearch.WordTrace tailWord_8180617 prefixEnd_8180617 4200588571341925032065533 := by
  unfold tailWord_8180617
  simp only [CollatzResearch.WordTrace]
  refine ⟨298371614204029221996860105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198914409469352814664573403 298371614204029221996860105)
  ·
    refine ⟨223778710653021916497645079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298371614204029221996860105 223778710653021916497645079)
    ·
      refine ⟨335668065979532874746467619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223778710653021916497645079 335668065979532874746467619)
      ·
        refine ⟨503502098969299312119701429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335668065979532874746467619 503502098969299312119701429)
        ·
          refine ⟨47203321778371810511222009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503502098969299312119701429 47203321778371810511222009)
          ·
            refine ⟨35402491333778857883416507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47203321778371810511222009 35402491333778857883416507)
            ·
              refine ⟨53103737000668286825124761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35402491333778857883416507 53103737000668286825124761)
              ·
                refine ⟨39827802750501215118843571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53103737000668286825124761 39827802750501215118843571)
                ·
                  refine ⟨59741704125751822678265357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39827802750501215118843571 59741704125751822678265357)
                  ·
                    refine ⟨22403139047156933504349509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59741704125751822678265357 22403139047156933504349509)
                    ·
                      refine ⟨4200588571341925032065533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22403139047156933504349509 4200588571341925032065533)
                      ·
                        rfl

theorem cell23_8180617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_8180617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180617 prefixEnd_8180617 := by exact prefixLift 8180617
  have htrace : WordTrace (prefixWord ++ tailWord_8180617) baseStart_8180617 baseEnd_8180617 := by
    simpa [prefixWord, tailWord_8180617, baseEnd_8180617] using wordTrace_append hprefix tailTrace_8180617
  have hstable : (prefixWord ++ tailWord_8180617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180617).length < 2 ^ (prefixWord ++ tailWord_8180617).sum := by decide
  have hdescent : baseEnd_8180617 < baseStart_8180617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180627 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 5, 4]
def baseStart_8180627 : Nat := 118140960795 + 8180627 * 2 ^ 59
def prefixEnd_8180627 : Nat := 4983230072969 + 3 ^ 40 * 8180627 * 2
def baseEnd_8180627 : Nat := 1400197902049489997646829

theorem tailTrace_8180627 : CollatzResearch.WordTrace tailWord_8180627 prefixEnd_8180627 1400197902049489997646829 := by
  unfold tailWord_8180627
  simp only [CollatzResearch.WordTrace]
  refine ⟨298371978933992993704724135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198914652622661995803149423 298371978933992993704724135)
  ·
    refine ⟨447557968400989490557086203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298371978933992993704724135 447557968400989490557086203)
    ·
      refine ⟨671336952601484235835629305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447557968400989490557086203 671336952601484235835629305)
      ·
        refine ⟨503502714451113176876721979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671336952601484235835629305 503502714451113176876721979)
        ·
          refine ⟨755254071676669765315082969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503502714451113176876721979 755254071676669765315082969)
          ·
            refine ⟨566440553757502323986312227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755254071676669765315082969 566440553757502323986312227)
            ·
              refine ⟨849660830636253485979468341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566440553757502323986312227 849660830636253485979468341)
              ·
                refine ⟨79655702872148764310575157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849660830636253485979468341 79655702872148764310575157)
                ·
                  refine ⟨7467722144263946654116421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79655702872148764310575157 7467722144263946654116421)
                  ·
                    refine ⟨1400197902049489997646829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467722144263946654116421 1400197902049489997646829)
                    ·
                      rfl

theorem cell23_8180627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 4].length) (baseStart_8180627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180627 prefixEnd_8180627 := by exact prefixLift 8180627
  have htrace : WordTrace (prefixWord ++ tailWord_8180627) baseStart_8180627 baseEnd_8180627 := by
    simpa [prefixWord, tailWord_8180627, baseEnd_8180627] using wordTrace_append hprefix tailTrace_8180627
  have hstable : (prefixWord ++ tailWord_8180627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180627).length < 2 ^ (prefixWord ++ tailWord_8180627).sum := by decide
  have hdescent : baseEnd_8180627 < baseStart_8180627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180764 : List Nat := [2, 2, 3, 1, 4, 1, 10]
def baseStart_8180764 : Nat := 118140960795 + 8180764 * 2 ^ 59
def prefixEnd_8180764 : Nat := 4983230072969 + 3 ^ 40 * 8180764 * 2
def baseEnd_8180764 : Nat := 51860050037014024159597

theorem tailTrace_8180764 : CollatzResearch.WordTrace tailWord_8180764 prefixEnd_8180764 51860050037014024159597 := by
  unfold tailWord_8180764
  simp only [CollatzResearch.WordTrace]
  refine ⟨149188487867248333051230673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198917983822997777401640897 149188487867248333051230673)
  ·
    refine ⟨111891365900436249788423005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149188487867248333051230673 111891365900436249788423005)
    ·
      refine ⟨41959262212663593670658627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111891365900436249788423005 41959262212663593670658627)
      ·
        refine ⟨62938893318995390505987941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41959262212663593670658627 62938893318995390505987941)
        ·
          refine ⟨11801042497311635719872739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62938893318995390505987941 11801042497311635719872739)
          ·
            refine ⟨17701563745967453579809109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801042497311635719872739 17701563745967453579809109)
            ·
              refine ⟨51860050037014024159597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17701563745967453579809109 51860050037014024159597)
              ·
                rfl

theorem cell23_8180764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 10].length) (baseStart_8180764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180764 prefixEnd_8180764 := by exact prefixLift 8180764
  have htrace : WordTrace (prefixWord ++ tailWord_8180764) baseStart_8180764 baseEnd_8180764 := by
    simpa [prefixWord, tailWord_8180764, baseEnd_8180764] using wordTrace_append hprefix tailTrace_8180764
  have hstable : (prefixWord ++ tailWord_8180764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180764).length < 2 ^ (prefixWord ++ tailWord_8180764).sum := by decide
  have hdescent : baseEnd_8180764 < baseStart_8180764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180768 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 4, 4]
def baseStart_8180768 : Nat := 118140960795 + 8180768 * 2 ^ 59
def prefixEnd_8180768 : Nat := 4983230072969 + 3 ^ 40 * 8180768 * 2
def baseEnd_8180768 : Nat := 1400222035640251313759113

theorem tailTrace_8180768 : CollatzResearch.WordTrace tailWord_8180768 prefixEnd_8180768 1400222035640251313759113 := by
  unfold tailWord_8180768
  simp only [CollatzResearch.WordTrace]
  refine ⟨149188560813241087392803479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198918081084321449857071305 149188560813241087392803479)
  ·
    refine ⟨223782841219861631089205219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149188560813241087392803479 223782841219861631089205219)
    ·
      refine ⟨335674261829792446633807829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223782841219861631089205219 335674261829792446633807829)
      ·
        refine ⟨7867365511635760467979871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 335674261829792446633807829 7867365511635760467979871)
        ·
          refine ⟨11801048267453640701969807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7867365511635760467979871 11801048267453640701969807)
          ·
            refine ⟨17701572401180461052954711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801048267453640701969807 17701572401180461052954711)
            ·
              refine ⟨26552358601770691579432067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17701572401180461052954711 26552358601770691579432067)
              ·
                refine ⟨39828537902656037369148101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26552358601770691579432067 39828537902656037369148101)
                ·
                  refine ⟨7467850856748007006715269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39828537902656037369148101 7467850856748007006715269)
                  ·
                    refine ⟨1400222035640251313759113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467850856748007006715269 1400222035640251313759113)
                    ·
                      rfl

theorem cell23_8180768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_8180768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180768 prefixEnd_8180768 := by exact prefixLift 8180768
  have htrace : WordTrace (prefixWord ++ tailWord_8180768) baseStart_8180768 baseEnd_8180768 := by
    simpa [prefixWord, tailWord_8180768, baseEnd_8180768] using wordTrace_append hprefix tailTrace_8180768
  have hstable : (prefixWord ++ tailWord_8180768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180768).length < 2 ^ (prefixWord ++ tailWord_8180768).sum := by decide
  have hdescent : baseEnd_8180768 < baseStart_8180768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180775 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_8180775 : Nat := 118140960795 + 8180775 * 2 ^ 59
def prefixEnd_8180775 : Nat := 4983230072969 + 3 ^ 40 * 8180775 * 2
def baseEnd_8180775 : Nat := 4200669701285335413889807

theorem tailTrace_8180775 : CollatzResearch.WordTrace tailWord_8180775 prefixEnd_8180775 4200669701285335413889807 := by
  unfold tailWord_8180775
  simp only [CollatzResearch.WordTrace]
  refine ⟨298377376937456814981111779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198918251291637876654074519 298377376937456814981111779)
  ·
    refine ⟨447566065406185222471667669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298377376937456814981111779 447566065406185222471667669)
    ·
      refine ⟨10489829657957466151679711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 447566065406185222471667669 10489829657957466151679711)
      ·
        refine ⟨15734744486936199227519567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10489829657957466151679711 15734744486936199227519567)
        ·
          refine ⟨23602116730404298841279351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734744486936199227519567 23602116730404298841279351)
          ·
            refine ⟨35403175095606448261919027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23602116730404298841279351 35403175095606448261919027)
            ·
              refine ⟨53104762643409672392878541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35403175095606448261919027 53104762643409672392878541)
              ·
                refine ⟨19914285991278627147329453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53104762643409672392878541 19914285991278627147329453)
                ·
                  refine ⟨7467857246729485180248545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19914285991278627147329453 7467857246729485180248545)
                  ·
                    refine ⟨5600892935047113885186409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7467857246729485180248545 5600892935047113885186409)
                    ·
                      refine ⟨4200669701285335413889807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600892935047113885186409 4200669701285335413889807)
                      ·
                        rfl

theorem cell23_8180775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_8180775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180775 prefixEnd_8180775 := by exact prefixLift 8180775
  have htrace : WordTrace (prefixWord ++ tailWord_8180775) baseStart_8180775 baseEnd_8180775 := by
    simpa [prefixWord, tailWord_8180775, baseEnd_8180775] using wordTrace_append hprefix tailTrace_8180775
  have hstable : (prefixWord ++ tailWord_8180775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180775).length < 2 ^ (prefixWord ++ tailWord_8180775).sum := by decide
  have hdescent : baseEnd_8180775 < baseStart_8180775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180788 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_8180788 : Nat := 118140960795 + 8180788 * 2 ^ 59
def prefixEnd_8180788 : Nat := 4983230072969 + 3 ^ 40 * 8180788 * 2
def baseEnd_8180788 : Nat := 4200676376533843863027247

theorem tailTrace_8180788 : CollatzResearch.WordTrace tailWord_8180788 prefixEnd_8180788 4200676376533843863027247 := by
  unfold tailWord_8180788
  simp only [CollatzResearch.WordTrace]
  refine ⟨149188925543204859100667509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198918567390939812134223345 149188925543204859100667509)
  ·
    refine ⟨13986461769675455540687579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149188925543204859100667509 13986461769675455540687579)
    ·
      refine ⟨20979692654513183311031369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13986461769675455540687579 20979692654513183311031369)
      ·
        refine ⟨15734769490884887483273527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20979692654513183311031369 15734769490884887483273527)
        ·
          refine ⟨23602154236327331224910291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734769490884887483273527 23602154236327331224910291)
          ·
            refine ⟨35403231354490996837365437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23602154236327331224910291 35403231354490996837365437)
            ·
              refine ⟨13276211757934123814012039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35403231354490996837365437 13276211757934123814012039)
              ·
                refine ⟨19914317636901185721018059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276211757934123814012039 19914317636901185721018059)
                ·
                  refine ⟨29871476455351778581527089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19914317636901185721018059 29871476455351778581527089)
                  ·
                    refine ⟨22403607341513833936145317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29871476455351778581527089 22403607341513833936145317)
                    ·
                      refine ⟨4200676376533843863027247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22403607341513833936145317 4200676376533843863027247)
                      ·
                        rfl

theorem cell23_8180788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_8180788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180788 prefixEnd_8180788 := by exact prefixLift 8180788
  have htrace : WordTrace (prefixWord ++ tailWord_8180788) baseStart_8180788 baseEnd_8180788 := by
    simpa [prefixWord, tailWord_8180788, baseEnd_8180788] using wordTrace_append hprefix tailTrace_8180788
  have hstable : (prefixWord ++ tailWord_8180788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180788).length < 2 ^ (prefixWord ++ tailWord_8180788).sum := by decide
  have hdescent : baseEnd_8180788 < baseStart_8180788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180798 : List Nat := [4, 2, 1, 3, 1, 3, 2, 7]
def baseStart_8180798 : Nat := 118140960795 + 8180798 * 2 ^ 59
def prefixEnd_8180798 : Nat := 4983230072969 + 3 ^ 40 * 8180798 * 2
def baseEnd_8180798 : Nat := 155580796716310697181563

theorem tailTrace_8180798 : CollatzResearch.WordTrace tailWord_8180798 prefixEnd_8180798 155580796716310697181563 := by
  unfold tailWord_8180798
  simp only [CollatzResearch.WordTrace]
  refine ⟨37297276977046686238649881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198918810544248993272799365 37297276977046686238649881)
  ·
    refine ⟨27972957732785014678987411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37297276977046686238649881 27972957732785014678987411)
    ·
      refine ⟨41959436599177522018481117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27972957732785014678987411 41959436599177522018481117)
      ·
        refine ⟨15734788724691570756930419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41959436599177522018481117 15734788724691570756930419)
        ·
          refine ⟨23602183087037356135395629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734788724691570756930419 23602183087037356135395629)
          ·
            refine ⟨8850818657639008550773361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23602183087037356135395629 8850818657639008550773361)
            ·
              refine ⟨6638113993229256413080021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8850818657639008550773361 6638113993229256413080021)
              ·
                refine ⟨155580796716310697181563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6638113993229256413080021 155580796716310697181563)
                ·
                  rfl

theorem cell23_8180798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_8180798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180798 prefixEnd_8180798 := by exact prefixLift 8180798
  have htrace : WordTrace (prefixWord ++ tailWord_8180798) baseStart_8180798 baseEnd_8180798 := by
    simpa [prefixWord, tailWord_8180798, baseEnd_8180798] using wordTrace_append hprefix tailTrace_8180798
  have hstable : (prefixWord ++ tailWord_8180798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180798).length < 2 ^ (prefixWord ++ tailWord_8180798).sum := by decide
  have hdescent : baseEnd_8180798 < baseStart_8180798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180842 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_8180842 : Nat := 118140960795 + 8180842 * 2 ^ 59
def prefixEnd_8180842 : Nat := 4983230072969 + 3 ^ 40 * 8180842 * 2
def baseEnd_8180842 : Nat := 4200704104489186651751999

theorem tailTrace_8180842 : CollatzResearch.WordTrace tailWord_8180842 prefixEnd_8180842 4200704104489186651751999 := by
  unfold tailWord_8180842
  simp only [CollatzResearch.WordTrace]
  refine ⟨74594955157053521355950195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198919880418809390282533853 74594955157053521355950195)
  ·
    refine ⟨111892432735580282033925293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74594955157053521355950195 111892432735580282033925293)
    ·
      refine ⟨41959662275842605762721985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111892432735580282033925293 41959662275842605762721985)
      ·
        refine ⟨31469746706881954322041489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41959662275842605762721985 31469746706881954322041489)
        ·
          refine ⟨23602310030161465741531117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31469746706881954322041489 23602310030161465741531117)
          ·
            refine ⟨8850866261310549653074169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23602310030161465741531117 8850866261310549653074169)
            ·
              refine ⟨6638149695982912239805627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8850866261310549653074169 6638149695982912239805627)
              ·
                refine ⟨9957224543974368359708441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638149695982912239805627 9957224543974368359708441)
                ·
                  refine ⟨7467918407980776269781331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957224543974368359708441 7467918407980776269781331)
                  ·
                    refine ⟨11201877611971164404671997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7467918407980776269781331 11201877611971164404671997)
                    ·
                      refine ⟨4200704104489186651751999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11201877611971164404671997 4200704104489186651751999)
                      ·
                        rfl

theorem cell23_8180842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_8180842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180842 prefixEnd_8180842 := by exact prefixLift 8180842
  have htrace : WordTrace (prefixWord ++ tailWord_8180842) baseStart_8180842 baseEnd_8180842 := by
    simpa [prefixWord, tailWord_8180842, baseEnd_8180842] using wordTrace_append hprefix tailTrace_8180842
  have hstable : (prefixWord ++ tailWord_8180842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180842).length < 2 ^ (prefixWord ++ tailWord_8180842).sum := by decide
  have hdescent : baseEnd_8180842 < baseStart_8180842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180844 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_8180844 : Nat := 118140960795 + 8180844 * 2 ^ 59
def prefixEnd_8180844 : Nat := 4983230072969 + 3 ^ 40 * 8180844 * 2
def baseEnd_8180844 : Nat := 4200705131450495643926989

theorem tailTrace_8180844 : CollatzResearch.WordTrace tailWord_8180844 prefixEnd_8180844 4200705131450495643926989 := by
  unfold tailWord_8180844
  simp only [CollatzResearch.WordTrace]
  refine ⟨149189946787103419882686793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198919929049471226510249057 149189946787103419882686793)
  ·
    refine ⟨111892460090327564912015095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149189946787103419882686793 111892460090327564912015095)
    ·
      refine ⟨167838690135491347368022643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111892460090327564912015095 167838690135491347368022643)
      ·
        refine ⟨251758035203237021052033965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167838690135491347368022643 251758035203237021052033965)
        ·
          refine ⟨94409263201213882894512737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251758035203237021052033965 94409263201213882894512737)
          ·
            refine ⟨70806947400910412170884553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94409263201213882894512737 70806947400910412170884553)
            ·
              refine ⟨53105210550682809128163415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70806947400910412170884553 53105210550682809128163415)
              ·
                refine ⟨79657815826024213692245123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53105210550682809128163415 79657815826024213692245123)
                ·
                  refine ⟨119486723739036320538367685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79657815826024213692245123 119486723739036320538367685)
                  ·
                    refine ⟨22403760701069310100943941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119486723739036320538367685 22403760701069310100943941)
                    ·
                      refine ⟨4200705131450495643926989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22403760701069310100943941 4200705131450495643926989)
                      ·
                        rfl

theorem cell23_8180844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_8180844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180844 prefixEnd_8180844 := by exact prefixLift 8180844
  have htrace : WordTrace (prefixWord ++ tailWord_8180844) baseStart_8180844 baseEnd_8180844 := by
    simpa [prefixWord, tailWord_8180844, baseEnd_8180844] using wordTrace_append hprefix tailTrace_8180844
  have hstable : (prefixWord ++ tailWord_8180844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180844).length < 2 ^ (prefixWord ++ tailWord_8180844).sum := by decide
  have hdescent : baseEnd_8180844 < baseStart_8180844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180871 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 5]
def baseStart_8180871 : Nat := 118140960795 + 8180871 * 2 ^ 59
def prefixEnd_8180871 : Nat := 4983230072969 + 3 ^ 40 * 8180871 * 2
def baseEnd_8180871 : Nat := 466746555047574115365485

theorem tailTrace_8180871 : CollatzResearch.WordTrace tailWord_8180871 prefixEnd_8180871 466746555047574115365485 := by
  unfold tailWord_8180871
  simp only [CollatzResearch.WordTrace]
  refine ⟨298380878345109023376606467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198920585563406015584404311 298380878345109023376606467)
  ·
    refine ⟨447571317517663535064909701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298380878345109023376606467 447571317517663535064909701)
    ·
      refine ⟨83919622034561912824670569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447571317517663535064909701 83919622034561912824670569)
      ·
        refine ⟨62939716525921434618502927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83919622034561912824670569 62939716525921434618502927)
        ·
          refine ⟨94409574788882151927754391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62939716525921434618502927 94409574788882151927754391)
          ·
            refine ⟨141614362183323227891631587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94409574788882151927754391 141614362183323227891631587)
            ·
              refine ⟨212421543274984841837447381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141614362183323227891631587 212421543274984841837447381)
              ·
                refine ⟨4978629920507457230565173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212421543274984841837447381 4978629920507457230565173)
                ·
                  refine ⟨466746555047574115365485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4978629920507457230565173 466746555047574115365485)
                  ·
                    rfl

theorem cell23_8180871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 5].length) (baseStart_8180871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180871 prefixEnd_8180871 := by exact prefixLift 8180871
  have htrace : WordTrace (prefixWord ++ tailWord_8180871) baseStart_8180871 baseEnd_8180871 := by
    simpa [prefixWord, tailWord_8180871, baseEnd_8180871] using wordTrace_append hprefix tailTrace_8180871
  have hstable : (prefixWord ++ tailWord_8180871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180871).length < 2 ^ (prefixWord ++ tailWord_8180871).sum := by decide
  have hdescent : baseEnd_8180871 < baseStart_8180871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180882 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_8180882 : Nat := 118140960795 + 8180882 * 2 ^ 59
def prefixEnd_8180882 : Nat := 4983230072969 + 3 ^ 40 * 8180882 * 2
def baseEnd_8180882 : Nat := 4200724643715366495251815

theorem tailTrace_8180882 : CollatzResearch.WordTrace tailWord_8180882 prefixEnd_8180882 4200724643715366495251815 := by
  unfold tailWord_8180882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595319887017293063814225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198920853032046114836837933 74595319887017293063814225)
  ·
    refine ⟨55946489915262969797860669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74595319887017293063814225 55946489915262969797860669)
    ·
      refine ⟨20979933718223613674197751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55946489915262969797860669 20979933718223613674197751)
      ·
        refine ⟨31469900577335420511296627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20979933718223613674197751 31469900577335420511296627)
        ·
          refine ⟨47204850866003130766944941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31469900577335420511296627 47204850866003130766944941)
          ·
            refine ⟨17701819074751174037604353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47204850866003130766944941 17701819074751174037604353)
            ·
              refine ⟨13276364306063380528203265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17701819074751174037604353 13276364306063380528203265)
              ·
                refine ⟨9957273229547535396152449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13276364306063380528203265 9957273229547535396152449)
                ·
                  refine ⟨7467954922160651547114337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957273229547535396152449 7467954922160651547114337)
                  ·
                    refine ⟨5600966191620488660335753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7467954922160651547114337 5600966191620488660335753)
                    ·
                      refine ⟨4200724643715366495251815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600966191620488660335753 4200724643715366495251815)
                      ·
                        rfl

theorem cell23_8180882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_8180882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180882 prefixEnd_8180882 := by exact prefixLift 8180882
  have htrace : WordTrace (prefixWord ++ tailWord_8180882) baseStart_8180882 baseEnd_8180882 := by
    simpa [prefixWord, tailWord_8180882, baseEnd_8180882] using wordTrace_append hprefix tailTrace_8180882
  have hstable : (prefixWord ++ tailWord_8180882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180882).length < 2 ^ (prefixWord ++ tailWord_8180882).sum := by decide
  have hdescent : baseEnd_8180882 < baseStart_8180882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180888 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 5]
def baseStart_8180888 : Nat := 118140960795 + 8180888 * 2 ^ 59
def prefixEnd_8180888 : Nat := 4983230072969 + 3 ^ 40 * 8180888 * 2
def baseEnd_8180888 : Nat := 466747524955477052419643

theorem tailTrace_8180888 : CollatzResearch.WordTrace tailWord_8180888 prefixEnd_8180888 466747524955477052419643 := by
  unfold tailWord_8180888
  simp only [CollatzResearch.WordTrace]
  refine ⟨149190749193023717639987659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198920998924031623519983545 149190749193023717639987659)
  ·
    refine ⟨223786123789535576459981489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149190749193023717639987659 223786123789535576459981489)
    ·
      refine ⟨167839592842151682344986117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223786123789535576459981489 167839592842151682344986117)
      ·
        refine ⟨31469923657903440439684897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167839592842151682344986117 31469923657903440439684897)
        ·
          refine ⟨23602442743427580329763673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31469923657903440439684897 23602442743427580329763673)
          ·
            refine ⟨17701832057570685247322755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23602442743427580329763673 17701832057570685247322755)
            ·
              refine ⟨26552748086356027870984133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17701832057570685247322755 26552748086356027870984133)
              ·
                refine ⟨4978640266191755225809525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26552748086356027870984133 4978640266191755225809525)
                ·
                  refine ⟨466747524955477052419643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4978640266191755225809525 466747524955477052419643)
                  ·
                    rfl

theorem cell23_8180888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 5].length) (baseStart_8180888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180888 prefixEnd_8180888 := by exact prefixLift 8180888
  have htrace : WordTrace (prefixWord ++ tailWord_8180888) baseStart_8180888 baseEnd_8180888 := by
    simpa [prefixWord, tailWord_8180888, baseEnd_8180888] using wordTrace_append hprefix tailTrace_8180888
  have hstable : (prefixWord ++ tailWord_8180888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180888).length < 2 ^ (prefixWord ++ tailWord_8180888).sum := by decide
  have hdescent : baseEnd_8180888 < baseStart_8180888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180921 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_8180921 : Nat := 118140960795 + 8180921 * 2 ^ 59
def prefixEnd_8180921 : Nat := 4983230072969 + 3 ^ 40 * 8180921 * 2
def baseEnd_8180921 : Nat := 4200744669460891842664135

theorem tailTrace_8180921 : CollatzResearch.WordTrace tailWord_8180921 prefixEnd_8180921 4200744669460891842664135 := by
  unfold tailWord_8180921
  simp only [CollatzResearch.WordTrace]
  refine ⟨298382701994927881915926617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198921801329951921277284411 298382701994927881915926617)
  ·
    refine ⟨223787026496195911436944963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298382701994927881915926617 223787026496195911436944963)
    ·
      refine ⟨335680539744293867155417445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223787026496195911436944963 335680539744293867155417445)
      ·
        refine ⟨62940101202055100091640771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335680539744293867155417445 62940101202055100091640771)
        ·
          refine ⟨94410151803082650137461157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62940101202055100091640771 94410151803082650137461157)
          ·
            refine ⟨17701903463077996900773967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94410151803082650137461157 17701903463077996900773967)
            ·
              refine ⟨26552855194616995351160951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17701903463077996900773967 26552855194616995351160951)
              ·
                refine ⟨39829282791925493026741427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26552855194616995351160951 39829282791925493026741427)
                ·
                  refine ⟨59743924187888239540112141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39829282791925493026741427 59743924187888239540112141)
                  ·
                    refine ⟨22403971570458089827542053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59743924187888239540112141 22403971570458089827542053)
                    ·
                      refine ⟨4200744669460891842664135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22403971570458089827542053 4200744669460891842664135)
                      ·
                        rfl

theorem cell23_8180921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_8180921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180921 prefixEnd_8180921 := by exact prefixLift 8180921
  have htrace : WordTrace (prefixWord ++ tailWord_8180921) baseStart_8180921 baseEnd_8180921 := by
    simpa [prefixWord, tailWord_8180921, baseEnd_8180921] using wordTrace_append hprefix tailTrace_8180921
  have hstable : (prefixWord ++ tailWord_8180921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180921).length < 2 ^ (prefixWord ++ tailWord_8180921).sum := by decide
  have hdescent : baseEnd_8180921 < baseStart_8180921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8180938 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_8180938 : Nat := 118140960795 + 8180938 * 2 ^ 59
def prefixEnd_8180938 : Nat := 4983230072969 + 3 ^ 40 * 8180938 * 2
def baseEnd_8180938 : Nat := 4200753398632018276151557

theorem tailTrace_8180938 : CollatzResearch.WordTrace tailWord_8180938 prefixEnd_8180938 4200753398632018276151557 := by
  unfold tailWord_8180938
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595830508966573454823867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198922214690577529212863645 74595830508966573454823867)
  ·
    refine ⟨111893745763449860182235801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74595830508966573454823867 111893745763449860182235801)
    ·
      refine ⟨83920309322587395136676851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111893745763449860182235801 83920309322587395136676851)
      ·
        refine ⟨125880463983881092705015277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83920309322587395136676851 125880463983881092705015277)
        ·
          refine ⟨47205173993955409764380729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125880463983881092705015277 47205173993955409764380729)
          ·
            refine ⟨35403880495466557323285547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47205173993955409764380729 35403880495466557323285547)
            ·
              refine ⟨53105820743199835984928321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35403880495466557323285547 53105820743199835984928321)
              ·
                refine ⟨39829365557399876988696241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53105820743199835984928321 39829365557399876988696241)
                ·
                  refine ⟨29872024168049907741522181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39829365557399876988696241 29872024168049907741522181)
                  ·
                    refine ⟨5601004531509357701535409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29872024168049907741522181 5601004531509357701535409)
                    ·
                      refine ⟨4200753398632018276151557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601004531509357701535409 4200753398632018276151557)
                      ·
                        rfl

theorem cell23_8180938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_8180938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8180938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8180938 prefixEnd_8180938 := by exact prefixLift 8180938
  have htrace : WordTrace (prefixWord ++ tailWord_8180938) baseStart_8180938 baseEnd_8180938 := by
    simpa [prefixWord, tailWord_8180938, baseEnd_8180938] using wordTrace_append hprefix tailTrace_8180938
  have hstable : (prefixWord ++ tailWord_8180938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8180938).length < 2 ^ (prefixWord ++ tailWord_8180938).sum := by decide
  have hdescent : baseEnd_8180938 < baseStart_8180938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8180938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181028 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_8181028 : Nat := 118140960795 + 8181028 * 2 ^ 59
def prefixEnd_8181028 : Nat := 4983230072969 + 3 ^ 40 * 8181028 * 2
def baseEnd_8181028 : Nat := 4200799611890922924026143

theorem tailTrace_8181028 : CollatzResearch.WordTrace tailWord_8181028 prefixEnd_8181028 4200799611890922924026143 := by
  unfold tailWord_8181028
  simp only [CollatzResearch.WordTrace]
  refine ⟨149193302302770119595035869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198924403070360159460047825 149193302302770119595035869)
  ·
    refine ⟨55947488363538794848138451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149193302302770119595035869 55947488363538794848138451)
    ·
      refine ⟨83921232545308192272207677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55947488363538794848138451 83921232545308192272207677)
      ·
        refine ⟨31470462204490572102077879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83921232545308192272207677 31470462204490572102077879)
        ·
          refine ⟨47205693306735858153116819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31470462204490572102077879 47205693306735858153116819)
          ·
            refine ⟨70808539960103787229675229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47205693306735858153116819 70808539960103787229675229)
            ·
              refine ⟨26553202485038920211128211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70808539960103787229675229 26553202485038920211128211)
              ·
                refine ⟨39829803727558380316692317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26553202485038920211128211 39829803727558380316692317)
                ·
                  refine ⟨14936176397834392618759619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39829803727558380316692317 14936176397834392618759619)
                  ·
                    refine ⟨22404264596751588928139429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14936176397834392618759619 22404264596751588928139429)
                    ·
                      refine ⟨4200799611890922924026143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22404264596751588928139429 4200799611890922924026143)
                      ·
                        rfl

theorem cell23_8181028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_8181028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181028 prefixEnd_8181028 := by exact prefixLift 8181028
  have htrace : WordTrace (prefixWord ++ tailWord_8181028) baseStart_8181028 baseEnd_8181028 := by
    simpa [prefixWord, tailWord_8181028, baseEnd_8181028] using wordTrace_append hprefix tailTrace_8181028
  have hstable : (prefixWord ++ tailWord_8181028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181028).length < 2 ^ (prefixWord ++ tailWord_8181028).sum := by decide
  have hdescent : baseEnd_8181028 < baseStart_8181028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181032 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_8181032 : Nat := 118140960795 + 8181032 * 2 ^ 59
def prefixEnd_8181032 : Nat := 4983230072969 + 3 ^ 40 * 8181032 * 2
def baseEnd_8181032 : Nat := 4200801665813540908376125

theorem tailTrace_8181032 : CollatzResearch.WordTrace tailWord_8181032 prefixEnd_8181032 4200801665813540908376125 := by
  unfold tailWord_8181032
  simp only [CollatzResearch.WordTrace]
  refine ⟨149193375248762873936608675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198924500331683831915478233 149193375248762873936608675)
  ·
    refine ⟨223790062873144310904913013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149193375248762873936608675 223790062873144310904913013)
    ·
      refine ⟨20980318394357279147335595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223790062873144310904913013 20980318394357279147335595)
      ·
        refine ⟨31470477591535918721003393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20980318394357279147335595 31470477591535918721003393)
        ·
          refine ⟨23602858193651939040752545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31470477591535918721003393 23602858193651939040752545)
          ·
            refine ⟨17702143645238954280564409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23602858193651939040752545 17702143645238954280564409)
            ·
              refine ⟨13276607733929215710423307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17702143645238954280564409 13276607733929215710423307)
              ·
                refine ⟨19914911600893823565634961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276607733929215710423307 19914911600893823565634961)
                ·
                  refine ⟨14936183700670367674226221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19914911600893823565634961 14936183700670367674226221)
                  ·
                    refine ⟨5601068887751387877834833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14936183700670367674226221 5601068887751387877834833)
                    ·
                      refine ⟨4200801665813540908376125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601068887751387877834833 4200801665813540908376125)
                      ·
                        rfl

theorem cell23_8181032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_8181032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181032 prefixEnd_8181032 := by exact prefixLift 8181032
  have htrace : WordTrace (prefixWord ++ tailWord_8181032) baseStart_8181032 baseEnd_8181032 := by
    simpa [prefixWord, tailWord_8181032, baseEnd_8181032] using wordTrace_append hprefix tailTrace_8181032
  have hstable : (prefixWord ++ tailWord_8181032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181032).length < 2 ^ (prefixWord ++ tailWord_8181032).sum := by decide
  have hdescent : baseEnd_8181032 < baseStart_8181032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181055 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 2, 4]
def baseStart_8181055 : Nat := 118140960795 + 8181055 * 2 ^ 59
def prefixEnd_8181055 : Nat := 4983230072969 + 3 ^ 40 * 8181055 * 2
def baseEnd_8181055 : Nat := 1400271158622864772796173

theorem tailTrace_8181055 : CollatzResearch.WordTrace tailWord_8181055 prefixEnd_8181055 1400271158622864772796173 := by
  unfold tailWord_8181055
  simp only [CollatzResearch.WordTrace]
  refine ⟨298387589376442422801304619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198925059584294948534203079 298387589376442422801304619)
  ·
    refine ⟨447581384064663634201956929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298387589376442422801304619 447581384064663634201956929)
    ·
      refine ⟨335686038048497725651467697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447581384064663634201956929 335686038048497725651467697)
      ·
        refine ⟨251764528536373294238600773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335686038048497725651467697 251764528536373294238600773)
        ·
          refine ⟨47205849100569992669737645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251764528536373294238600773 47205849100569992669737645)
          ·
            refine ⟨17702193412713747251151617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47205849100569992669737645 17702193412713747251151617)
            ·
              refine ⟨13276645059535310438363713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17702193412713747251151617 13276645059535310438363713)
              ·
                refine ⟨9957483794651482828772785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13276645059535310438363713 9957483794651482828772785)
                ·
                  refine ⟨7468112845988612121579589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957483794651482828772785 7468112845988612121579589)
                  ·
                    refine ⟨1400271158622864772796173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7468112845988612121579589 1400271158622864772796173)
                    ·
                      rfl

theorem cell23_8181055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_8181055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181055 prefixEnd_8181055 := by exact prefixLift 8181055
  have htrace : WordTrace (prefixWord ++ tailWord_8181055) baseStart_8181055 baseEnd_8181055 := by
    simpa [prefixWord, tailWord_8181055, baseEnd_8181055] using wordTrace_append hprefix tailTrace_8181055
  have hstable : (prefixWord ++ tailWord_8181055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181055).length < 2 ^ (prefixWord ++ tailWord_8181055).sum := by decide
  have hdescent : baseEnd_8181055 < baseStart_8181055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181068 : List Nat := [2, 2, 1, 3, 2, 4, 1, 8]
def baseStart_8181068 : Nat := 118140960795 + 8181068 * 2 ^ 59
def prefixEnd_8181068 : Nat := 4983230072969 + 3 ^ 40 * 8181068 * 2
def baseEnd_8181068 : Nat := 155585931522855658056517

theorem tailTrace_8181068 : CollatzResearch.WordTrace tailWord_8181068 prefixEnd_8181068 155585931522855658056517 := by
  unfold tailWord_8181068
  simp only [CollatzResearch.WordTrace]
  refine ⟨149194031762697663010763929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198925375683596884014351905 149194031762697663010763929)
  ·
    refine ⟨111895523822023247258072947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149194031762697663010763929 111895523822023247258072947)
    ·
      refine ⟨167843285733034870887109421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111895523822023247258072947 167843285733034870887109421)
      ·
        refine ⟨62941232149888076582666033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167843285733034870887109421 62941232149888076582666033)
        ·
          refine ⟨47205924112416057436999525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62941232149888076582666033 47205924112416057436999525)
          ·
            refine ⟨8851110771078010769437411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47205924112416057436999525 8851110771078010769437411)
            ·
              refine ⟨13276666156617016154156117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851110771078010769437411 13276666156617016154156117)
              ·
                refine ⟨155585931522855658056517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13276666156617016154156117 155585931522855658056517)
                ·
                  rfl

theorem cell23_8181068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 8].length) (baseStart_8181068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181068 prefixEnd_8181068 := by exact prefixLift 8181068
  have htrace : WordTrace (prefixWord ++ tailWord_8181068) baseStart_8181068 baseEnd_8181068 := by
    simpa [prefixWord, tailWord_8181068, baseEnd_8181068] using wordTrace_append hprefix tailTrace_8181068
  have hstable : (prefixWord ++ tailWord_8181068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181068).length < 2 ^ (prefixWord ++ tailWord_8181068).sum := by decide
  have hdescent : baseEnd_8181068 < baseStart_8181068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181096 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_8181096 : Nat := 118140960795 + 8181096 * 2 ^ 59
def prefixEnd_8181096 : Nat := 4983230072969 + 3 ^ 40 * 8181096 * 2
def baseEnd_8181096 : Nat := 4200834528575428657975831

theorem tailTrace_8181096 : CollatzResearch.WordTrace tailWord_8181096 prefixEnd_8181096 4200834528575428657975831 := by
  unfold tailWord_8181096
  simp only [CollatzResearch.WordTrace]
  refine ⟨149194542384646943401773571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198926056512862591202364761 149194542384646943401773571)
  ·
    refine ⟨223791813576970415102660357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149194542384646943401773571 223791813576970415102660357)
    ·
      refine ⟨41960965045681952831748817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223791813576970415102660357 41960965045681952831748817)
      ·
        refine ⟨31470723784261464623811613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41960965045681952831748817 31470723784261464623811613)
        ·
          refine ⟨11801521419098049233929355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31470723784261464623811613 11801521419098049233929355)
          ·
            refine ⟨17702282128647073850894033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801521419098049233929355 17702282128647073850894033)
            ·
              refine ⟨13276711596485305388170525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17702282128647073850894033 13276711596485305388170525)
              ·
                refine ⟨4978766848681989520563947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13276711596485305388170525 4978766848681989520563947)
                ·
                  refine ⟨7468150273022984280845921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978766848681989520563947 7468150273022984280845921)
                  ·
                    refine ⟨5601112704767238210634441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468150273022984280845921 5601112704767238210634441)
                    ·
                      refine ⟨4200834528575428657975831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601112704767238210634441 4200834528575428657975831)
                      ·
                        rfl

theorem cell23_8181096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_8181096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181096 prefixEnd_8181096 := by exact prefixLift 8181096
  have htrace : WordTrace (prefixWord ++ tailWord_8181096) baseStart_8181096 baseEnd_8181096 := by
    simpa [prefixWord, tailWord_8181096, baseEnd_8181096] using wordTrace_append hprefix tailTrace_8181096
  have hstable : (prefixWord ++ tailWord_8181096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181096).length < 2 ^ (prefixWord ++ tailWord_8181096).sum := by decide
  have hdescent : baseEnd_8181096 < baseStart_8181096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181111 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 4, 6]
def baseStart_8181111 : Nat := 118140960795 + 8181111 * 2 ^ 59
def prefixEnd_8181111 : Nat := 4983230072969 + 3 ^ 40 * 8181111 * 2
def baseEnd_8181111 : Nat := 1400280743595082033096087

theorem tailTrace_8181111 : CollatzResearch.WordTrace tailWord_8181111 prefixEnd_8181111 1400280743595082033096087 := by
  unfold tailWord_8181111
  simp only [CollatzResearch.WordTrace]
  refine ⟨298389631864239544365343187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198926421242826362910228791 298389631864239544365343187)
  ·
    refine ⟨447584447796359316548014781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298389631864239544365343187 447584447796359316548014781)
    ·
      refine ⟨167844167923634743705505543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447584447796359316548014781 167844167923634743705505543)
      ·
        refine ⟨251766251885452115558258315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167844167923634743705505543 251766251885452115558258315)
        ·
          refine ⟨377649377828178173337387473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251766251885452115558258315 377649377828178173337387473)
          ·
            refine ⟨283237033371133630003040605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377649377828178173337387473 283237033371133630003040605)
            ·
              refine ⟨106213887514175111251140227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283237033371133630003040605 106213887514175111251140227)
              ·
                refine ⟨159320831271262666876710341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106213887514175111251140227 159320831271262666876710341)
                ·
                  refine ⟨29872655863361750039383189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159320831271262666876710341 29872655863361750039383189)
                  ·
                    refine ⟨1400280743595082033096087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29872655863361750039383189 1400280743595082033096087)
                    ·
                      rfl

theorem cell23_8181111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_8181111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181111 prefixEnd_8181111 := by exact prefixLift 8181111
  have htrace : WordTrace (prefixWord ++ tailWord_8181111) baseStart_8181111 baseEnd_8181111 := by
    simpa [prefixWord, tailWord_8181111, baseEnd_8181111] using wordTrace_append hprefix tailTrace_8181111
  have hstable : (prefixWord ++ tailWord_8181111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181111).length < 2 ^ (prefixWord ++ tailWord_8181111).sum := by decide
  have hdescent : baseEnd_8181111 < baseStart_8181111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181128 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_8181128 : Nat := 118140960795 + 8181128 * 2 ^ 59
def prefixEnd_8181128 : Nat := 4983230072969 + 3 ^ 40 * 8181128 * 2
def baseEnd_8181128 : Nat := 1400283653318790844258561

theorem tailTrace_8181128 : CollatzResearch.WordTrace tailWord_8181128 prefixEnd_8181128 1400283653318790844258561 := by
  unfold tailWord_8181128
  simp only [CollatzResearch.WordTrace]
  refine ⟨149195125952588978134356019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198926834603451970845808025 149195125952588978134356019)
  ·
    refine ⟨223792688928883467201534029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149195125952588978134356019 223792688928883467201534029)
    ·
      refine ⟨83922258348331300200575261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223792688928883467201534029 83922258348331300200575261)
      ·
        refine ⟨31470846880624237575215723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83922258348331300200575261 31470846880624237575215723)
        ·
          refine ⟨47206270320936356362823585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31470846880624237575215723 47206270320936356362823585)
          ·
            refine ⟨35404702740702267272117689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47206270320936356362823585 35404702740702267272117689)
            ·
              refine ⟨26553527055526700454088267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35404702740702267272117689 26553527055526700454088267)
              ·
                refine ⟨39830290583290050681132401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26553527055526700454088267 39830290583290050681132401)
                ·
                  refine ⟨29872717937467538010849301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39830290583290050681132401 29872717937467538010849301)
                  ·
                    refine ⟨1400283653318790844258561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29872717937467538010849301 1400283653318790844258561)
                    ·
                      rfl

theorem cell23_8181128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_8181128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181128 prefixEnd_8181128 := by exact prefixLift 8181128
  have htrace : WordTrace (prefixWord ++ tailWord_8181128) baseStart_8181128 baseEnd_8181128 := by
    simpa [prefixWord, tailWord_8181128, baseEnd_8181128] using wordTrace_append hprefix tailTrace_8181128
  have hstable : (prefixWord ++ tailWord_8181128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181128).length < 2 ^ (prefixWord ++ tailWord_8181128).sum := by decide
  have hdescent : baseEnd_8181128 < baseStart_8181128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181129 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 2, 1, 3]
def baseStart_8181129 : Nat := 118140960795 + 8181129 * 2 ^ 59
def prefixEnd_8181129 : Nat := 4983230072969 + 3 ^ 40 * 8181129 * 2
def baseEnd_8181129 : Nat := 4200851473437027028863179

theorem tailTrace_8181129 : CollatzResearch.WordTrace tailWord_8181129 prefixEnd_8181129 4200851473437027028863179 := by
  unfold tailWord_8181129
  simp only [CollatzResearch.WordTrace]
  refine ⟨298390288378174333439498441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198926858918782888959665627 298390288378174333439498441)
  ·
    refine ⟨223792716283630750079623831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298390288378174333439498441 223792716283630750079623831)
    ·
      refine ⟨335689074425446125119435747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223792716283630750079623831 335689074425446125119435747)
      ·
        refine ⟨503533611638169187679153621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335689074425446125119435747 503533611638169187679153621)
        ·
          refine ⟨11801569022769590336230163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 503533611638169187679153621 11801569022769590336230163)
          ·
            refine ⟨17702353534154385504345245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801569022769590336230163 17702353534154385504345245)
            ·
              refine ⟨6638382575307894564129467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17702353534154385504345245 6638382575307894564129467)
              ·
                refine ⟨9957573862961841846194201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638382575307894564129467 9957573862961841846194201)
                ·
                  refine ⟨7468180397221381384645651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957573862961841846194201 7468180397221381384645651)
                  ·
                    refine ⟨11202270595832072076968477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468180397221381384645651 11202270595832072076968477)
                    ·
                      refine ⟨4200851473437027028863179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202270595832072076968477 4200851473437027028863179)
                      ·
                        rfl

theorem cell23_8181129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 1, 3].length) (baseStart_8181129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181129 prefixEnd_8181129 := by exact prefixLift 8181129
  have htrace : WordTrace (prefixWord ++ tailWord_8181129) baseStart_8181129 baseEnd_8181129 := by
    simpa [prefixWord, tailWord_8181129, baseEnd_8181129] using wordTrace_append hprefix tailTrace_8181129
  have hstable : (prefixWord ++ tailWord_8181129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181129).length < 2 ^ (prefixWord ++ tailWord_8181129).sum := by decide
  have hdescent : baseEnd_8181129 < baseStart_8181129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181161 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_8181161 : Nat := 118140960795 + 8181161 * 2 ^ 59
def prefixEnd_8181161 : Nat := 4983230072969 + 3 ^ 40 * 8181161 * 2
def baseEnd_8181161 : Nat := 4200867904817970903663031

theorem tailTrace_8181161 : CollatzResearch.WordTrace tailWord_8181161 prefixEnd_8181161 4200867904817970903663031 := by
  unfold tailWord_8181161
  simp only [CollatzResearch.WordTrace]
  refine ⟨298391455514058402904663337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198927637009372268603108891 298391455514058402904663337)
  ·
    refine ⟨223793591635543802178497503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298391455514058402904663337 223793591635543802178497503)
    ·
      refine ⟨335690387453315703267746255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223793591635543802178497503 335690387453315703267746255)
      ·
        refine ⟨503535581179973554901619383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335690387453315703267746255 503535581179973554901619383)
        ·
          refine ⟨755303371769960332352429075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503535581179973554901619383 755303371769960332352429075)
          ·
            refine ⟨1132955057654940498528643613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755303371769960332352429075 1132955057654940498528643613)
            ·
              refine ⟨424858146620602686948241355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1132955057654940498528643613 424858146620602686948241355)
              ·
                refine ⟨637287219930904030422362033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424858146620602686948241355 637287219930904030422362033)
                ·
                  refine ⟨477965414948178022816771525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637287219930904030422362033 477965414948178022816771525)
                  ·
                    refine ⟨89618515302783379278144661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477965414948178022816771525 89618515302783379278144661)
                    ·
                      refine ⟨4200867904817970903663031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89618515302783379278144661 4200867904817970903663031)
                      ·
                        rfl

theorem cell23_8181161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_8181161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181161 prefixEnd_8181161 := by exact prefixLift 8181161
  have htrace : WordTrace (prefixWord ++ tailWord_8181161) baseStart_8181161 baseEnd_8181161 := by
    simpa [prefixWord, tailWord_8181161, baseEnd_8181161] using wordTrace_append hprefix tailTrace_8181161
  have hstable : (prefixWord ++ tailWord_8181161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181161).length < 2 ^ (prefixWord ++ tailWord_8181161).sum := by decide
  have hdescent : baseEnd_8181161 < baseStart_8181161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181168 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_8181168 : Nat := 118140960795 + 8181168 * 2 ^ 59
def prefixEnd_8181168 : Nat := 4983230072969 + 3 ^ 40 * 8181168 * 2
def baseEnd_8181168 : Nat := 4200871499182552376275499

theorem tailTrace_8181168 : CollatzResearch.WordTrace tailWord_8181168 prefixEnd_8181168 4200871499182552376275499 := by
  unfold tailWord_8181168
  simp only [CollatzResearch.WordTrace]
  refine ⟨149195855412516521550084079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198927807216688695400112105 149195855412516521550084079)
  ·
    refine ⟨223793783118774782325126119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149195855412516521550084079 223793783118774782325126119)
    ·
      refine ⟨335690674678162173487689179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223793783118774782325126119 335690674678162173487689179)
      ·
        refine ⟨503536012017243260231533769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335690674678162173487689179 503536012017243260231533769)
        ·
          refine ⟨377652009012932445173650327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503536012017243260231533769 377652009012932445173650327)
          ·
            refine ⟨566478013519398667760475491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377652009012932445173650327 566478013519398667760475491)
            ·
              refine ⟨849717020279098001640713237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566478013519398667760475491 849717020279098001640713237)
              ·
                refine ⟨39830485325582718826908433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 849717020279098001640713237 39830485325582718826908433)
                ·
                  refine ⟨29872863994187039120181325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39830485325582718826908433 29872863994187039120181325)
                  ·
                    refine ⟨11202323997820139670067997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29872863994187039120181325 11202323997820139670067997)
                    ·
                      refine ⟨4200871499182552376275499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202323997820139670067997 4200871499182552376275499)
                      ·
                        rfl

theorem cell23_8181168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_8181168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181168 prefixEnd_8181168 := by exact prefixLift 8181168
  have htrace : WordTrace (prefixWord ++ tailWord_8181168) baseStart_8181168 baseEnd_8181168 := by
    simpa [prefixWord, tailWord_8181168, baseEnd_8181168] using wordTrace_append hprefix tailTrace_8181168
  have hstable : (prefixWord ++ tailWord_8181168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181168).length < 2 ^ (prefixWord ++ tailWord_8181168).sum := by decide
  have hdescent : baseEnd_8181168 < baseStart_8181168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181205 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_8181205 : Nat := 118140960795 + 8181205 * 2 ^ 59
def prefixEnd_8181205 : Nat := 4983230072969 + 3 ^ 40 * 8181205 * 2
def baseEnd_8181205 : Nat := 1400296832655589577170943

theorem tailTrace_8181205 : CollatzResearch.WordTrace tailWord_8181205 prefixEnd_8181205 1400296832655589577170943 := by
  unfold tailWord_8181205
  simp only [CollatzResearch.WordTrace]
  refine ⟨298393060325898998419265069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198928706883932665612843379 298393060325898998419265069)
  ·
    refine ⟨111897397622212124407224401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298393060325898998419265069 111897397622212124407224401)
    ·
      refine ⟨83923048216659093305418301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111897397622212124407224401 83923048216659093305418301)
      ·
        refine ⟨31471143081247159989531863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83923048216659093305418301 31471143081247159989531863)
        ·
          refine ⟨47206714621870739984297795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31471143081247159989531863 47206714621870739984297795)
          ·
            refine ⟨70810071932806109976446693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47206714621870739984297795 70810071932806109976446693)
            ·
              refine ⟨13276888487401145620583755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70810071932806109976446693 13276888487401145620583755)
              ·
                refine ⟨19915332731101718430875633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276888487401145620583755 19915332731101718430875633)
                ·
                  refine ⟨14936499548326288823156725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19915332731101718430875633 14936499548326288823156725)
                  ·
                    refine ⟨1400296832655589577170943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14936499548326288823156725 1400296832655589577170943)
                    ·
                      rfl

theorem cell23_8181205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_8181205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181205 prefixEnd_8181205 := by exact prefixLift 8181205
  have htrace : WordTrace (prefixWord ++ tailWord_8181205) baseStart_8181205 baseEnd_8181205 := by
    simpa [prefixWord, tailWord_8181205, baseEnd_8181205] using wordTrace_append hprefix tailTrace_8181205
  have hstable : (prefixWord ++ tailWord_8181205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181205).length < 2 ^ (prefixWord ++ tailWord_8181205).sum := by decide
  have hdescent : baseEnd_8181205 < baseStart_8181205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181208 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_8181208 : Nat := 118140960795 + 8181208 * 2 ^ 59
def prefixEnd_8181208 : Nat := 4983230072969 + 3 ^ 40 * 8181208 * 2
def baseEnd_8181208 : Nat := 4200892038408732219775315

theorem tailTrace_8181208 : CollatzResearch.WordTrace tailWord_8181208 prefixEnd_8181208 4200892038408732219775315 := by
  unfold tailWord_8181208
  simp only [CollatzResearch.WordTrace]
  refine ⟨149196584872444064965812139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198928779829925419954416185 149196584872444064965812139)
  ·
    refine ⟨223794877308666097448718209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149196584872444064965812139 223794877308666097448718209)
    ·
      refine ⟨167846157981499573086538657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223794877308666097448718209 167846157981499573086538657)
      ·
        refine ⟨125884618486124679814903993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167846157981499573086538657 125884618486124679814903993)
        ·
          refine ⟨94413463864593509861177995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125884618486124679814903993 94413463864593509861177995)
          ·
            refine ⟨141620195796890264791766993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94413463864593509861177995 141620195796890264791766993)
            ·
              refine ⟨106215146847667698593825245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141620195796890264791766993 106215146847667698593825245)
              ·
                refine ⟨39830680067875386972684467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106215146847667698593825245 39830680067875386972684467)
                ·
                  refine ⟨59746020101813080459026701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39830680067875386972684467 59746020101813080459026701)
                  ·
                    refine ⟨22404757538179905172135013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59746020101813080459026701 22404757538179905172135013)
                    ·
                      refine ⟨4200892038408732219775315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22404757538179905172135013 4200892038408732219775315)
                      ·
                        rfl

theorem cell23_8181208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_8181208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181208 prefixEnd_8181208 := by exact prefixLift 8181208
  have htrace : WordTrace (prefixWord ++ tailWord_8181208) baseStart_8181208 baseEnd_8181208 := by
    simpa [prefixWord, tailWord_8181208, baseEnd_8181208] using wordTrace_append hprefix tailTrace_8181208
  have hstable : (prefixWord ++ tailWord_8181208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181208).length < 2 ^ (prefixWord ++ tailWord_8181208).sum := by decide
  have hdescent : baseEnd_8181208 < baseStart_8181208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181226 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_8181226 : Nat := 118140960795 + 8181226 * 2 ^ 59
def prefixEnd_8181226 : Nat := 4983230072969 + 3 ^ 40 * 8181226 * 2
def baseEnd_8181226 : Nat := 466766809006723683261137

theorem tailTrace_8181226 : CollatzResearch.WordTrace tailWord_8181226 prefixEnd_8181226 466766809006723683261137 := by
  unfold tailWord_8181226
  simp only [CollatzResearch.WordTrace]
  refine ⟨74598456564705729751444883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198929217505881946003853021 74598456564705729751444883)
  ·
    refine ⟨111897684847058594627167325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74598456564705729751444883 111897684847058594627167325)
    ·
      refine ⟨41961631817646972985187747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111897684847058594627167325 41961631817646972985187747)
      ·
        refine ⟨62942447726470459477781621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41961631817646972985187747 62942447726470459477781621)
        ·
          refine ⟨5900854474356605576042027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62942447726470459477781621 5900854474356605576042027)
          ·
            refine ⟨8851281711534908364063041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900854474356605576042027 8851281711534908364063041)
            ·
              refine ⟨6638461283651181273047281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8851281711534908364063041 6638461283651181273047281)
              ·
                refine ⟨4978845962738385954785461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6638461283651181273047281 4978845962738385954785461)
                ·
                  refine ⟨466766809006723683261137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4978845962738385954785461 466766809006723683261137)
                  ·
                    rfl

theorem cell23_8181226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_8181226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181226 prefixEnd_8181226 := by exact prefixLift 8181226
  have htrace : WordTrace (prefixWord ++ tailWord_8181226) baseStart_8181226 baseEnd_8181226 := by
    simpa [prefixWord, tailWord_8181226, baseEnd_8181226] using wordTrace_append hprefix tailTrace_8181226
  have hstable : (prefixWord ++ tailWord_8181226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181226).length < 2 ^ (prefixWord ++ tailWord_8181226).sum := by decide
  have hdescent : baseEnd_8181226 < baseStart_8181226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181259 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 2, 1, 4]
def baseStart_8181259 : Nat := 118140960795 + 8181259 * 2 ^ 59
def prefixEnd_8181259 : Nat := 4983230072969 + 3 ^ 40 * 8181259 * 2
def baseEnd_8181259 : Nat := 4200918225922111520237581

theorem tailTrace_8181259 : CollatzResearch.WordTrace tailWord_8181259 prefixEnd_8181259 4200918225922111520237581 := by
  unfold tailWord_8181259
  simp only [CollatzResearch.WordTrace]
  refine ⟨298395029867703365641730831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198930019911802243761153887 298395029867703365641730831)
  ·
    refine ⟨447592544801555048462596247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298395029867703365641730831 447592544801555048462596247)
    ·
      refine ⟨671388817202332572693894371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447592544801555048462596247 671388817202332572693894371)
      ·
        refine ⟨1007083225803498859040841557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671388817202332572693894371 1007083225803498859040841557)
        ·
          refine ⟨5900878276192376127192431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 1007083225803498859040841557 5900878276192376127192431)
          ·
            refine ⟨8851317414288564190788647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900878276192376127192431 8851317414288564190788647)
            ·
              refine ⟨13276976121432846286182971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851317414288564190788647 13276976121432846286182971)
              ·
                refine ⟨19915464182149269429274457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276976121432846286182971 19915464182149269429274457)
                ·
                  refine ⟨14936598136611952071955843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19915464182149269429274457 14936598136611952071955843)
                  ·
                    refine ⟨22404897204917928107933765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14936598136611952071955843 22404897204917928107933765)
                    ·
                      refine ⟨4200918225922111520237581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22404897204917928107933765 4200918225922111520237581)
                      ·
                        rfl

theorem cell23_8181259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 1, 4].length) (baseStart_8181259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181259 prefixEnd_8181259 := by exact prefixLift 8181259
  have htrace : WordTrace (prefixWord ++ tailWord_8181259) baseStart_8181259 baseEnd_8181259 := by
    simpa [prefixWord, tailWord_8181259, baseEnd_8181259] using wordTrace_append hprefix tailTrace_8181259
  have hstable : (prefixWord ++ tailWord_8181259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181259).length < 2 ^ (prefixWord ++ tailWord_8181259).sum := by decide
  have hdescent : baseEnd_8181259 < baseStart_8181259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181262 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_8181262 : Nat := 118140960795 + 8181262 * 2 ^ 59
def prefixEnd_8181262 : Nat := 4983230072969 + 3 ^ 40 * 8181262 * 2
def baseEnd_8181262 : Nat := 4200919766364075008500067

theorem tailTrace_8181262 : CollatzResearch.WordTrace tailWord_8181262 prefixEnd_8181262 4200919766364075008500067 := by
  unfold tailWord_8181262
  simp only [CollatzResearch.WordTrace]
  refine ⟨37299392410836562144261255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198930092857794998102726693 37299392410836562144261255)
  ·
    refine ⟨55949088616254843216391883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37299392410836562144261255 55949088616254843216391883)
    ·
      refine ⟨83923632924382264824587825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55949088616254843216391883 83923632924382264824587825)
      ·
        refine ⟨62942724693286698618440869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83923632924382264824587825 62942724693286698618440869)
        ·
          refine ⟨11801760879991255990957663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62942724693286698618440869 11801760879991255990957663)
          ·
            refine ⟨17702641319986883986436495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801760879991255990957663 17702641319986883986436495)
            ·
              refine ⟨26553961979980325979654743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17702641319986883986436495 26553961979980325979654743)
              ·
                refine ⟨39830942969970488969482115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26553961979980325979654743 39830942969970488969482115)
                ·
                  refine ⟨59746414454955733454223173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39830942969970488969482115 59746414454955733454223173)
                  ·
                    refine ⟨11202452710304200022666845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59746414454955733454223173 11202452710304200022666845)
                    ·
                      refine ⟨4200919766364075008500067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202452710304200022666845 4200919766364075008500067)
                      ·
                        rfl

theorem cell23_8181262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_8181262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181262 prefixEnd_8181262 := by exact prefixLift 8181262
  have htrace : WordTrace (prefixWord ++ tailWord_8181262) baseStart_8181262 baseEnd_8181262 := by
    simpa [prefixWord, tailWord_8181262, baseEnd_8181262] using wordTrace_append hprefix tailTrace_8181262
  have hstable : (prefixWord ++ tailWord_8181262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181262).length < 2 ^ (prefixWord ++ tailWord_8181262).sum := by decide
  have hdescent : baseEnd_8181262 < baseStart_8181262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181269 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_8181269 : Nat := 118140960795 + 8181269 * 2 ^ 59
def prefixEnd_8181269 : Nat := 4983230072969 + 3 ^ 40 * 8181269 * 2
def baseEnd_8181269 : Nat := 1400307786909552160370845

theorem tailTrace_8181269 : CollatzResearch.WordTrace tailWord_8181269 prefixEnd_8181269 1400307786909552160370845 := by
  unfold tailWord_8181269
  simp only [CollatzResearch.WordTrace]
  refine ⟨298395394597667137349594861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198930263065111424899729907 298395394597667137349594861)
  ·
    refine ⟨111898272974125176506098073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298395394597667137349594861 111898272974125176506098073)
    ·
      refine ⟨83923704730593882379573555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111898272974125176506098073 83923704730593882379573555)
      ·
        refine ⟨125885557095890823569360333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83923704730593882379573555 125885557095890823569360333)
        ·
          refine ⟨47207083910959058838510125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125885557095890823569360333 47207083910959058838510125)
          ·
            refine ⟨17702656466609647064441297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47207083910959058838510125 17702656466609647064441297)
            ·
              refine ⟨13276992349957235298330973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17702656466609647064441297 13276992349957235298330973)
              ·
                refine ⟨4978872131233963236874115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13276992349957235298330973 4978872131233963236874115)
                ·
                  refine ⟨7468308196850944855311173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978872131233963236874115 7468308196850944855311173)
                  ·
                    refine ⟨1400307786909552160370845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7468308196850944855311173 1400307786909552160370845)
                    ·
                      rfl

theorem cell23_8181269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_8181269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181269 prefixEnd_8181269 := by exact prefixLift 8181269
  have htrace : WordTrace (prefixWord ++ tailWord_8181269) baseStart_8181269 baseEnd_8181269 := by
    simpa [prefixWord, tailWord_8181269, baseEnd_8181269] using wordTrace_append hprefix tailTrace_8181269
  have hstable : (prefixWord ++ tailWord_8181269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181269).length < 2 ^ (prefixWord ++ tailWord_8181269).sum := by decide
  have hdescent : baseEnd_8181269 < baseStart_8181269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181332 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_8181332 : Nat := 118140960795 + 8181332 * 2 ^ 59
def prefixEnd_8181332 : Nat := 4983230072969 + 3 ^ 40 * 8181332 * 2
def baseEnd_8181332 : Nat := 4200955710009889734624745

theorem tailTrace_8181332 : CollatzResearch.WordTrace tailWord_8181332 prefixEnd_8181332 4200955710009889734624745 := by
  unfold tailWord_8181332
  simp only [CollatzResearch.WordTrace]
  refine ⟨149198846198219449554569125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198931794930959266072758833 149198846198219449554569125)
  ·
    refine ⟨27974783662166146791481711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149198846198219449554569125 27974783662166146791481711)
    ·
      refine ⟨41962175493249220187222567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27974783662166146791481711 41962175493249220187222567)
      ·
        refine ⟨62943263239873830280833851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41962175493249220187222567 62943263239873830280833851)
        ·
          refine ⟨94414894859810745421250777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62943263239873830280833851 94414894859810745421250777)
          ·
            refine ⟨70811171144858059065938083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94414894859810745421250777 70811171144858059065938083)
            ·
              refine ⟨106216756717287088598907125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70811171144858059065938083 106216756717287088598907125)
              ·
                refine ⟨9957820942245664556147543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106216756717287088598907125 9957820942245664556147543)
                ·
                  refine ⟨14936731413368496834221315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9957820942245664556147543 14936731413368496834221315)
                  ·
                    refine ⟨22405097120052745251331973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14936731413368496834221315 22405097120052745251331973)
                    ·
                      refine ⟨4200955710009889734624745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22405097120052745251331973 4200955710009889734624745)
                      ·
                        rfl

theorem cell23_8181332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_8181332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181332 prefixEnd_8181332 := by exact prefixLift 8181332
  have htrace : WordTrace (prefixWord ++ tailWord_8181332) baseStart_8181332 baseEnd_8181332 := by
    simpa [prefixWord, tailWord_8181332, baseEnd_8181332] using wordTrace_append hprefix tailTrace_8181332
  have hstable : (prefixWord ++ tailWord_8181332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181332).length < 2 ^ (prefixWord ++ tailWord_8181332).sum := by decide
  have hdescent : baseEnd_8181332 < baseStart_8181332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181335 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_8181335 : Nat := 118140960795 + 8181335 * 2 ^ 59
def prefixEnd_8181335 : Nat := 4983230072969 + 3 ^ 40 * 8181335 * 2
def baseEnd_8181335 : Nat := 4200957250451853222887231

theorem tailTrace_8181335 : CollatzResearch.WordTrace tailWord_8181335 prefixEnd_8181335 4200957250451853222887231 := by
  unfold tailWord_8181335
  simp only [CollatzResearch.WordTrace]
  refine ⟨298397801815428030621497459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198931867876952020414331639 298397801815428030621497459)
  ·
    refine ⟨447596702723142045932246189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298397801815428030621497459 447596702723142045932246189)
    ·
      refine ⟨167848763521178267224592321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447596702723142045932246189 167848763521178267224592321)
      ·
        refine ⟨125886572640883700418444241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167848763521178267224592321 125886572640883700418444241)
        ·
          refine ⟨94414929480662775313833181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125886572640883700418444241 94414929480662775313833181)
          ·
            refine ⟨35405598555248540742687443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94414929480662775313833181 35405598555248540742687443)
            ·
              refine ⟨53108397832872811114031165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35405598555248540742687443 53108397832872811114031165)
              ·
                refine ⟨19915649187327304167761687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53108397832872811114031165 19915649187327304167761687)
                ·
                  refine ⟨29873473780990956251642531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19915649187327304167761687 29873473780990956251642531)
                  ·
                    refine ⟨44810210671486434377463797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29873473780990956251642531 44810210671486434377463797)
                    ·
                      refine ⟨4200957250451853222887231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44810210671486434377463797 4200957250451853222887231)
                      ·
                        rfl

theorem cell23_8181335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_8181335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181335 prefixEnd_8181335 := by exact prefixLift 8181335
  have htrace : WordTrace (prefixWord ++ tailWord_8181335) baseStart_8181335 baseEnd_8181335 := by
    simpa [prefixWord, tailWord_8181335, baseEnd_8181335] using wordTrace_append hprefix tailTrace_8181335
  have hstable : (prefixWord ++ tailWord_8181335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181335).length < 2 ^ (prefixWord ++ tailWord_8181335).sum := by decide
  have hdescent : baseEnd_8181335 < baseStart_8181335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181352 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_8181352 : Nat := 118140960795 + 8181352 * 2 ^ 59
def prefixEnd_8181352 : Nat := 4983230072969 + 3 ^ 40 * 8181352 * 2
def baseEnd_8181352 : Nat := 4200965979622979656374653

theorem tailTrace_8181352 : CollatzResearch.WordTrace tailWord_8181352 prefixEnd_8181352 4200965979622979656374653 := by
  unfold tailWord_8181352
  simp only [CollatzResearch.WordTrace]
  refine ⟨149199210928183221262433155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198932281237577628349910873 149199210928183221262433155)
  ·
    refine ⟨223798816392274831893649733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149199210928183221262433155 223798816392274831893649733)
    ·
      refine ⟨41962278073551530980059325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223798816392274831893649733 41962278073551530980059325)
      ·
        refine ⟨15735854277581824117522247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41962278073551530980059325 15735854277581824117522247)
        ·
          refine ⟨23603781416372736176283371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15735854277581824117522247 23603781416372736176283371)
          ·
            refine ⟨35405672124559104264425057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23603781416372736176283371 35405672124559104264425057)
            ·
              refine ⟨26554254093419328198318793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35405672124559104264425057 26554254093419328198318793)
              ·
                refine ⟨19915690570064496148739095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26554254093419328198318793 19915690570064496148739095)
                ·
                  refine ⟨29873535855096744223108643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19915690570064496148739095 29873535855096744223108643)
                  ·
                    refine ⟨44810303782645116334662965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29873535855096744223108643 44810303782645116334662965)
                    ·
                      refine ⟨4200965979622979656374653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44810303782645116334662965 4200965979622979656374653)
                      ·
                        rfl

theorem cell23_8181352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_8181352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181352 prefixEnd_8181352 := by exact prefixLift 8181352
  have htrace : WordTrace (prefixWord ++ tailWord_8181352) baseStart_8181352 baseEnd_8181352 := by
    simpa [prefixWord, tailWord_8181352, baseEnd_8181352] using wordTrace_append hprefix tailTrace_8181352
  have hstable : (prefixWord ++ tailWord_8181352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181352).length < 2 ^ (prefixWord ++ tailWord_8181352).sum := by decide
  have hdescent : baseEnd_8181352 < baseStart_8181352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181366 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_8181366 : Nat := 118140960795 + 8181366 * 2 ^ 59
def prefixEnd_8181366 : Nat := 4983230072969 + 3 ^ 40 * 8181366 * 2
def baseEnd_8181366 : Nat := 4200973168352142601599589

theorem tailTrace_8181366 : CollatzResearch.WordTrace tailWord_8181366 prefixEnd_8181366 4200973168352142601599589 := by
  unfold tailWord_8181366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18649933279894732682242247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198932621652210481943917301 18649933279894732682242247)
  ·
    refine ⟨27974899919842099023363371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18649933279894732682242247 27974899919842099023363371)
    ·
      refine ⟨41962349879763148535045057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27974899919842099023363371 41962349879763148535045057)
      ·
        refine ⟨31471762409822361401283793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41962349879763148535045057 31471762409822361401283793)
        ·
          refine ⟨23603821807366771050962845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31471762409822361401283793 23603821807366771050962845)
          ·
            refine ⟨8851433177762539144111067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23603821807366771050962845 8851433177762539144111067)
            ·
              refine ⟨13277149766643808716166601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851433177762539144111067 13277149766643808716166601)
              ·
                refine ⟨9957862324982856537124951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13277149766643808716166601 9957862324982856537124951)
                ·
                  refine ⟨14936793487474284805687427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9957862324982856537124951 14936793487474284805687427)
                  ·
                    refine ⟨22405190231211427208531141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14936793487474284805687427 22405190231211427208531141)
                    ·
                      refine ⟨4200973168352142601599589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22405190231211427208531141 4200973168352142601599589)
                      ·
                        rfl

theorem cell23_8181366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_8181366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181366 prefixEnd_8181366 := by exact prefixLift 8181366
  have htrace : WordTrace (prefixWord ++ tailWord_8181366) baseStart_8181366 baseEnd_8181366 := by
    simpa [prefixWord, tailWord_8181366, baseEnd_8181366] using wordTrace_append hprefix tailTrace_8181366
  have hstable : (prefixWord ++ tailWord_8181366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181366).length < 2 ^ (prefixWord ++ tailWord_8181366).sum := by decide
  have hdescent : baseEnd_8181366 < baseStart_8181366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181386 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_8181386 : Nat := 118140960795 + 8181386 * 2 ^ 59
def prefixEnd_8181386 : Nat := 4983230072969 + 3 ^ 40 * 8181386 * 2
def baseEnd_8181386 : Nat := 4200983437965232523349497

theorem tailTrace_8181386 : CollatzResearch.WordTrace tailWord_8181386 prefixEnd_8181386 4200983437965232523349497 := by
  unfold tailWord_8181386
  simp only [CollatzResearch.WordTrace]
  refine ⟨74599915484560816582901003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198933107958828844221069341 74599915484560816582901003)
  ·
    refine ⟨111899873226841224874351505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74599915484560816582901003 111899873226841224874351505)
    ·
      refine ⟨83924904920130918655763629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111899873226841224874351505 83924904920130918655763629)
      ·
        refine ⟨31471839345049094495911361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83924904920130918655763629 31471839345049094495911361)
        ·
          refine ⟨23603879508786820871933521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31471839345049094495911361 23603879508786820871933521)
          ·
            refine ⟨17702909631590115653950141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23603879508786820871933521 17702909631590115653950141)
            ·
              refine ⟨6638591111846293370231303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17702909631590115653950141 6638591111846293370231303)
              ·
                refine ⟨9957886667769440055346955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638591111846293370231303 9957886667769440055346955)
                ·
                  refine ⟨14936830001654160083020433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9957886667769440055346955 14936830001654160083020433)
                  ·
                    refine ⟨11202622501240620062265325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14936830001654160083020433 11202622501240620062265325)
                    ·
                      refine ⟨4200983437965232523349497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202622501240620062265325 4200983437965232523349497)
                      ·
                        rfl

theorem cell23_8181386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_8181386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181386 prefixEnd_8181386 := by exact prefixLift 8181386
  have htrace : WordTrace (prefixWord ++ tailWord_8181386) baseStart_8181386 baseEnd_8181386 := by
    simpa [prefixWord, tailWord_8181386, baseEnd_8181386] using wordTrace_append hprefix tailTrace_8181386
  have hstable : (prefixWord ++ tailWord_8181386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181386).length < 2 ^ (prefixWord ++ tailWord_8181386).sum := by decide
  have hdescent : baseEnd_8181386 < baseStart_8181386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181399 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_8181399 : Nat := 118140960795 + 8181399 * 2 ^ 59
def prefixEnd_8181399 : Nat := 4983230072969 + 3 ^ 40 * 8181399 * 2
def baseEnd_8181399 : Nat := 4200990113213740972486937

theorem tailTrace_8181399 : CollatzResearch.WordTrace tailWord_8181399 prefixEnd_8181399 4200990113213740972486937 := by
  unfold tailWord_8181399
  simp only [CollatzResearch.WordTrace]
  refine ⟨298400136087196169551827251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198933424058130779701218167 298400136087196169551827251)
  ·
    refine ⟨447600204130794254327740877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298400136087196169551827251 447600204130794254327740877)
    ·
      refine ⟨167850076549047845372902829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447600204130794254327740877 167850076549047845372902829)
      ·
        refine ⟨62943778705892942014838561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167850076549047845372902829 62943778705892942014838561)
        ·
          refine ⟨47207834029419706511128921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62943778705892942014838561 47207834029419706511128921)
          ·
            refine ⟨35405875522064779883346691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47207834029419706511128921 35405875522064779883346691)
            ·
              refine ⟨53108813283097169825020037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35405875522064779883346691 53108813283097169825020037)
              ·
                refine ⟨9957902490580719342191257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53108813283097169825020037 9957902490580719342191257)
                ·
                  refine ⟨7468426867935539506643443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957902490580719342191257 7468426867935539506643443)
                  ·
                    refine ⟨11202640301903309259965165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468426867935539506643443 11202640301903309259965165)
                    ·
                      refine ⟨4200990113213740972486937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202640301903309259965165 4200990113213740972486937)
                      ·
                        rfl

theorem cell23_8181399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_8181399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181399 prefixEnd_8181399 := by exact prefixLift 8181399
  have htrace : WordTrace (prefixWord ++ tailWord_8181399) baseStart_8181399 baseEnd_8181399 := by
    simpa [prefixWord, tailWord_8181399, baseEnd_8181399] using wordTrace_append hprefix tailTrace_8181399
  have hstable : (prefixWord ++ tailWord_8181399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181399).length < 2 ^ (prefixWord ++ tailWord_8181399).sum := by decide
  have hdescent : baseEnd_8181399 < baseStart_8181399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181400 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 1, 2, 2]
def baseStart_8181400 : Nat := 118140960795 + 8181400 * 2 ^ 59
def prefixEnd_8181400 : Nat := 4983230072969 + 3 ^ 40 * 8181400 * 2
def baseEnd_8181400 : Nat := 4200990626694395468574433

theorem tailTrace_8181400 : CollatzResearch.WordTrace tailWord_8181400 prefixEnd_8181400 4200990626694395468574433 := by
  unfold tailWord_8181400
  simp only [CollatzResearch.WordTrace]
  refine ⟨149200086280096273361306827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198933448373461697815075769 149200086280096273361306827)
  ·
    refine ⟨223800129420144410041960241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149200086280096273361306827 223800129420144410041960241)
    ·
      refine ⟨167850097065108307531470181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223800129420144410041960241 167850097065108307531470181)
      ·
        refine ⟨31471893199707807662150659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167850097065108307531470181 31471893199707807662150659)
        ·
          refine ⟨47207839799561711493225989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31471893199707807662150659 47207839799561711493225989)
          ·
            refine ⟨8851469962417820904979873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47207839799561711493225989 8851469962417820904979873)
            ·
              refine ⟨6638602471813365678734905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8851469962417820904979873 6638602471813365678734905)
              ·
                refine ⟨4978951853860024259051179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6638602471813365678734905 4978951853860024259051179)
                ·
                  refine ⟨7468427780790036388576769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978951853860024259051179 7468427780790036388576769)
                  ·
                    refine ⟨5601320835592527291432577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468427780790036388576769 5601320835592527291432577)
                    ·
                      refine ⟨4200990626694395468574433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601320835592527291432577 4200990626694395468574433)
                      ·
                        rfl

theorem cell23_8181400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_8181400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181400 prefixEnd_8181400 := by exact prefixLift 8181400
  have htrace : WordTrace (prefixWord ++ tailWord_8181400) baseStart_8181400 baseEnd_8181400 := by
    simpa [prefixWord, tailWord_8181400, baseEnd_8181400] using wordTrace_append hprefix tailTrace_8181400
  have hstable : (prefixWord ++ tailWord_8181400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181400).length < 2 ^ (prefixWord ++ tailWord_8181400).sum := by decide
  have hdescent : baseEnd_8181400 < baseStart_8181400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181409 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_8181409 : Nat := 118140960795 + 8181409 * 2 ^ 59
def prefixEnd_8181409 : Nat := 4983230072969 + 3 ^ 40 * 8181409 * 2
def baseEnd_8181409 : Nat := 4200995248020285933361891

theorem tailTrace_8181409 : CollatzResearch.WordTrace tailWord_8181409 prefixEnd_8181409 4200995248020285933361891 := by
  unfold tailWord_8181409
  simp only [CollatzResearch.WordTrace]
  refine ⟨298400500817159941259691281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198933667211439960839794187 298400500817159941259691281)
  ·
    refine ⟨223800375612869955944768461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298400500817159941259691281 223800375612869955944768461)
    ·
      refine ⟨83925140854826233479288173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223800375612869955944768461 83925140854826233479288173)
      ·
        refine ⟨31471927820559837554733065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83925140854826233479288173 31471927820559837554733065)
        ·
          refine ⟨23603945865419878166049799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31471927820559837554733065 23603945865419878166049799)
          ·
            refine ⟨35405918798129817249074699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23603945865419878166049799 35405918798129817249074699)
            ·
              refine ⟨53108878197194725873612049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35405918798129817249074699 53108878197194725873612049)
              ·
                refine ⟨39831658647896044405209037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53108878197194725873612049 39831658647896044405209037)
                ·
                  refine ⟨14936871992961016651953389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39831658647896044405209037 14936871992961016651953389)
                  ·
                    refine ⟨5601326997360381244482521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14936871992961016651953389 5601326997360381244482521)
                    ·
                      refine ⟨4200995248020285933361891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601326997360381244482521 4200995248020285933361891)
                      ·
                        rfl

theorem cell23_8181409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_8181409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181409 prefixEnd_8181409 := by exact prefixLift 8181409
  have htrace : WordTrace (prefixWord ++ tailWord_8181409) baseStart_8181409 baseEnd_8181409 := by
    simpa [prefixWord, tailWord_8181409, baseEnd_8181409] using wordTrace_append hprefix tailTrace_8181409
  have hstable : (prefixWord ++ tailWord_8181409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181409).length < 2 ^ (prefixWord ++ tailWord_8181409).sum := by decide
  have hdescent : baseEnd_8181409 < baseStart_8181409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181439 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 4, 2, 2]
def baseStart_8181439 : Nat := 118140960795 + 8181439 * 2 ^ 59
def prefixEnd_8181439 : Nat := 4983230072969 + 3 ^ 40 * 8181439 * 2
def baseEnd_8181439 : Nat := 4201010652439920815986753

theorem tailTrace_8181439 : CollatzResearch.WordTrace tailWord_8181439 prefixEnd_8181439 4201010652439920815986753 := by
  unfold tailWord_8181439
  simp only [CollatzResearch.WordTrace]
  refine ⟨298401595007051256383283371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198934396671367504255522247 298401595007051256383283371)
  ·
    refine ⟨447602392510576884574925057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298401595007051256383283371 447602392510576884574925057)
    ·
      refine ⟨335701794382932663431193793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447602392510576884574925057 335701794382932663431193793)
      ·
        refine ⟨251776345787199497573395345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335701794382932663431193793 251776345787199497573395345)
        ·
          refine ⟨188832259340399623180046509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251776345787199497573395345 188832259340399623180046509)
          ·
            refine ⟨70812097252649858692517441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188832259340399623180046509 70812097252649858692517441)
            ·
              refine ⟨53109072939487394019388081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70812097252649858692517441 53109072939487394019388081)
              ·
                refine ⟨39831804704615545514541061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53109072939487394019388081 39831804704615545514541061)
                ·
                  refine ⟨7468463382115414783976449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39831804704615545514541061 7468463382115414783976449)
                  ·
                    refine ⟨5601347536586561087982337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468463382115414783976449 5601347536586561087982337)
                    ·
                      refine ⟨4201010652439920815986753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601347536586561087982337 4201010652439920815986753)
                      ·
                        rfl

theorem cell23_8181439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_8181439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181439 prefixEnd_8181439 := by exact prefixLift 8181439
  have htrace : WordTrace (prefixWord ++ tailWord_8181439) baseStart_8181439 baseEnd_8181439 := by
    simpa [prefixWord, tailWord_8181439, baseEnd_8181439] using wordTrace_append hprefix tailTrace_8181439
  have hstable : (prefixWord ++ tailWord_8181439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181439).length < 2 ^ (prefixWord ++ tailWord_8181439).sum := by decide
  have hdescent : baseEnd_8181439 < baseStart_8181439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181472 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_8181472 : Nat := 118140960795 + 8181472 * 2 ^ 59
def prefixEnd_8181472 : Nat := 4983230072969 + 3 ^ 40 * 8181472 * 2
def baseEnd_8181472 : Nat := 4201027597301519186874101

theorem tailTrace_8181472 : CollatzResearch.WordTrace tailWord_8181472 prefixEnd_8181472 4201027597301519186874101 := by
  unfold tailWord_8181472
  simp only [CollatzResearch.WordTrace]
  refine ⟨149201399307965851509617335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198935199077287802012823113 149201399307965851509617335)
  ·
    refine ⟨223802098961948777264426003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149201399307965851509617335 223802098961948777264426003)
    ·
      refine ⟨335703148442923165896639005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223802098961948777264426003 335703148442923165896639005)
      ·
        refine ⟨125888680666096187211239627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335703148442923165896639005 125888680666096187211239627)
        ·
          refine ⟨188833020999144280816859441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125888680666096187211239627 188833020999144280816859441)
          ·
            refine ⟨141624765749358210612644581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188833020999144280816859441 141624765749358210612644581)
            ·
              refine ⟨26554643578004664489870859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141624765749358210612644581 26554643578004664489870859)
              ·
                refine ⟨39831965367006996734806289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26554643578004664489870859 39831965367006996734806289)
                ·
                  refine ⟨29873974025255247551104717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39831965367006996734806289 29873974025255247551104717)
                  ·
                    refine ⟨11202740259470717831664269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29873974025255247551104717 11202740259470717831664269)
                    ·
                      refine ⟨4201027597301519186874101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202740259470717831664269 4201027597301519186874101)
                      ·
                        rfl

theorem cell23_8181472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_8181472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181472 prefixEnd_8181472 := by exact prefixLift 8181472
  have htrace : WordTrace (prefixWord ++ tailWord_8181472) baseStart_8181472 baseEnd_8181472 := by
    simpa [prefixWord, tailWord_8181472, baseEnd_8181472] using wordTrace_append hprefix tailTrace_8181472
  have hstable : (prefixWord ++ tailWord_8181472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181472).length < 2 ^ (prefixWord ++ tailWord_8181472).sum := by decide
  have hdescent : baseEnd_8181472 < baseStart_8181472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181473 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_8181473 : Nat := 118140960795 + 8181473 * 2 ^ 59
def prefixEnd_8181473 : Nat := 4983230072969 + 3 ^ 40 * 8181473 * 2
def baseEnd_8181473 : Nat := 4201028110782173682961597

theorem tailTrace_8181473 : CollatzResearch.WordTrace tailWord_8181473 prefixEnd_8181473 4201028110782173682961597 := by
  unfold tailWord_8181473
  simp only [CollatzResearch.WordTrace]
  refine ⟨298402835088928080190021073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198935223392618720126680715 298402835088928080190021073)
  ·
    refine ⟨223802126316696060142515805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298402835088928080190021073 223802126316696060142515805)
    ·
      refine ⟨83925797368761022553443427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223802126316696060142515805 83925797368761022553443427)
      ·
        refine ⟨125888696053141533830165141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83925797368761022553443427 125888696053141533830165141)
        ·
          refine ⟨5901032627491009398288991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125888696053141533830165141 5901032627491009398288991)
          ·
            refine ⟨8851548941236514097433487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901032627491009398288991 8851548941236514097433487)
            ·
              refine ⟨13277323411854771146150231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851548941236514097433487 13277323411854771146150231)
              ·
                refine ⟨19915985117782156719225347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13277323411854771146150231 19915985117782156719225347)
                ·
                  refine ⟨29873977676673235078838021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19915985117782156719225347 29873977676673235078838021)
                  ·
                    refine ⟨5601370814376231577282129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29873977676673235078838021 5601370814376231577282129)
                    ·
                      refine ⟨4201028110782173682961597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601370814376231577282129 4201028110782173682961597)
                      ·
                        rfl

theorem cell23_8181473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_8181473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181473 prefixEnd_8181473 := by exact prefixLift 8181473
  have htrace : WordTrace (prefixWord ++ tailWord_8181473) baseStart_8181473 baseEnd_8181473 := by
    simpa [prefixWord, tailWord_8181473, baseEnd_8181473] using wordTrace_append hprefix tailTrace_8181473
  have hstable : (prefixWord ++ tailWord_8181473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181473).length < 2 ^ (prefixWord ++ tailWord_8181473).sum := by decide
  have hdescent : baseEnd_8181473 < baseStart_8181473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181545 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_8181545 : Nat := 118140960795 + 8181545 * 2 ^ 59
def prefixEnd_8181545 : Nat := 4983230072969 + 3 ^ 40 * 8181545 * 2
def baseEnd_8181545 : Nat := 4201065081389297401261265

theorem tailTrace_8181545 : CollatzResearch.WordTrace tailWord_8181545 prefixEnd_8181545 4201065081389297401261265 := by
  unfold tailWord_8181545
  simp only [CollatzResearch.WordTrace]
  refine ⟨298405461144667236486642089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198936974096444824324428059 298405461144667236486642089)
  ·
    refine ⟨223804095858500427364981567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298405461144667236486642089 223804095858500427364981567)
    ·
      refine ⟨335706143787750641047472351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223804095858500427364981567 335706143787750641047472351)
      ·
        refine ⟨503559215681625961571208527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335706143787750641047472351 503559215681625961571208527)
        ·
          refine ⟨755338823522438942356812791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503559215681625961571208527 755338823522438942356812791)
          ·
            refine ⟨1133008235283658413535219187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755338823522438942356812791 1133008235283658413535219187)
            ·
              refine ⟨1699512352925487620302828781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133008235283658413535219187 1699512352925487620302828781)
              ·
                refine ⟨637317132347057857613560793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699512352925487620302828781 637317132347057857613560793)
                ·
                  refine ⟨477987849260293393210170595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637317132347057857613560793 477987849260293393210170595)
                  ·
                    refine ⟨716981773890440089815255893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477987849260293393210170595 716981773890440089815255893)
                    ·
                      refine ⟨4201065081389297401261265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 716981773890440089815255893 4201065081389297401261265)
                      ·
                        rfl

theorem cell23_8181545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_8181545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181545 prefixEnd_8181545 := by exact prefixLift 8181545
  have htrace : WordTrace (prefixWord ++ tailWord_8181545) baseStart_8181545 baseEnd_8181545 := by
    simpa [prefixWord, tailWord_8181545, baseEnd_8181545] using wordTrace_append hprefix tailTrace_8181545
  have hstable : (prefixWord ++ tailWord_8181545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181545).length < 2 ^ (prefixWord ++ tailWord_8181545).sum := by decide
  have hdescent : baseEnd_8181545 < baseStart_8181545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181566 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_8181566 : Nat := 118140960795 + 8181566 * 2 ^ 59
def prefixEnd_8181566 : Nat := 4983230072969 + 3 ^ 40 * 8181566 * 2
def baseEnd_8181566 : Nat := 4201075864483041819098669

theorem tailTrace_8181566 : CollatzResearch.WordTrace tailWord_8181566 prefixEnd_8181566 4201075864483041819098669 := by
  unfold tailWord_8181566
  simp only [CollatzResearch.WordTrace]
  refine ⟨37300778384698894634144569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198937484718394104715437701 37300778384698894634144569)
  ·
    refine ⟨27975583788524170975608427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37300778384698894634144569 27975583788524170975608427)
    ·
      refine ⟨41963375682786256463412641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27975583788524170975608427 41963375682786256463412641)
      ·
        refine ⟨31472531762089692347559481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41963375682786256463412641 31472531762089692347559481)
        ·
          refine ⟨23604398821567269260669611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31472531762089692347559481 23604398821567269260669611)
          ·
            refine ⟨35406598232350903891004417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23604398821567269260669611 35406598232350903891004417)
            ·
              refine ⟨26554948674263177918253313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35406598232350903891004417 26554948674263177918253313)
              ·
                refine ⟨19916211505697383438689985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26554948674263177918253313 19916211505697383438689985)
                ·
                  refine ⟨14937158629273037579017489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19916211505697383438689985 14937158629273037579017489)
                  ·
                    refine ⟨11202868971954778184263117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14937158629273037579017489 11202868971954778184263117)
                    ·
                      refine ⟨4201075864483041819098669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202868971954778184263117 4201075864483041819098669)
                      ·
                        rfl

theorem cell23_8181566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_8181566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181566 prefixEnd_8181566 := by exact prefixLift 8181566
  have htrace : WordTrace (prefixWord ++ tailWord_8181566) baseStart_8181566 baseEnd_8181566 := by
    simpa [prefixWord, tailWord_8181566, baseEnd_8181566] using wordTrace_append hprefix tailTrace_8181566
  have hstable : (prefixWord ++ tailWord_8181566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181566).length < 2 ^ (prefixWord ++ tailWord_8181566).sum := by decide
  have hdescent : baseEnd_8181566 < baseStart_8181566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181613 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_8181613 : Nat := 118140960795 + 8181613 * 2 ^ 59
def prefixEnd_8181613 : Nat := 4983230072969 + 3 ^ 40 * 8181613 * 2
def baseEnd_8181613 : Nat := 4201099998073803135210953

theorem tailTrace_8181613 : CollatzResearch.WordTrace tailWord_8181613 prefixEnd_8181613 4201099998073803135210953 := by
  unfold tailWord_8181613
  simp only [CollatzResearch.WordTrace]
  refine ⟨298407941308420884100117493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198938627538947256066744995 298407941308420884100117493)
  ·
    refine ⟨27975744497664457884386015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298407941308420884100117493 27975744497664457884386015)
    ·
      refine ⟨41963616746496686826579023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27975744497664457884386015 41963616746496686826579023)
      ·
        refine ⟨62945425119745030239868535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41963616746496686826579023 62945425119745030239868535)
        ·
          refine ⟨94418137679617545359802803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62945425119745030239868535 94418137679617545359802803)
          ·
            refine ⟨141627206519426318039704205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94418137679617545359802803 141627206519426318039704205)
            ·
              refine ⟨53110202444784869264889077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141627206519426318039704205 53110202444784869264889077)
              ·
                refine ⟨4979081479198581493583351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53110202444784869264889077 4979081479198581493583351)
                ·
                  refine ⟨7468622218797872240375027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979081479198581493583351 7468622218797872240375027)
                  ·
                    refine ⟨11202933328196808360562541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468622218797872240375027 11202933328196808360562541)
                    ·
                      refine ⟨4201099998073803135210953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202933328196808360562541 4201099998073803135210953)
                      ·
                        rfl

theorem cell23_8181613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_8181613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181613 prefixEnd_8181613 := by exact prefixLift 8181613
  have htrace : WordTrace (prefixWord ++ tailWord_8181613) baseStart_8181613 baseEnd_8181613 := by
    simpa [prefixWord, tailWord_8181613, baseEnd_8181613] using wordTrace_append hprefix tailTrace_8181613
  have hstable : (prefixWord ++ tailWord_8181613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181613).length < 2 ^ (prefixWord ++ tailWord_8181613).sum := by decide
  have hdescent : baseEnd_8181613 < baseStart_8181613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181630 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8181630 : Nat := 118140960795 + 8181630 * 2 ^ 59
def prefixEnd_8181630 : Nat := 4983230072969 + 3 ^ 40 * 8181630 * 2
def baseEnd_8181630 : Nat := 4201108727244929568698375

theorem tailTrace_8181630 : CollatzResearch.WordTrace tailWord_8181630 prefixEnd_8181630 4201108727244929568698375 := by
  unfold tailWord_8181630
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301070168669912000435793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198939040899572864002324229 37301070168669912000435793)
  ·
    refine ⟨27975802626502434000326845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37301070168669912000435793 27975802626502434000326845)
    ·
      refine ⟨10490925984938412750122567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27975802626502434000326845 10490925984938412750122567)
      ·
        refine ⟨15736388977407619125183851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10490925984938412750122567 15736388977407619125183851)
        ·
          refine ⟨23604583466111428687775777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15736388977407619125183851 23604583466111428687775777)
          ·
            refine ⟨17703437599583571515831833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23604583466111428687775777 17703437599583571515831833)
            ·
              refine ⟨13277578199687678636873875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17703437599583571515831833 13277578199687678636873875)
              ·
                refine ⟨19916367299531517955310813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13277578199687678636873875 19916367299531517955310813)
                ·
                  refine ⟨7468637737324319233241555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19916367299531517955310813 7468637737324319233241555)
                  ·
                    refine ⟨11202956605986478849862333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468637737324319233241555 11202956605986478849862333)
                    ·
                      refine ⟨4201108727244929568698375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11202956605986478849862333 4201108727244929568698375)
                      ·
                        rfl

theorem cell23_8181630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8181630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181630 prefixEnd_8181630 := by exact prefixLift 8181630
  have htrace : WordTrace (prefixWord ++ tailWord_8181630) baseStart_8181630 baseEnd_8181630 := by
    simpa [prefixWord, tailWord_8181630, baseEnd_8181630] using wordTrace_append hprefix tailTrace_8181630
  have hstable : (prefixWord ++ tailWord_8181630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181630).length < 2 ^ (prefixWord ++ tailWord_8181630).sum := by decide
  have hdescent : baseEnd_8181630 < baseStart_8181630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181632 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_8181632 : Nat := 118140960795 + 8181632 * 2 ^ 59
def prefixEnd_8181632 : Nat := 4983230072969 + 3 ^ 40 * 8181632 * 2
def baseEnd_8181632 : Nat := 4201109754206238560873365

theorem tailTrace_8181632 : CollatzResearch.WordTrace tailWord_8181632 prefixEnd_8181632 4201109754206238560873365 := by
  unfold tailWord_8181632
  simp only [CollatzResearch.WordTrace]
  refine ⟨149204317147676025172529575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198939089530234700230039433 149204317147676025172529575)
  ·
    refine ⟨223806475721514037758794363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149204317147676025172529575 223806475721514037758794363)
    ·
      refine ⟨335709713582271056638191545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223806475721514037758794363 335709713582271056638191545)
      ·
        refine ⟨251782285186703292478643659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335709713582271056638191545 251782285186703292478643659)
        ·
          refine ⟨377673427780054938717965489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251782285186703292478643659 377673427780054938717965489)
          ·
            refine ⟨283255070835041204038474117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377673427780054938717965489 283255070835041204038474117)
            ·
              refine ⟨53110325781570225757213897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283255070835041204038474117 53110325781570225757213897)
              ·
                refine ⟨39832744336177669317910423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53110325781570225757213897 39832744336177669317910423)
                ·
                  refine ⟨59749116504266503976865635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39832744336177669317910423 59749116504266503976865635)
                  ·
                    refine ⟨89623674756399755965298453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59749116504266503976865635 89623674756399755965298453)
                    ·
                      refine ⟨4201109754206238560873365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89623674756399755965298453 4201109754206238560873365)
                      ·
                        rfl

theorem cell23_8181632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_8181632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181632 prefixEnd_8181632 := by exact prefixLift 8181632
  have htrace : WordTrace (prefixWord ++ tailWord_8181632) baseStart_8181632 baseEnd_8181632 := by
    simpa [prefixWord, tailWord_8181632, baseEnd_8181632] using wordTrace_append hprefix tailTrace_8181632
  have hstable : (prefixWord ++ tailWord_8181632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181632).length < 2 ^ (prefixWord ++ tailWord_8181632).sum := by decide
  have hdescent : baseEnd_8181632 < baseStart_8181632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181649 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_8181649 : Nat := 118140960795 + 8181649 * 2 ^ 59
def prefixEnd_8181649 : Nat := 4983230072969 + 3 ^ 40 * 8181649 * 2
def baseEnd_8181649 : Nat := 4201118483377364994360787

theorem tailTrace_8181649 : CollatzResearch.WordTrace tailWord_8181649 prefixEnd_8181649 4201118483377364994360787 := by
  unfold tailWord_8181649
  simp only [CollatzResearch.WordTrace]
  refine ⟨298409254336290462248428001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198939502890860308165618667 298409254336290462248428001)
  ·
    refine ⟨223806940752217846686321001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298409254336290462248428001 223806940752217846686321001)
    ·
      refine ⟨167855205564163385014740751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223806940752217846686321001 167855205564163385014740751)
      ·
        refine ⟨251782808346245077522111127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167855205564163385014740751 251782808346245077522111127)
        ·
          refine ⟨377674212519367616283166691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251782808346245077522111127 377674212519367616283166691)
          ·
            refine ⟨566511318779051424424750037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377674212519367616283166691 566511318779051424424750037)
            ·
              refine ⟨13277609033884017759955079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 566511318779051424424750037 13277609033884017759955079)
              ·
                refine ⟨19916413550826026639932619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13277609033884017759955079 19916413550826026639932619)
                ·
                  refine ⟨29874620326239039959898929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19916413550826026639932619 29874620326239039959898929)
                  ·
                    refine ⟨22405965244679279969924197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29874620326239039959898929 22405965244679279969924197)
                    ·
                      refine ⟨4201118483377364994360787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22405965244679279969924197 4201118483377364994360787)
                      ·
                        rfl

theorem cell23_8181649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_8181649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181649 prefixEnd_8181649 := by exact prefixLift 8181649
  have htrace : WordTrace (prefixWord ++ tailWord_8181649) baseStart_8181649 baseEnd_8181649 := by
    simpa [prefixWord, tailWord_8181649, baseEnd_8181649] using wordTrace_append hprefix tailTrace_8181649
  have hstable : (prefixWord ++ tailWord_8181649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181649).length < 2 ^ (prefixWord ++ tailWord_8181649).sum := by decide
  have hdescent : baseEnd_8181649 < baseStart_8181649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181669 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_8181669 : Nat := 118140960795 + 8181669 * 2 ^ 59
def prefixEnd_8181669 : Nat := 4983230072969 + 3 ^ 40 * 8181669 * 2
def baseEnd_8181669 : Nat := 4201128752990454916110695

theorem tailTrace_8181669 : CollatzResearch.WordTrace tailWord_8181669 prefixEnd_8181669 4201128752990454916110695 := by
  unfold tailWord_8181669
  simp only [CollatzResearch.WordTrace]
  refine ⟨298409983796218005664156061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198939989197478670442770707 298409983796218005664156061)
  ·
    refine ⟨111903743923581752124058523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298409983796218005664156061 111903743923581752124058523)
    ·
      refine ⟨167855615885372628186087785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111903743923581752124058523 167855615885372628186087785)
      ·
        refine ⟨125891711914029471139565839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167855615885372628186087785 125891711914029471139565839)
        ·
          refine ⟨188837567871044206709348759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125891711914029471139565839 188837567871044206709348759)
          ·
            refine ⟨283256351806566310064023139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188837567871044206709348759 283256351806566310064023139)
            ·
              refine ⟨424884527709849465096034709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283256351806566310064023139 424884527709849465096034709)
              ·
                refine ⟨19916462236399193676376627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 424884527709849465096034709 19916462236399193676376627)
                ·
                  refine ⟨29874693354598790514564941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19916462236399193676376627 29874693354598790514564941)
                  ·
                    refine ⟨11203010007974546442961853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29874693354598790514564941 11203010007974546442961853)
                    ·
                      refine ⟨4201128752990454916110695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203010007974546442961853 4201128752990454916110695)
                      ·
                        rfl

theorem cell23_8181669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_8181669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181669 prefixEnd_8181669 := by exact prefixLift 8181669
  have htrace : WordTrace (prefixWord ++ tailWord_8181669) baseStart_8181669 baseEnd_8181669 := by
    simpa [prefixWord, tailWord_8181669, baseEnd_8181669] using wordTrace_append hprefix tailTrace_8181669
  have hstable : (prefixWord ++ tailWord_8181669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181669).length < 2 ^ (prefixWord ++ tailWord_8181669).sum := by decide
  have hdescent : baseEnd_8181669 < baseStart_8181669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181696 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2]
def baseStart_8181696 : Nat := 118140960795 + 8181696 * 2 ^ 59
def prefixEnd_8181696 : Nat := 4983230072969 + 3 ^ 40 * 8181696 * 2
def baseEnd_8181696 : Nat := 4201142616968126310473071

theorem tailTrace_8181696 : CollatzResearch.WordTrace tailWord_8181696 prefixEnd_8181696 4201142616968126310473071 := by
  unfold tailWord_8181696
  simp only [CollatzResearch.WordTrace]
  refine ⟨149205484283560094637694471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198940645711413459516925961 149205484283560094637694471)
  ·
    refine ⟨223808226425340141956541707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149205484283560094637694471 223808226425340141956541707)
    ·
      refine ⟨335712339638010212934812561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223808226425340141956541707 335712339638010212934812561)
      ·
        refine ⟨251784254728507659701109421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335712339638010212934812561 251784254728507659701109421)
        ·
          refine ⟨94419095523190372387916033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251784254728507659701109421 94419095523190372387916033)
          ·
            refine ⟨70814321642392779290937025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94419095523190372387916033 70814321642392779290937025)
            ·
              refine ⟨53110741231794584468202769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70814321642392779290937025 53110741231794584468202769)
              ·
                refine ⟨39833055923845938351152077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53110741231794584468202769 39833055923845938351152077)
                ·
                  refine ⟨14937395971442226881682029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39833055923845938351152077 14937395971442226881682029)
                  ·
                    refine ⟨5601523489290835080630761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14937395971442226881682029 5601523489290835080630761)
                    ·
                      refine ⟨4201142616968126310473071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601523489290835080630761 4201142616968126310473071)
                      ·
                        rfl

theorem cell23_8181696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_8181696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181696 prefixEnd_8181696 := by exact prefixLift 8181696
  have htrace : WordTrace (prefixWord ++ tailWord_8181696) baseStart_8181696 baseEnd_8181696 := by
    simpa [prefixWord, tailWord_8181696, baseEnd_8181696] using wordTrace_append hprefix tailTrace_8181696
  have hstable : (prefixWord ++ tailWord_8181696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181696).length < 2 ^ (prefixWord ++ tailWord_8181696).sum := by decide
  have hdescent : baseEnd_8181696 < baseStart_8181696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181724 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_8181724 : Nat := 118140960795 + 8181724 * 2 ^ 59
def prefixEnd_8181724 : Nat := 4983230072969 + 3 ^ 40 * 8181724 * 2
def baseEnd_8181724 : Nat := 4201156994426452200922943

theorem tailTrace_8181724 : CollatzResearch.WordTrace tailWord_8181724 prefixEnd_8181724 4201156994426452200922943 := by
  unfold tailWord_8181724
  simp only [CollatzResearch.WordTrace]
  refine ⟨149205994905509375028704113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198941326540679166704938817 149205994905509375028704113)
  ·
    refine ⟨111904496179132031271528085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149205994905509375028704113 111904496179132031271528085)
    ·
      refine ⟨5245523258396813965852879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111904496179132031271528085 5245523258396813965852879)
      ·
        refine ⟨7868284887595220948779319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245523258396813965852879 7868284887595220948779319)
        ·
          refine ⟨11802427331392831423168979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868284887595220948779319 11802427331392831423168979)
          ·
            refine ⟨17703640997089247134753469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11802427331392831423168979 17703640997089247134753469)
            ·
              refine ⟨6638865373908467675532551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17703640997089247134753469 6638865373908467675532551)
              ·
                refine ⟨9958298060862701513298827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638865373908467675532551 9958298060862701513298827)
                ·
                  refine ⟨14937447091294052269948241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9958298060862701513298827 14937447091294052269948241)
                  ·
                    refine ⟨11203085318470539202461181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14937447091294052269948241 11203085318470539202461181)
                    ·
                      refine ⟨4201156994426452200922943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203085318470539202461181 4201156994426452200922943)
                      ·
                        rfl

theorem cell23_8181724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_8181724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181724 prefixEnd_8181724 := by exact prefixLift 8181724
  have htrace : WordTrace (prefixWord ++ tailWord_8181724) baseStart_8181724 baseEnd_8181724 := by
    simpa [prefixWord, tailWord_8181724, baseEnd_8181724] using wordTrace_append hprefix tailTrace_8181724
  have hstable : (prefixWord ++ tailWord_8181724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181724).length < 2 ^ (prefixWord ++ tailWord_8181724).sum := by decide
  have hdescent : baseEnd_8181724 < baseStart_8181724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181729 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_8181729 : Nat := 118140960795 + 8181729 * 2 ^ 59
def prefixEnd_8181729 : Nat := 4983230072969 + 3 ^ 40 * 8181729 * 2
def baseEnd_8181729 : Nat := 4201159561829724681360419

theorem tailTrace_8181729 : CollatzResearch.WordTrace tailWord_8181729 prefixEnd_8181729 4201159561829724681360419 := by
  unfold tailWord_8181729
  simp only [CollatzResearch.WordTrace]
  refine ⟨298412172176000635911340241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198941448117333757274226827 298412172176000635911340241)
  ·
    refine ⟨223809129132000476933505181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298412172176000635911340241 223809129132000476933505181)
    ·
      refine ⟨83928423424500178850064443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223809129132000476933505181 83928423424500178850064443)
      ·
        refine ⟨125892635136750268275096665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83928423424500178850064443 125892635136750268275096665)
        ·
          refine ⟨94419476352562701206322499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125892635136750268275096665 94419476352562701206322499)
          ·
            refine ⟨141629214528844051809483749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94419476352562701206322499 141629214528844051809483749)
            ·
              refine ⟨26555477724158259714278203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141629214528844051809483749 26555477724158259714278203)
              ·
                refine ⟨39833216586237389571417305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26555477724158259714278203 39833216586237389571417305)
                ·
                  refine ⟨29874912439678042178562979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39833216586237389571417305 29874912439678042178562979)
                  ·
                    refine ⟨44812368659517063267844469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29874912439678042178562979 44812368659517063267844469)
                    ·
                      refine ⟨4201159561829724681360419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44812368659517063267844469 4201159561829724681360419)
                      ·
                        rfl

theorem cell23_8181729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_8181729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181729 prefixEnd_8181729 := by exact prefixLift 8181729
  have htrace : WordTrace (prefixWord ++ tailWord_8181729) baseStart_8181729 baseEnd_8181729 := by
    simpa [prefixWord, tailWord_8181729, baseEnd_8181729] using wordTrace_append hprefix tailTrace_8181729
  have hstable : (prefixWord ++ tailWord_8181729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181729).length < 2 ^ (prefixWord ++ tailWord_8181729).sum := by decide
  have hdescent : baseEnd_8181729 < baseStart_8181729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181829 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_8181829 : Nat := 118140960795 + 8181829 * 2 ^ 59
def prefixEnd_8181829 : Nat := 4983230072969 + 3 ^ 40 * 8181829 * 2
def baseEnd_8181829 : Nat := 4201210909895174290109959

theorem tailTrace_8181829 : CollatzResearch.WordTrace tailWord_8181829 prefixEnd_8181829 4201210909895174290109959 := by
  unfold tailWord_8181829
  simp only [CollatzResearch.WordTrace]
  refine ⟨298415819475638352989980541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198943879650425568659987027 298415819475638352989980541)
  ·
    refine ⟨111905932303364382371242703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298415819475638352989980541 111905932303364382371242703)
    ·
      refine ⟨167858898455046573556864055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111905932303364382371242703 167858898455046573556864055)
      ·
        refine ⟨251788347682569860335296083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167858898455046573556864055 251788347682569860335296083)
        ·
          refine ⟨377682521523854790502944125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251788347682569860335296083 377682521523854790502944125)
          ·
            refine ⟨141630945571445546438604047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377682521523854790502944125 141630945571445546438604047)
            ·
              refine ⟨212446418357168319657906071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141630945571445546438604047 212446418357168319657906071)
              ·
                refine ⟨318669627535752479486859107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212446418357168319657906071 318669627535752479486859107)
                ·
                  refine ⟨478004441303628719230288661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318669627535752479486859107 478004441303628719230288661)
                  ·
                    refine ⟨22406458186107596213919781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 478004441303628719230288661 22406458186107596213919781)
                    ·
                      refine ⟨4201210909895174290109959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22406458186107596213919781 4201210909895174290109959)
                      ·
                        rfl

theorem cell23_8181829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_8181829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181829 prefixEnd_8181829 := by exact prefixLift 8181829
  have htrace : WordTrace (prefixWord ++ tailWord_8181829) baseStart_8181829 baseEnd_8181829 := by
    simpa [prefixWord, tailWord_8181829, baseEnd_8181829] using wordTrace_append hprefix tailTrace_8181829
  have hstable : (prefixWord ++ tailWord_8181829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181829).length < 2 ^ (prefixWord ++ tailWord_8181829).sum := by decide
  have hdescent : baseEnd_8181829 < baseStart_8181829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181836 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_8181836 : Nat := 118140960795 + 8181836 * 2 ^ 59
def prefixEnd_8181836 : Nat := 4983230072969 + 3 ^ 40 * 8181836 * 2
def baseEnd_8181836 : Nat := 4201214504259755762722427

theorem tailTrace_8181836 : CollatzResearch.WordTrace tailWord_8181836 prefixEnd_8181836 4201214504259755762722427 := by
  unfold tailWord_8181836
  simp only [CollatzResearch.WordTrace]
  refine ⟨149208037393306496592742681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198944049857741995456990241 149208037393306496592742681)
  ·
    refine ⟨111906028044979872444557011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149208037393306496592742681 111906028044979872444557011)
    ·
      refine ⟨167859042067469808666835517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111906028044979872444557011 167859042067469808666835517)
      ·
        refine ⟨62947140775301178250063319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167859042067469808666835517 62947140775301178250063319)
        ·
          refine ⟨94420711162951767375094979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62947140775301178250063319 94420711162951767375094979)
          ·
            refine ⟨141631066744427651062642469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94420711162951767375094979 141631066744427651062642469)
            ·
              refine ⟨26555825014580184574245463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141631066744427651062642469 26555825014580184574245463)
              ·
                refine ⟨39833737521870276861368195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26555825014580184574245463 39833737521870276861368195)
                ·
                  refine ⟨59750606282805415292052293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39833737521870276861368195 59750606282805415292052293)
                  ·
                    refine ⟨11203238678026015367259805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59750606282805415292052293 11203238678026015367259805)
                    ·
                      refine ⟨4201214504259755762722427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203238678026015367259805 4201214504259755762722427)
                      ·
                        rfl

theorem cell23_8181836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_8181836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181836 prefixEnd_8181836 := by exact prefixLift 8181836
  have htrace : WordTrace (prefixWord ++ tailWord_8181836) baseStart_8181836 baseEnd_8181836 := by
    simpa [prefixWord, tailWord_8181836, baseEnd_8181836] using wordTrace_append hprefix tailTrace_8181836
  have hstable : (prefixWord ++ tailWord_8181836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181836).length < 2 ^ (prefixWord ++ tailWord_8181836).sum := by decide
  have hdescent : baseEnd_8181836 < baseStart_8181836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181859 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_8181859 : Nat := 118140960795 + 8181859 * 2 ^ 59
def prefixEnd_8181859 : Nat := 4983230072969 + 3 ^ 40 * 8181859 * 2
def baseEnd_8181859 : Nat := 4201226314314809172734821

theorem tailTrace_8181859 : CollatzResearch.WordTrace tailWord_8181859 prefixEnd_8181859 4201226314314809172734821 := by
  unfold tailWord_8181859
  simp only [CollatzResearch.WordTrace]
  refine ⟨298416913665529668113572631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198944609110353112075715087 298416913665529668113572631)
  ·
    refine ⟨447625370498294502170358947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298416913665529668113572631 447625370498294502170358947)
    ·
      refine ⟨671438055747441753255538421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447625370498294502170358947 671438055747441753255538421)
      ·
        refine ⟨62947317726322664367706727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 671438055747441753255538421 62947317726322664367706727)
        ·
          refine ⟨94420976589483996551560091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62947317726322664367706727 94420976589483996551560091)
          ·
            refine ⟨141631464884225994827340137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94420976589483996551560091 141631464884225994827340137)
            ·
              refine ⟨106223598663169496120505103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141631464884225994827340137 106223598663169496120505103)
              ·
                refine ⟨159335397994754244180757655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106223598663169496120505103 159335397994754244180757655)
                ·
                  refine ⟨239003096992131366271136483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159335397994754244180757655 239003096992131366271136483)
                  ·
                    refine ⟨358504645488197049406704725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239003096992131366271136483 358504645488197049406704725)
                    ·
                      refine ⟨4201226314314809172734821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 358504645488197049406704725 4201226314314809172734821)
                      ·
                        rfl

theorem cell23_8181859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_8181859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181859 prefixEnd_8181859 := by exact prefixLift 8181859
  have htrace : WordTrace (prefixWord ++ tailWord_8181859) baseStart_8181859 baseEnd_8181859 := by
    simpa [prefixWord, tailWord_8181859, baseEnd_8181859] using wordTrace_append hprefix tailTrace_8181859
  have hstable : (prefixWord ++ tailWord_8181859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181859).length < 2 ^ (prefixWord ++ tailWord_8181859).sum := by decide
  have hdescent : baseEnd_8181859 < baseStart_8181859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181916 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_8181916 : Nat := 118140960795 + 8181916 * 2 ^ 59
def prefixEnd_8181916 : Nat := 4983230072969 + 3 ^ 40 * 8181916 * 2
def baseEnd_8181916 : Nat := 1400418527570705149907353

theorem tailTrace_8181916 : CollatzResearch.WordTrace tailWord_8181916 prefixEnd_8181916 1400418527570705149907353 := by
  unfold tailWord_8181916
  simp only [CollatzResearch.WordTrace]
  refine ⟨149209496313161583424198801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198945995084215444565598401 149209496313161583424198801)
  ·
    refine ⟨111907122234871187568149101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149209496313161583424198801 111907122234871187568149101)
    ·
      refine ⟨41965170838076695338055913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111907122234871187568149101 41965170838076695338055913)
      ·
        refine ⟨31473878128557521503541935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41965170838076695338055913 31473878128557521503541935)
        ·
          refine ⟨47210817192836282255312903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31473878128557521503541935 47210817192836282255312903)
          ·
            refine ⟨70816225789254423382969355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47210817192836282255312903 70816225789254423382969355)
            ·
              refine ⟨106224338683881635074454033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70816225789254423382969355 106224338683881635074454033)
              ·
                refine ⟨79668254012911226305840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106224338683881635074454033 79668254012911226305840525)
                ·
                  refine ⟨29875595254841709864690197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79668254012911226305840525 29875595254841709864690197)
                  ·
                    refine ⟨1400418527570705149907353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29875595254841709864690197 1400418527570705149907353)
                    ·
                      rfl

theorem cell23_8181916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_8181916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181916 prefixEnd_8181916 := by exact prefixLift 8181916
  have htrace : WordTrace (prefixWord ++ tailWord_8181916) baseStart_8181916 baseEnd_8181916 := by
    simpa [prefixWord, tailWord_8181916, baseEnd_8181916] using wordTrace_append hprefix tailTrace_8181916
  have hstable : (prefixWord ++ tailWord_8181916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181916).length < 2 ^ (prefixWord ++ tailWord_8181916).sum := by decide
  have hdescent : baseEnd_8181916 < baseStart_8181916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181917 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_8181917 : Nat := 118140960795 + 8181917 * 2 ^ 59
def prefixEnd_8181917 : Nat := 4983230072969 + 3 ^ 40 * 8181917 * 2
def baseEnd_8181917 : Nat := 4201256096192769945809555

theorem tailTrace_8181917 : CollatzResearch.WordTrace tailWord_8181917 prefixEnd_8181917 4201256096192769945809555 := by
  unfold tailWord_8181917
  simp only [CollatzResearch.WordTrace]
  refine ⟨298419029099319544019184005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198946019399546362679456003 298419029099319544019184005)
  ·
    refine ⟨55953567956122414503597001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298419029099319544019184005 55953567956122414503597001)
    ·
      refine ⟨41965175967091810877697751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55953567956122414503597001 41965175967091810877697751)
      ·
        refine ⟨62947763950637716316546627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41965175967091810877697751 62947763950637716316546627)
        ·
          refine ⟨94421645925956574474819941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62947763950637716316546627 94421645925956574474819941)
          ·
            refine ⟨17704058611116857714028739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94421645925956574474819941 17704058611116857714028739)
            ·
              refine ⟨26556087916675286571043109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17704058611116857714028739 26556087916675286571043109)
              ·
                refine ⟨4979266484376616232070583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26556087916675286571043109 4979266484376616232070583)
                ·
                  refine ⟨7468899726564924348105875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979266484376616232070583 7468899726564924348105875)
                  ·
                    refine ⟨11203349589847386522158813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468899726564924348105875 11203349589847386522158813)
                    ·
                      refine ⟨4201256096192769945809555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203349589847386522158813 4201256096192769945809555)
                      ·
                        rfl

theorem cell23_8181917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_8181917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181917 prefixEnd_8181917 := by exact prefixLift 8181917
  have htrace : WordTrace (prefixWord ++ tailWord_8181917) baseStart_8181917 baseEnd_8181917 := by
    simpa [prefixWord, tailWord_8181917, baseEnd_8181917] using wordTrace_append hprefix tailTrace_8181917
  have hstable : (prefixWord ++ tailWord_8181917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181917).length < 2 ^ (prefixWord ++ tailWord_8181917).sum := by decide
  have hdescent : baseEnd_8181917 < baseStart_8181917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181933 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_8181933 : Nat := 118140960795 + 8181933 * 2 ^ 59
def prefixEnd_8181933 : Nat := 4983230072969 + 3 ^ 40 * 8181933 * 2
def baseEnd_8181933 : Nat := 1400421437294413961069827

theorem tailTrace_8181933 : CollatzResearch.WordTrace tailWord_8181933 prefixEnd_8181933 1400421437294413961069827 := by
  unfold tailWord_8181933
  simp only [CollatzResearch.WordTrace]
  refine ⟨298419612667261578751766453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198946408444841052501177635 298419612667261578751766453)
  ·
    refine ⟨27976838687555773007978105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298419612667261578751766453 27976838687555773007978105)
    ·
      refine ⟨20982629015666829755983579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27976838687555773007978105 20982629015666829755983579)
      ·
        refine ⟨31473943523500244633975369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20982629015666829755983579 31473943523500244633975369)
        ·
          refine ⟨23605457642625183475481527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31473943523500244633975369 23605457642625183475481527)
          ·
            refine ⟨35408186463937775213222291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605457642625183475481527 35408186463937775213222291)
            ·
              refine ⟨53112279695906662819833437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35408186463937775213222291 53112279695906662819833437)
              ·
                refine ⟨19917104885964998557437539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53112279695906662819833437 19917104885964998557437539)
                ·
                  refine ⟨29875657328947497836156309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19917104885964998557437539 29875657328947497836156309)
                  ·
                    refine ⟨1400421437294413961069827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29875657328947497836156309 1400421437294413961069827)
                    ·
                      rfl

theorem cell23_8181933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_8181933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181933 prefixEnd_8181933 := by exact prefixLift 8181933
  have htrace : WordTrace (prefixWord ++ tailWord_8181933) baseStart_8181933 baseEnd_8181933 := by
    simpa [prefixWord, tailWord_8181933, baseEnd_8181933] using wordTrace_append hprefix tailTrace_8181933
  have hstable : (prefixWord ++ tailWord_8181933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181933).length < 2 ^ (prefixWord ++ tailWord_8181933).sum := by decide
  have hdescent : baseEnd_8181933 < baseStart_8181933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181934 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_8181934 : Nat := 118140960795 + 8181934 * 2 ^ 59
def prefixEnd_8181934 : Nat := 4983230072969 + 3 ^ 40 * 8181934 * 2
def baseEnd_8181934 : Nat := 4201264825363896379296977

theorem tailTrace_8181934 : CollatzResearch.WordTrace tailWord_8181934 prefixEnd_8181934 4201264825363896379296977 := by
  unfold tailWord_8181934
  simp only [CollatzResearch.WordTrace]
  refine ⟨37302456142532244490319107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198946432760171970615035237 37302456142532244490319107)
  ·
    refine ⟨55953684213798366735478661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37302456142532244490319107 55953684213798366735478661)
    ·
      refine ⟨10491315790087193762902249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55953684213798366735478661 10491315790087193762902249)
      ·
        refine ⟨7868486842565395322176687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10491315790087193762902249 7868486842565395322176687)
        ·
          refine ⟨11802730263848092983265031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868486842565395322176687 11802730263848092983265031)
          ·
            refine ⟨17704095395772139474897547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11802730263848092983265031 17704095395772139474897547)
            ·
              refine ⟨26556143093658209212346321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17704095395772139474897547 26556143093658209212346321)
              ·
                refine ⟨19917107320243656909259741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26556143093658209212346321 19917107320243656909259741)
                ·
                  refine ⟨7468915245091371340972403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19917107320243656909259741 7468915245091371340972403)
                  ·
                    refine ⟨11203372867637057011458605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468915245091371340972403 11203372867637057011458605)
                    ·
                      refine ⟨4201264825363896379296977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203372867637057011458605 4201264825363896379296977)
                      ·
                        rfl

theorem cell23_8181934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_8181934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181934 prefixEnd_8181934 := by exact prefixLift 8181934
  have htrace : WordTrace (prefixWord ++ tailWord_8181934) baseStart_8181934 baseEnd_8181934 := by
    simpa [prefixWord, tailWord_8181934, baseEnd_8181934] using wordTrace_append hprefix tailTrace_8181934
  have hstable : (prefixWord ++ tailWord_8181934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181934).length < 2 ^ (prefixWord ++ tailWord_8181934).sum := by decide
  have hdescent : baseEnd_8181934 < baseStart_8181934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181943 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_8181943 : Nat := 118140960795 + 8181943 * 2 ^ 59
def prefixEnd_8181943 : Nat := 4983230072969 + 3 ^ 40 * 8181943 * 2
def baseEnd_8181943 : Nat := 4201269446689786844084435

theorem tailTrace_8181943 : CollatzResearch.WordTrace tailWord_8181943 prefixEnd_8181943 4201269446689786844084435 := by
  unfold tailWord_8181943
  simp only [CollatzResearch.WordTrace]
  refine ⟨298419977397225350459630483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198946651598150233639753655 298419977397225350459630483)
  ·
    refine ⟨447629966095838025689445725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298419977397225350459630483 447629966095838025689445725)
    ·
      refine ⟨167861237285939259633542147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447629966095838025689445725 167861237285939259633542147)
      ·
        refine ⟨251791855928908889450313221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167861237285939259633542147 251791855928908889450313221)
        ·
          refine ⟨47210972986670416771933729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251791855928908889450313221 47210972986670416771933729)
          ·
            refine ⟨35408229740002812578950297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47210972986670416771933729 35408229740002812578950297)
            ·
              refine ⟨26556172305002109434212723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35408229740002812578950297 26556172305002109434212723)
              ·
                refine ⟨39834258457503164151319085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26556172305002109434212723 39834258457503164151319085)
                ·
                  refine ⟨14937846921563686556744657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39834258457503164151319085 14937846921563686556744657)
                  ·
                    refine ⟨11203385191172764917558493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14937846921563686556744657 11203385191172764917558493)
                    ·
                      refine ⟨4201269446689786844084435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203385191172764917558493 4201269446689786844084435)
                      ·
                        rfl

theorem cell23_8181943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_8181943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181943 prefixEnd_8181943 := by exact prefixLift 8181943
  have htrace : WordTrace (prefixWord ++ tailWord_8181943) baseStart_8181943 baseEnd_8181943 := by
    simpa [prefixWord, tailWord_8181943, baseEnd_8181943] using wordTrace_append hprefix tailTrace_8181943
  have hstable : (prefixWord ++ tailWord_8181943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181943).length < 2 ^ (prefixWord ++ tailWord_8181943).sum := by decide
  have hdescent : baseEnd_8181943 < baseStart_8181943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181954 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_8181954 : Nat := 118140960795 + 8181954 * 2 ^ 59
def prefixEnd_8181954 : Nat := 4983230072969 + 3 ^ 40 * 8181954 * 2
def baseEnd_8181954 : Nat := 1400425031658995433682295

theorem tailTrace_8181954 : CollatzResearch.WordTrace tailWord_8181954 prefixEnd_8181954 1400425031658995433682295 := by
  unfold tailWord_8181954
  simp only [CollatzResearch.WordTrace]
  refine ⟨74605094650046374834570229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198946919066790332892187277 74605094650046374834570229)
  ·
    refine ⟨6994227623441847640740959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74605094650046374834570229 6994227623441847640740959)
    ·
      refine ⟨10491341435162771461111439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994227623441847640740959 10491341435162771461111439)
      ·
        refine ⟨15737012152744157191667159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10491341435162771461111439 15737012152744157191667159)
        ·
          refine ⟨23605518229116235787500739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737012152744157191667159 23605518229116235787500739)
          ·
            refine ⟨35408277343674353681251109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605518229116235787500739 35408277343674353681251109)
            ·
              refine ⟨6639052001938941315234583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35408277343674353681251109 6639052001938941315234583)
              ·
                refine ⟨9958578002908411972851875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639052001938941315234583 9958578002908411972851875)
                ·
                  refine ⟨14937867004362617959277813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9958578002908411972851875 14937867004362617959277813)
                  ·
                    refine ⟨1400425031658995433682295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14937867004362617959277813 1400425031658995433682295)
                    ·
                      rfl

theorem cell23_8181954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_8181954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181954 prefixEnd_8181954 := by exact prefixLift 8181954
  have htrace : WordTrace (prefixWord ++ tailWord_8181954) baseStart_8181954 baseEnd_8181954 := by
    simpa [prefixWord, tailWord_8181954, baseEnd_8181954] using wordTrace_append hprefix tailTrace_8181954
  have hstable : (prefixWord ++ tailWord_8181954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181954).length < 2 ^ (prefixWord ++ tailWord_8181954).sum := by decide
  have hdescent : baseEnd_8181954 < baseStart_8181954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181957 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 1, 2, 2]
def baseStart_8181957 : Nat := 118140960795 + 8181957 * 2 ^ 59
def prefixEnd_8181957 : Nat := 4983230072969 + 3 ^ 40 * 8181957 * 2
def baseEnd_8181957 : Nat := 4201276635418949789309371

theorem tailTrace_8181957 : CollatzResearch.WordTrace tailWord_8181957 prefixEnd_8181957 4201276635418949789309371 := by
  unfold tailWord_8181957
  simp only [CollatzResearch.WordTrace]
  refine ⟨298420488019174630850640125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198946992012783087233760083 298420488019174630850640125)
  ·
    refine ⟨111907683007190486568990047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298420488019174630850640125 111907683007190486568990047)
    ·
      refine ⟨167861524510785729853485071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111907683007190486568990047 167861524510785729853485071)
      ·
        refine ⟨251792286766178594780227607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167861524510785729853485071 251792286766178594780227607)
        ·
          refine ⟨377688430149267892170341411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251792286766178594780227607 377688430149267892170341411)
          ·
            refine ⟨566532645223901838255512117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377688430149267892170341411 566532645223901838255512117)
            ·
              refine ⟨53112435489740797336454261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 566532645223901838255512117 53112435489740797336454261)
              ·
                refine ⟨4979290827163199750292587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53112435489740797336454261 4979290827163199750292587)
                ·
                  refine ⟨7468936240744799625438881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979290827163199750292587 7468936240744799625438881)
                  ·
                    refine ⟨5601702180558599719079161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468936240744799625438881 5601702180558599719079161)
                    ·
                      refine ⟨4201276635418949789309371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601702180558599719079161 4201276635418949789309371)
                      ·
                        rfl

theorem cell23_8181957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_8181957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181957 prefixEnd_8181957 := by exact prefixLift 8181957
  have htrace : WordTrace (prefixWord ++ tailWord_8181957) baseStart_8181957 baseEnd_8181957 := by
    simpa [prefixWord, tailWord_8181957, baseEnd_8181957] using wordTrace_append hprefix tailTrace_8181957
  have hstable : (prefixWord ++ tailWord_8181957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181957).length < 2 ^ (prefixWord ++ tailWord_8181957).sum := by decide
  have hdescent : baseEnd_8181957 < baseStart_8181957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181974 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_8181974 : Nat := 118140960795 + 8181974 * 2 ^ 59
def prefixEnd_8181974 : Nat := 4983230072969 + 3 ^ 40 * 8181974 * 2
def baseEnd_8181974 : Nat := 4201285364590076222796793

theorem tailTrace_8181974 : CollatzResearch.WordTrace tailWord_8181974 prefixEnd_8181974 4201285364590076222796793 := by
  unfold tailWord_8181974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18651319253757065172125561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198947405373408695169339317 18651319253757065172125561)
  ·
    refine ⟨13988489440317798879094171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18651319253757065172125561 13988489440317798879094171)
    ·
      refine ⟨20982734160476698318641257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13988489440317798879094171 20982734160476698318641257)
      ·
        refine ⟨15737050620357523738980943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20982734160476698318641257 15737050620357523738980943)
        ·
          refine ⟨23605575930536285608471415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737050620357523738980943 23605575930536285608471415)
          ·
            refine ⟨35408363895804428412707123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605575930536285608471415 35408363895804428412707123)
            ·
              refine ⟨53112545843706642619060685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35408363895804428412707123 53112545843706642619060685)
              ·
                refine ⟨19917204691389990982147757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53112545843706642619060685 19917204691389990982147757)
                ·
                  refine ⟨7468951759271246618305409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19917204691389990982147757 7468951759271246618305409)
                  ·
                    refine ⟨5601713819453434963729057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468951759271246618305409 5601713819453434963729057)
                    ·
                      refine ⟨4201285364590076222796793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601713819453434963729057 4201285364590076222796793)
                      ·
                        rfl

theorem cell23_8181974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_8181974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181974 prefixEnd_8181974 := by exact prefixLift 8181974
  have htrace : WordTrace (prefixWord ++ tailWord_8181974) baseStart_8181974 baseEnd_8181974 := by
    simpa [prefixWord, tailWord_8181974, baseEnd_8181974] using wordTrace_append hprefix tailTrace_8181974
  have hstable : (prefixWord ++ tailWord_8181974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181974).length < 2 ^ (prefixWord ++ tailWord_8181974).sum := by decide
  have hdescent : baseEnd_8181974 < baseStart_8181974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181987 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8181987 : Nat := 118140960795 + 8181987 * 2 ^ 59
def prefixEnd_8181987 : Nat := 4983230072969 + 3 ^ 40 * 8181987 * 2
def baseEnd_8181987 : Nat := 4201292039838584671934233

theorem tailTrace_8181987 : CollatzResearch.WordTrace tailWord_8181987 prefixEnd_8181987 4201292039838584671934233 := by
  unfold tailWord_8181987
  simp only [CollatzResearch.WordTrace]
  refine ⟨298421582209065945974232215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198947721472710630649488143 298421582209065945974232215)
  ·
    refine ⟨447632373313598918961348323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298421582209065945974232215 447632373313598918961348323)
    ·
      refine ⟨671448559970398378442022485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447632373313598918961348323 671448559970398378442022485)
      ·
        refine ⟨7868537812153105997367451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 671448559970398378442022485 7868537812153105997367451)
        ·
          refine ⟨11802806718229658996051177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868537812153105997367451 11802806718229658996051177)
          ·
            refine ⟨8852105038672244247038383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11802806718229658996051177 8852105038672244247038383)
            ·
              refine ⟨13278157558008366370557575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8852105038672244247038383 13278157558008366370557575)
              ·
                refine ⟨19917236337012549555836363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13278157558008366370557575 19917236337012549555836363)
                ·
                  refine ⟨29875854505518824333754545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19917236337012549555836363 29875854505518824333754545)
                  ·
                    refine ⟨22406890879139118250315909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29875854505518824333754545 22406890879139118250315909)
                    ·
                      refine ⟨4201292039838584671934233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22406890879139118250315909 4201292039838584671934233)
                      ·
                        rfl

theorem cell23_8181987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8181987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181987 prefixEnd_8181987 := by exact prefixLift 8181987
  have htrace : WordTrace (prefixWord ++ tailWord_8181987) baseStart_8181987 baseEnd_8181987 := by
    simpa [prefixWord, tailWord_8181987, baseEnd_8181987] using wordTrace_append hprefix tailTrace_8181987
  have hstable : (prefixWord ++ tailWord_8181987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181987).length < 2 ^ (prefixWord ++ tailWord_8181987).sum := by decide
  have hdescent : baseEnd_8181987 < baseStart_8181987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181997 : List Nat := [1, 5, 1, 2, 4, 1, 2, 7]
def baseStart_8181997 : Nat := 118140960795 + 8181997 * 2 ^ 59
def prefixEnd_8181997 : Nat := 4983230072969 + 3 ^ 40 * 8181997 * 2
def baseEnd_8181997 : Nat := 155603599060930727141081

theorem tailTrace_8181997 : CollatzResearch.WordTrace tailWord_8181997 prefixEnd_8181997 155603599060930727141081 := by
  unfold tailWord_8181997
  simp only [CollatzResearch.WordTrace]
  refine ⟨298421946939029717682096245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198947964626019811788064163 298421946939029717682096245)
  ·
    refine ⟨27977057525534036032696523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298421946939029717682096245 27977057525534036032696523)
    ·
      refine ⟨41965586288301054049044785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27977057525534036032696523 41965586288301054049044785)
      ·
        refine ⟨31474189716225790536783589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41965586288301054049044785 31474189716225790536783589)
        ·
          refine ⟨5901410571792335725646923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31474189716225790536783589 5901410571792335725646923)
          ·
            refine ⟨8852115857688503588470385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901410571792335725646923 8852115857688503588470385)
            ·
              refine ⟨6639086893266377691352789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8852115857688503588470385 6639086893266377691352789)
              ·
                refine ⟨155603599060930727141081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6639086893266377691352789 155603599060930727141081)
                ·
                  rfl

theorem cell23_8181997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 7].length) (baseStart_8181997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8181997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8181997 prefixEnd_8181997 := by exact prefixLift 8181997
  have htrace : WordTrace (prefixWord ++ tailWord_8181997) baseStart_8181997 baseEnd_8181997 := by
    simpa [prefixWord, tailWord_8181997, baseEnd_8181997] using wordTrace_append hprefix tailTrace_8181997
  have hstable : (prefixWord ++ tailWord_8181997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181997).length < 2 ^ (prefixWord ++ tailWord_8181997).sum := by decide
  have hdescent : baseEnd_8181997 < baseStart_8181997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182016 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_8182016 : Nat := 118140960795 + 8182016 * 2 ^ 59
def prefixEnd_8182016 : Nat := 4983230072969 + 3 ^ 40 * 8182016 * 2
def baseEnd_8182016 : Nat := 4201306930777565058471599

theorem tailTrace_8182016 : CollatzResearch.WordTrace tailWord_8182016 prefixEnd_8182016 4201306930777565058471599 := by
  unfold tailWord_8182016
  simp only [CollatzResearch.WordTrace]
  refine ⟨149211319962980441963518951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198948426617307255951358601 149211319962980441963518951)
  ·
    refine ⟨223816979944470662945278427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149211319962980441963518951 223816979944470662945278427)
    ·
      refine ⟨335725469916705994417917641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223816979944470662945278427 335725469916705994417917641)
      ·
        refine ⟨251794102437529495813438231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335725469916705994417917641 251794102437529495813438231)
        ·
          refine ⟨377691153656294243720157347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251794102437529495813438231 377691153656294243720157347)
          ·
            refine ⟨566536730484441365580236021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377691153656294243720157347 566536730484441365580236021)
            ·
              refine ⟨53112818482916378023147127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 566536730484441365580236021 53112818482916378023147127)
              ·
                refine ⟨79669227724374567034720691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53112818482916378023147127 79669227724374567034720691)
                ·
                  refine ⟨119503841586561850552081037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79669227724374567034720691 119503841586561850552081037)
                  ·
                    refine ⟨44813940594960693957030389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119503841586561850552081037 44813940594960693957030389)
                    ·
                      refine ⟨4201306930777565058471599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44813940594960693957030389 4201306930777565058471599)
                      ·
                        rfl

theorem cell23_8182016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_8182016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182016 prefixEnd_8182016 := by exact prefixLift 8182016
  have htrace : WordTrace (prefixWord ++ tailWord_8182016) baseStart_8182016 baseEnd_8182016 := by
    simpa [prefixWord, tailWord_8182016, baseEnd_8182016] using wordTrace_append hprefix tailTrace_8182016
  have hstable : (prefixWord ++ tailWord_8182016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182016).length < 2 ^ (prefixWord ++ tailWord_8182016).sum := by decide
  have hdescent : baseEnd_8182016 < baseStart_8182016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182081 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8182081 : Nat := 118140960795 + 8182081 * 2 ^ 59
def prefixEnd_8182081 : Nat := 4983230072969 + 3 ^ 40 * 8182081 * 2
def baseEnd_8182081 : Nat := 4201340307020107304158801

theorem tailTrace_8182081 : CollatzResearch.WordTrace tailWord_8182081 prefixEnd_8182081 4201340307020107304158801 := by
  unfold tailWord_8182081
  simp only [CollatzResearch.WordTrace]
  refine ⟨298425010670725400028154097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198950007113816933352102731 298425010670725400028154097)
  ·
    refine ⟨223818758003044050021115573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298425010670725400028154097 223818758003044050021115573)
    ·
      refine ⟨20983008562785379689479585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223818758003044050021115573 20983008562785379689479585)
      ·
        refine ⟨15737256422089034767109689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20983008562785379689479585 15737256422089034767109689)
        ·
          refine ⟨11802942316566776075332267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15737256422089034767109689 11802942316566776075332267)
          ·
            refine ⟨17704413474850164112998401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11802942316566776075332267 17704413474850164112998401)
            ·
              refine ⟨13278310106137623084748801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17704413474850164112998401 13278310106137623084748801)
              ·
                refine ⟨9958732579603217313561601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13278310106137623084748801 9958732579603217313561601)
                ·
                  refine ⟨7469049434702412985171201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9958732579603217313561601 7469049434702412985171201)
                  ·
                    refine ⟨5601787076026809738878401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7469049434702412985171201 5601787076026809738878401)
                    ·
                      refine ⟨4201340307020107304158801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601787076026809738878401 4201340307020107304158801)
                      ·
                        rfl

theorem cell23_8182081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8182081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182081 prefixEnd_8182081 := by exact prefixLift 8182081
  have htrace : WordTrace (prefixWord ++ tailWord_8182081) baseStart_8182081 baseEnd_8182081 := by
    simpa [prefixWord, tailWord_8182081, baseEnd_8182081] using wordTrace_append hprefix tailTrace_8182081
  have hstable : (prefixWord ++ tailWord_8182081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182081).length < 2 ^ (prefixWord ++ tailWord_8182081).sum := by decide
  have hdescent : baseEnd_8182081 < baseStart_8182081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182083 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 2, 5]
def baseStart_8182083 : Nat := 118140960795 + 8182083 * 2 ^ 59
def prefixEnd_8182083 : Nat := 4983230072969 + 3 ^ 40 * 8182083 * 2
def baseEnd_8182083 : Nat := 1400447111327138765444597

theorem tailTrace_8182083 : CollatzResearch.WordTrace tailWord_8182083 prefixEnd_8182083 1400447111327138765444597 := by
  unfold tailWord_8182083
  simp only [CollatzResearch.WordTrace]
  refine ⟨298425083616718154369726903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198950055744478769579817935 298425083616718154369726903)
  ·
    refine ⟨447637625425077231554590355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298425083616718154369726903 447637625425077231554590355)
    ·
      refine ⟨671456438137615847331885533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447637625425077231554590355 671456438137615847331885533)
      ·
        refine ⟨251796164301605942749457075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671456438137615847331885533 251796164301605942749457075)
        ·
          refine ⟨377694246452408914124185613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251796164301605942749457075 377694246452408914124185613)
          ·
            refine ⟨141635342419653342796569605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377694246452408914124185613 141635342419653342796569605)
            ·
              refine ⟨26556626703685001774356801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141635342419653342796569605 26556626703685001774356801)
              ·
                refine ⟨19917470027763751330767601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26556626703685001774356801 19917470027763751330767601)
                ·
                  refine ⟨14938102520822813498075701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19917470027763751330767601 14938102520822813498075701)
                  ·
                    refine ⟨1400447111327138765444597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14938102520822813498075701 1400447111327138765444597)
                    ·
                      rfl

theorem cell23_8182083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 5].length) (baseStart_8182083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182083 prefixEnd_8182083 := by exact prefixLift 8182083
  have htrace : WordTrace (prefixWord ++ tailWord_8182083) baseStart_8182083 baseEnd_8182083 := by
    simpa [prefixWord, tailWord_8182083, baseEnd_8182083] using wordTrace_append hprefix tailTrace_8182083
  have hstable : (prefixWord ++ tailWord_8182083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182083).length < 2 ^ (prefixWord ++ tailWord_8182083).sum := by decide
  have hdescent : baseEnd_8182083 < baseStart_8182083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182103 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_8182103 : Nat := 118140960795 + 8182103 * 2 ^ 59
def prefixEnd_8182103 : Nat := 4983230072969 + 3 ^ 40 * 8182103 * 2
def baseEnd_8182103 : Nat := 4201351603594506218083699

theorem tailTrace_8182103 : CollatzResearch.WordTrace tailWord_8182103 prefixEnd_8182103 4201351603594506218083699 := by
  unfold tailWord_8182103
  simp only [CollatzResearch.WordTrace]
  refine ⟨298425813076645697785454963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198950542051097131856969975 298425813076645697785454963)
  ·
    refine ⟨447638719614968546678182445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298425813076645697785454963 447638719614968546678182445)
    ·
      refine ⟨167864519855613205004318417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447638719614968546678182445 167864519855613205004318417)
      ·
        refine ⟨125898389891709903753238813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167864519855613205004318417 125898389891709903753238813)
        ·
          refine ⟨47211896209391213907464555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125898389891709903753238813 47211896209391213907464555)
          ·
            refine ⟨70817844314086820861196833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47211896209391213907464555 70817844314086820861196833)
            ·
              refine ⟨53113383235565115645897625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70817844314086820861196833 53113383235565115645897625)
              ·
                refine ⟨39835037426673836734423219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53113383235565115645897625 39835037426673836734423219)
                ·
                  refine ⟨59752556140010755101634829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39835037426673836734423219 59752556140010755101634829)
                  ·
                    refine ⟨22407208552504033163113061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59752556140010755101634829 22407208552504033163113061)
                    ·
                      refine ⟨4201351603594506218083699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22407208552504033163113061 4201351603594506218083699)
                      ·
                        rfl

theorem cell23_8182103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_8182103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182103 prefixEnd_8182103 := by exact prefixLift 8182103
  have htrace : WordTrace (prefixWord ++ tailWord_8182103) baseStart_8182103 baseEnd_8182103 := by
    simpa [prefixWord, tailWord_8182103, baseEnd_8182103] using wordTrace_append hprefix tailTrace_8182103
  have hstable : (prefixWord ++ tailWord_8182103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182103).length < 2 ^ (prefixWord ++ tailWord_8182103).sum := by decide
  have hdescent : baseEnd_8182103 < baseStart_8182103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182120 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_8182120 : Nat := 118140960795 + 8182120 * 2 ^ 59
def prefixEnd_8182120 : Nat := 4983230072969 + 3 ^ 40 * 8182120 * 2
def baseEnd_8182120 : Nat := 4201360332765632651571121

theorem tailTrace_8182120 : CollatzResearch.WordTrace tailWord_8182120 prefixEnd_8182120 4201360332765632651571121 := by
  unfold tailWord_8182120
  simp only [CollatzResearch.WordTrace]
  refine ⟨149213216558792054844411907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198950955411722739792549209 149213216558792054844411907)
  ·
    refine ⟨223819824838188082266617861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149213216558792054844411907 223819824838188082266617861)
    ·
      refine ⟨41966217157160265424990849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223819824838188082266617861 41966217157160265424990849)
      ·
        refine ⟨31474662867870199068743137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41966217157160265424990849 31474662867870199068743137)
        ·
          refine ⟨23605997150902649301557353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31474662867870199068743137 23605997150902649301557353)
          ·
            refine ⟨17704497863176986976168015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23605997150902649301557353 17704497863176986976168015)
            ·
              refine ⟨26556746794765480464252023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17704497863176986976168015 26556746794765480464252023)
              ·
                refine ⟨39835120192148220696378035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26556746794765480464252023 39835120192148220696378035)
                ·
                  refine ⟨59752680288222331044567053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39835120192148220696378035 59752680288222331044567053)
                  ·
                    refine ⟨22407255108083374141712645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59752680288222331044567053 22407255108083374141712645)
                    ·
                      refine ⟨4201360332765632651571121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22407255108083374141712645 4201360332765632651571121)
                      ·
                        rfl

theorem cell23_8182120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_8182120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182120 prefixEnd_8182120 := by exact prefixLift 8182120
  have htrace : WordTrace (prefixWord ++ tailWord_8182120) baseStart_8182120 baseEnd_8182120 := by
    simpa [prefixWord, tailWord_8182120, baseEnd_8182120] using wordTrace_append hprefix tailTrace_8182120
  have hstable : (prefixWord ++ tailWord_8182120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182120).length < 2 ^ (prefixWord ++ tailWord_8182120).sum := by decide
  have hdescent : baseEnd_8182120 < baseStart_8182120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182123 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 3]
def baseStart_8182123 : Nat := 118140960795 + 8182123 * 2 ^ 59
def prefixEnd_8182123 : Nat := 4983230072969 + 3 ^ 40 * 8182123 * 2
def baseEnd_8182123 : Nat := 4201361873207596139833607

theorem tailTrace_8182123 : CollatzResearch.WordTrace tailWord_8182123 prefixEnd_8182123 4201361873207596139833607 := by
  unfold tailWord_8182123
  simp only [CollatzResearch.WordTrace]
  refine ⟨298426542536573241201183023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198951028357715494134122015 298426542536573241201183023)
  ·
    refine ⟨447639813804859861801774535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298426542536573241201183023 447639813804859861801774535)
    ·
      refine ⟨671459720707289792702661803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447639813804859861801774535 671459720707289792702661803)
      ·
        refine ⟨1007189581060934689053992705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671459720707289792702661803 1007189581060934689053992705)
        ·
          refine ⟨755392185795701016790494529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007189581060934689053992705 755392185795701016790494529)
          ·
            refine ⟨566544139346775762592870897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755392185795701016790494529 566544139346775762592870897)
            ·
              refine ⟨424908104510081821944653173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566544139346775762592870897 424908104510081821944653173)
              ·
                refine ⟨39835134797820170807311235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424908104510081821944653173 39835134797820170807311235)
                ·
                  refine ⟨59752702196730256210966853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39835134797820170807311235 59752702196730256210966853)
                  ·
                    refine ⟨11203631661886923039556285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59752702196730256210966853 11203631661886923039556285)
                    ·
                      refine ⟨4201361873207596139833607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203631661886923039556285 4201361873207596139833607)
                      ·
                        rfl

theorem cell23_8182123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 3].length) (baseStart_8182123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182123 prefixEnd_8182123 := by exact prefixLift 8182123
  have htrace : WordTrace (prefixWord ++ tailWord_8182123) baseStart_8182123 baseEnd_8182123 := by
    simpa [prefixWord, tailWord_8182123, baseEnd_8182123] using wordTrace_append hprefix tailTrace_8182123
  have hstable : (prefixWord ++ tailWord_8182123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182123).length < 2 ^ (prefixWord ++ tailWord_8182123).sum := by decide
  have hdescent : baseEnd_8182123 < baseStart_8182123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182147 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 3, 4]
def baseStart_8182147 : Nat := 118140960795 + 8182147 * 2 ^ 59
def prefixEnd_8182147 : Nat := 4983230072969 + 3 ^ 40 * 8182147 * 2
def baseEnd_8182147 : Nat := 1400458065581101348644499

theorem tailTrace_8182147 : CollatzResearch.WordTrace tailWord_8182147 prefixEnd_8182147 1400458065581101348644499 := by
  unfold tailWord_8182147
  simp only [CollatzResearch.WordTrace]
  refine ⟨298427417888486293300056695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198951611925657528866704463 298427417888486293300056695)
  ·
    refine ⟨447641126832729439950085043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298427417888486293300056695 447641126832729439950085043)
    ·
      refine ⟨671461690249094159925127565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447641126832729439950085043 671461690249094159925127565)
      ·
        refine ⟨251798133843410309971922837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671461690249094159925127565 251798133843410309971922837)
        ·
          refine ⟨11803037523909858279933883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251798133843410309971922837 11803037523909858279933883)
          ·
            refine ⟨17704556285864787419900825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803037523909858279933883 17704556285864787419900825)
            ·
              refine ⟨13278417214398590564925619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17704556285864787419900825 13278417214398590564925619)
              ·
                refine ⟨19917625821597885847388429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13278417214398590564925619 19917625821597885847388429)
                ·
                  refine ⟨7469109683099207192770661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19917625821597885847388429 7469109683099207192770661)
                  ·
                    refine ⟨1400458065581101348644499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469109683099207192770661 1400458065581101348644499)
                    ·
                      rfl

theorem cell23_8182147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 4].length) (baseStart_8182147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182147 prefixEnd_8182147 := by exact prefixLift 8182147
  have htrace : WordTrace (prefixWord ++ tailWord_8182147) baseStart_8182147 baseEnd_8182147 := by
    simpa [prefixWord, tailWord_8182147, baseEnd_8182147] using wordTrace_append hprefix tailTrace_8182147
  have hstable : (prefixWord ++ tailWord_8182147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182147).length < 2 ^ (prefixWord ++ tailWord_8182147).sum := by decide
  have hdescent : baseEnd_8182147 < baseStart_8182147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182204 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_8182204 : Nat := 118140960795 + 8182204 * 2 ^ 59
def prefixEnd_8182204 : Nat := 4983230072969 + 3 ^ 40 * 8182204 * 2
def baseEnd_8182204 : Nat := 4201403465140610322920735

theorem tailTrace_8182204 : CollatzResearch.WordTrace tailWord_8182204 prefixEnd_8182204 4201403465140610322920735 := by
  unfold tailWord_8182204
  simp only [CollatzResearch.WordTrace]
  refine ⟨149214748424639896017440833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198952997899519861356587777 149214748424639896017440833)
  ·
    refine ⟨111911061318479922013080625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149214748424639896017440833 111911061318479922013080625)
    ·
      refine ⟨83933295988859941509810469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111911061318479922013080625 83933295988859941509810469)
      ·
        refine ⟨15737492997911239033089463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83933295988859941509810469 15737492997911239033089463)
        ·
          refine ⟨23606239496866858549634195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737492997911239033089463 23606239496866858549634195)
          ·
            refine ⟨35409359245300287824451293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23606239496866858549634195 35409359245300287824451293)
            ·
              refine ⟨13278509716987607934169235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35409359245300287824451293 13278509716987607934169235)
              ·
                refine ⟨19917764575481411901253853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13278509716987607934169235 19917764575481411901253853)
                ·
                  refine ⟨7469161715805529462970195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19917764575481411901253853 7469161715805529462970195)
                  ·
                    refine ⟨11203742573708294194455293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7469161715805529462970195 11203742573708294194455293)
                    ·
                      refine ⟨4201403465140610322920735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203742573708294194455293 4201403465140610322920735)
                      ·
                        rfl

theorem cell23_8182204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_8182204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182204 prefixEnd_8182204 := by exact prefixLift 8182204
  have htrace : WordTrace (prefixWord ++ tailWord_8182204) baseStart_8182204 baseEnd_8182204 := by
    simpa [prefixWord, tailWord_8182204, baseEnd_8182204] using wordTrace_append hprefix tailTrace_8182204
  have hstable : (prefixWord ++ tailWord_8182204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182204).length < 2 ^ (prefixWord ++ tailWord_8182204).sum := by decide
  have hdescent : baseEnd_8182204 < baseStart_8182204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182233 : List Nat := [1, 2, 1, 2, 4, 1, 1, 11]
def baseStart_8182233 : Nat := 118140960795 + 8182233 * 2 ^ 59
def prefixEnd_8182233 : Nat := 4983230072969 + 3 ^ 40 * 8182233 * 2
def baseEnd_8182233 : Nat := 155608087262207063313263

theorem tailTrace_8182233 : CollatzResearch.WordTrace tailWord_8182233 prefixEnd_8182233 155608087262207063313263 := by
  unfold tailWord_8182233
  simp only [CollatzResearch.WordTrace]
  refine ⟨298430554566174729987687353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198953703044116486658458235 298430554566174729987687353)
  ·
    refine ⟨223822915924631047490765515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298430554566174729987687353 223822915924631047490765515)
    ·
      refine ⟨335734373886946571236148273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223822915924631047490765515 335734373886946571236148273)
      ·
        refine ⟨251800780415209928427111205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335734373886946571236148273 251800780415209928427111205)
        ·
          refine ⟨47212646327851861580083351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251800780415209928427111205 47212646327851861580083351)
          ·
            refine ⟨70818969491777792370125027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47212646327851861580083351 70818969491777792370125027)
            ·
              refine ⟨106228454237666688555187541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70818969491777792370125027 106228454237666688555187541)
              ·
                refine ⟨155608087262207063313263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106228454237666688555187541 155608087262207063313263)
                ·
                  rfl

theorem cell23_8182233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 11].length) (baseStart_8182233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182233 prefixEnd_8182233 := by exact prefixLift 8182233
  have htrace : WordTrace (prefixWord ++ tailWord_8182233) baseStart_8182233 baseEnd_8182233 := by
    simpa [prefixWord, tailWord_8182233, baseEnd_8182233] using wordTrace_append hprefix tailTrace_8182233
  have hstable : (prefixWord ++ tailWord_8182233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182233).length < 2 ^ (prefixWord ++ tailWord_8182233).sum := by decide
  have hdescent : baseEnd_8182233 < baseStart_8182233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182240 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_8182240 : Nat := 118140960795 + 8182240 * 2 ^ 59
def prefixEnd_8182240 : Nat := 4983230072969 + 3 ^ 40 * 8182240 * 2
def baseEnd_8182240 : Nat := 4201421950444172182070569

theorem tailTrace_8182240 : CollatzResearch.WordTrace tailWord_8182240 prefixEnd_8182240 4201421950444172182070569 := by
  unfold tailWord_8182240
  simp only [CollatzResearch.WordTrace]
  refine ⟨149215404938574685091596087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198953873251432913455461449 149215404938574685091596087)
  ·
    refine ⟨223823107407862027637394131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149215404938574685091596087 223823107407862027637394131)
    ·
      refine ⟨335734661111793041456091197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223823107407862027637394131 335734661111793041456091197)
      ·
        refine ⟨125900497916922390546034199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335734661111793041456091197 125900497916922390546034199)
        ·
          refine ⟨188850746875383585819051299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125900497916922390546034199 188850746875383585819051299)
          ·
            refine ⟨283276120313075378728576949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188850746875383585819051299 283276120313075378728576949)
            ·
              refine ⟨26557136279350816755804089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283276120313075378728576949 26557136279350816755804089)
              ·
                refine ⟨19917852209513112566853067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26557136279350816755804089 19917852209513112566853067)
                ·
                  refine ⟨29876778314269668850279601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19917852209513112566853067 29876778314269668850279601)
                  ·
                    refine ⟨22407583735702251637709701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29876778314269668850279601 22407583735702251637709701)
                    ·
                      refine ⟨4201421950444172182070569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22407583735702251637709701 4201421950444172182070569)
                      ·
                        rfl

theorem cell23_8182240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_8182240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182240 prefixEnd_8182240 := by exact prefixLift 8182240
  have htrace : WordTrace (prefixWord ++ tailWord_8182240) baseStart_8182240 baseEnd_8182240 := by
    simpa [prefixWord, tailWord_8182240, baseEnd_8182240] using wordTrace_append hprefix tailTrace_8182240
  have hstable : (prefixWord ++ tailWord_8182240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182240).length < 2 ^ (prefixWord ++ tailWord_8182240).sum := by decide
  have hdescent : baseEnd_8182240 < baseStart_8182240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182254 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_8182254 : Nat := 118140960795 + 8182254 * 2 ^ 59
def prefixEnd_8182254 : Nat := 4983230072969 + 3 ^ 40 * 8182254 * 2
def baseEnd_8182254 : Nat := 1400476379724445042431835

theorem tailTrace_8182254 : CollatzResearch.WordTrace tailWord_8182254 prefixEnd_8182254 1400476379724445042431835 := by
  unfold tailWord_8182254
  simp only [CollatzResearch.WordTrace]
  refine ⟨37303915062387331321775227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198954213666065767049467877 37303915062387331321775227)
  ·
    refine ⟨55955872593580996982662841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37303915062387331321775227 55955872593580996982662841)
    ·
      refine ⟨41966904445185747736997131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55955872593580996982662841 41966904445185747736997131)
      ·
        refine ⟨62950356667778621605495697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41966904445185747736997131 62950356667778621605495697)
        ·
          refine ⟨47212767500833966204121773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62950356667778621605495697 47212767500833966204121773)
          ·
            refine ⟨17704787812812737326545665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47212767500833966204121773 17704787812812737326545665)
            ·
              refine ⟨13278590859609552994909249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17704787812812737326545665 13278590859609552994909249)
              ·
                refine ⟨9958943144707164746181937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13278590859609552994909249 9958943144707164746181937)
                ·
                  refine ⟨7469207358530373559636453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9958943144707164746181937 7469207358530373559636453)
                  ·
                    refine ⟨1400476379724445042431835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469207358530373559636453 1400476379724445042431835)
                    ·
                      rfl

theorem cell23_8182254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_8182254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182254 prefixEnd_8182254 := by exact prefixLift 8182254
  have htrace : WordTrace (prefixWord ++ tailWord_8182254) baseStart_8182254 baseEnd_8182254 := by
    simpa [prefixWord, tailWord_8182254, baseEnd_8182254] using wordTrace_append hprefix tailTrace_8182254
  have hstable : (prefixWord ++ tailWord_8182254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182254).length < 2 ^ (prefixWord ++ tailWord_8182254).sum := by decide
  have hdescent : baseEnd_8182254 < baseStart_8182254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182295 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 1, 2, 2]
def baseStart_8182295 : Nat := 118140960795 + 8182295 * 2 ^ 59
def prefixEnd_8182295 : Nat := 4983230072969 + 3 ^ 40 * 8182295 * 2
def baseEnd_8182295 : Nat := 4201450191880169466882817

theorem tailTrace_8182295 : CollatzResearch.WordTrace tailWord_8182295 prefixEnd_8182295 4201450191880169466882817 := by
  unfold tailWord_8182295
  simp only [CollatzResearch.WordTrace]
  refine ⟨298432815891950114576444339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198955210594633409717629559 298432815891950114576444339)
  ·
    refine ⟨447649223837925171864666509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298432815891950114576444339 447649223837925171864666509)
    ·
      refine ⟨167868458939221939449249941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447649223837925171864666509 167868458939221939449249941)
      ·
        refine ⟨7868834012776028411683591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167868458939221939449249941 7868834012776028411683591)
        ·
          refine ⟨11803251019164042617525387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868834012776028411683591 11803251019164042617525387)
          ·
            refine ⟨17704876528746063926288081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803251019164042617525387 17704876528746063926288081)
            ·
              refine ⟨13278657396559547944716061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17704876528746063926288081 13278657396559547944716061)
              ·
                refine ⟨4979496523709830479268523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13278657396559547944716061 4979496523709830479268523)
                ·
                  refine ⟨7469244785564745718902785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979496523709830479268523 7469244785564745718902785)
                  ·
                    refine ⟨5601933589173559289177089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7469244785564745718902785 5601933589173559289177089)
                    ·
                      refine ⟨4201450191880169466882817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601933589173559289177089 4201450191880169466882817)
                      ·
                        rfl

theorem cell23_8182295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_8182295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182295 prefixEnd_8182295 := by exact prefixLift 8182295
  have htrace : WordTrace (prefixWord ++ tailWord_8182295) baseStart_8182295 baseEnd_8182295 := by
    simpa [prefixWord, tailWord_8182295, baseEnd_8182295] using wordTrace_append hprefix tailTrace_8182295
  have hstable : (prefixWord ++ tailWord_8182295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182295).length < 2 ^ (prefixWord ++ tailWord_8182295).sum := by decide
  have hdescent : baseEnd_8182295 < baseStart_8182295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182320 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_8182320 : Nat := 118140960795 + 8182320 * 2 ^ 59
def prefixEnd_8182320 : Nat := 4983230072969 + 3 ^ 40 * 8182320 * 2
def baseEnd_8182320 : Nat := 4201463028896531869070201

theorem tailTrace_8182320 : CollatzResearch.WordTrace tailWord_8182320 prefixEnd_8182320 4201463028896531869070201 := by
  unfold tailWord_8182320
  simp only [CollatzResearch.WordTrace]
  refine ⟨149216863858429771923052207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198955818477906362564069609 149216863858429771923052207)
  ·
    refine ⟨223825295787644657884578311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149216863858429771923052207 223825295787644657884578311)
    ·
      refine ⟨335737943681466986826867467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223825295787644657884578311 335737943681466986826867467)
      ·
        refine ⟨503606915522200480240301201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335737943681466986826867467 503606915522200480240301201)
        ·
          refine ⟨377705186641650360180225901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503606915522200480240301201 377705186641650360180225901)
          ·
            refine ⟨141639444990618885067584713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377705186641650360180225901 141639444990618885067584713)
            ·
              refine ⟨106229583742964163800688535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141639444990618885067584713 106229583742964163800688535)
              ·
                refine ⟨159344375614446245701032803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106229583742964163800688535 159344375614446245701032803)
                ·
                  refine ⟨239016563421669368551549205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159344375614446245701032803 239016563421669368551549205)
                  ·
                    refine ⟨11203901410390751650853869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 239016563421669368551549205 11203901410390751650853869)
                    ·
                      refine ⟨4201463028896531869070201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11203901410390751650853869 4201463028896531869070201)
                      ·
                        rfl

theorem cell23_8182320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_8182320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182320 prefixEnd_8182320 := by exact prefixLift 8182320
  have htrace : WordTrace (prefixWord ++ tailWord_8182320) baseStart_8182320 baseEnd_8182320 := by
    simpa [prefixWord, tailWord_8182320, baseEnd_8182320] using wordTrace_append hprefix tailTrace_8182320
  have hstable : (prefixWord ++ tailWord_8182320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182320).length < 2 ^ (prefixWord ++ tailWord_8182320).sum := by decide
  have hdescent : baseEnd_8182320 < baseStart_8182320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182377 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 2, 5, 2]
def baseStart_8182377 : Nat := 118140960795 + 8182377 * 2 ^ 59
def prefixEnd_8182377 : Nat := 4983230072969 + 3 ^ 40 * 8182377 * 2
def baseEnd_8182377 : Nat := 4201492297293838146057439

theorem tailTrace_8182377 : CollatzResearch.WordTrace tailWord_8182377 prefixEnd_8182377 4201492297293838146057439 := by
  unfold tailWord_8182377
  simp only [CollatzResearch.WordTrace]
  refine ⟨298435806677653042580929385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198957204451768695053952923 298435806677653042580929385)
  ·
    refine ⟨223826855008239781935697039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298435806677653042580929385 223826855008239781935697039)
    ·
      refine ⟨335740282512359672903545559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223826855008239781935697039 335740282512359672903545559)
      ·
        refine ⟨503610423768539509355318339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335740282512359672903545559 503610423768539509355318339)
        ·
          refine ⟨755415635652809264032977509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503610423768539509355318339 755415635652809264032977509)
          ·
            refine ⟨141640431684901737006183283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 755415635652809264032977509 141640431684901737006183283)
            ·
              refine ⟨212460647527352605509274925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141640431684901737006183283 212460647527352605509274925)
              ·
                refine ⟨79672742822757227065978097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212460647527352605509274925 79672742822757227065978097)
                ·
                  refine ⟨59754557117067920299483573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79672742822757227065978097 59754557117067920299483573)
                  ·
                    refine ⟨5601989729725117528076585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59754557117067920299483573 5601989729725117528076585)
                    ·
                      refine ⟨4201492297293838146057439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5601989729725117528076585 4201492297293838146057439)
                      ·
                        rfl

theorem cell23_8182377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 5, 2].length) (baseStart_8182377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182377 prefixEnd_8182377 := by exact prefixLift 8182377
  have htrace : WordTrace (prefixWord ++ tailWord_8182377) baseStart_8182377 baseEnd_8182377 := by
    simpa [prefixWord, tailWord_8182377, baseEnd_8182377] using wordTrace_append hprefix tailTrace_8182377
  have hstable : (prefixWord ++ tailWord_8182377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182377).length < 2 ^ (prefixWord ++ tailWord_8182377).sum := by decide
  have hdescent : baseEnd_8182377 < baseStart_8182377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182380 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_8182380 : Nat := 118140960795 + 8182380 * 2 ^ 59
def prefixEnd_8182380 : Nat := 4983230072969 + 3 ^ 40 * 8182380 * 2
def baseEnd_8182380 : Nat := 4201493837735801634319925

theorem tailTrace_8182380 : CollatzResearch.WordTrace tailWord_8182380 prefixEnd_8182380 4201493837735801634319925 := by
  unfold tailWord_8182380
  simp only [CollatzResearch.WordTrace]
  refine ⟨149217958048321087046644297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198957277397761449395525729 149217958048321087046644297)
  ·
    refine ⟨111913468536240815284983223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149217958048321087046644297 111913468536240815284983223)
    ·
      refine ⟨167870202804361222927474835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111913468536240815284983223 167870202804361222927474835)
      ·
        refine ⟨251805304206541834391212253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167870202804361222927474835 251805304206541834391212253)
        ·
          refine ⟨94426989077453187896704595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251805304206541834391212253 94426989077453187896704595)
          ·
            refine ⟨141640483616179781845056893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94426989077453187896704595 141640483616179781845056893)
            ·
              refine ⟨53115181356067418191896335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141640483616179781845056893 53115181356067418191896335)
              ·
                refine ⟨79672772034101127287844503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53115181356067418191896335 79672772034101127287844503)
                ·
                  refine ⟨119509158051151690931766755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79672772034101127287844503 119509158051151690931766755)
                  ·
                    refine ⟨179263737076727536397650133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119509158051151690931766755 179263737076727536397650133)
                    ·
                      refine ⟨4201493837735801634319925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179263737076727536397650133 4201493837735801634319925)
                      ·
                        rfl

theorem cell23_8182380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_8182380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182380 prefixEnd_8182380 := by exact prefixLift 8182380
  have htrace : WordTrace (prefixWord ++ tailWord_8182380) baseStart_8182380 baseEnd_8182380 := by
    simpa [prefixWord, tailWord_8182380, baseEnd_8182380] using wordTrace_append hprefix tailTrace_8182380
  have hstable : (prefixWord ++ tailWord_8182380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182380).length < 2 ^ (prefixWord ++ tailWord_8182380).sum := by decide
  have hdescent : baseEnd_8182380 < baseStart_8182380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182404 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_8182404 : Nat := 118140960795 + 8182404 * 2 ^ 59
def prefixEnd_8182404 : Nat := 4983230072969 + 3 ^ 40 * 8182404 * 2
def baseEnd_8182404 : Nat := 1400502053757169846806605

theorem tailTrace_8182404 : CollatzResearch.WordTrace tailWord_8182404 prefixEnd_8182404 1400502053757169846806605 := by
  unfold tailWord_8182404
  simp only [CollatzResearch.WordTrace]
  refine ⟨149218395724277613096081133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198957860965703484128108177 149218395724277613096081133)
  ·
    refine ⟨55956898396604104911030425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149218395724277613096081133 55956898396604104911030425)
    ·
      refine ⟨41967673797453078683272819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55956898396604104911030425 41967673797453078683272819)
      ·
        refine ⟨62951510696179618024909229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41967673797453078683272819 62951510696179618024909229)
        ·
          refine ⟨23606816511067356759340961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62951510696179618024909229 23606816511067356759340961)
          ·
            refine ⟨17705112383300517569505721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23606816511067356759340961 17705112383300517569505721)
            ·
              refine ⟨13278834287475388177129291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17705112383300517569505721 13278834287475388177129291)
              ·
                refine ⟨19918251431213082265693937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13278834287475388177129291 19918251431213082265693937)
                ·
                  refine ⟨14938688573409811699270453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19918251431213082265693937 14938688573409811699270453)
                  ·
                    refine ⟨1400502053757169846806605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14938688573409811699270453 1400502053757169846806605)
                    ·
                      rfl

theorem cell23_8182404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_8182404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182404 prefixEnd_8182404 := by exact prefixLift 8182404
  have htrace : WordTrace (prefixWord ++ tailWord_8182404) baseStart_8182404 baseEnd_8182404 := by
    simpa [prefixWord, tailWord_8182404, baseEnd_8182404] using wordTrace_append hprefix tailTrace_8182404
  have hstable : (prefixWord ++ tailWord_8182404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182404).length < 2 ^ (prefixWord ++ tailWord_8182404).sum := by decide
  have hdescent : baseEnd_8182404 < baseStart_8182404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182424 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 2, 4, 2]
def baseStart_8182424 : Nat := 118140960795 + 8182424 * 2 ^ 59
def prefixEnd_8182424 : Nat := 4983230072969 + 3 ^ 40 * 8182424 * 2
def baseEnd_8182424 : Nat := 4201516430884599462169723

theorem tailTrace_8182424 : CollatzResearch.WordTrace tailWord_8182424 prefixEnd_8182424 4201516430884599462169723 := by
  unfold tailWord_8182424
  simp only [CollatzResearch.WordTrace]
  refine ⟨149218760454241384803945163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198958347272321846405260217 149218760454241384803945163)
  ·
    refine ⟨223828140681362077205917745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149218760454241384803945163 223828140681362077205917745)
    ·
      refine ⟨167871105511021557904438309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223828140681362077205917745 167871105511021557904438309)
      ·
        refine ⟨31475832283316542107082183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167871105511021557904438309 31475832283316542107082183)
        ·
          refine ⟨47213748424974813160623275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31475832283316542107082183 47213748424974813160623275)
          ·
            refine ⟨70820622637462219740934913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47213748424974813160623275 70820622637462219740934913)
            ·
              refine ⟨53115466978096664805701185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70820622637462219740934913 53115466978096664805701185)
              ·
                refine ⟨39836600233572498604275889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53115466978096664805701185 39836600233572498604275889)
                ·
                  refine ⟨29877450175179373953206917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39836600233572498604275889 29877450175179373953206917)
                  ·
                    refine ⟨5602021907846132616226297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29877450175179373953206917 5602021907846132616226297)
                    ·
                      refine ⟨4201516430884599462169723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602021907846132616226297 4201516430884599462169723)
                      ·
                        rfl

theorem cell23_8182424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_8182424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182424 prefixEnd_8182424 := by exact prefixLift 8182424
  have htrace : WordTrace (prefixWord ++ tailWord_8182424) baseStart_8182424 baseEnd_8182424 := by
    simpa [prefixWord, tailWord_8182424, baseEnd_8182424] using wordTrace_append hprefix tailTrace_8182424
  have hstable : (prefixWord ++ tailWord_8182424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182424).length < 2 ^ (prefixWord ++ tailWord_8182424).sum := by decide
  have hdescent : baseEnd_8182424 < baseStart_8182424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182447 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 6]
def baseStart_8182447 : Nat := 118140960795 + 8182447 * 2 ^ 59
def prefixEnd_8182447 : Nat := 4983230072969 + 3 ^ 40 * 8182447 * 2
def baseEnd_8182447 : Nat := 466836471215516985798013

theorem tailTrace_8182447 : CollatzResearch.WordTrace tailWord_8182447 prefixEnd_8182447 466836471215516985798013 := by
  unfold tailWord_8182447
  simp only [CollatzResearch.WordTrace]
  refine ⟨298438359787399444535977595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198958906524932963023985063 298438359787399444535977595)
  ·
    refine ⟨447657539681099166803966393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298438359787399444535977595 447657539681099166803966393)
    ·
      refine ⟨335743154760824375102974795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447657539681099166803966393 335743154760824375102974795)
      ·
        refine ⟨503614732141236562654462193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335743154760824375102974795 503614732141236562654462193)
        ·
          refine ⟨377711049105927421990846645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503614732141236562654462193 377711049105927421990846645)
          ·
            refine ⟨35410410853680695811641873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377711049105927421990846645 35410410853680695811641873)
            ·
              refine ⟨26557808140260521858731405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35410410853680695811641873 26557808140260521858731405)
              ·
                refine ⟨9959178052597695697024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26557808140260521858731405 9959178052597695697024277)
                ·
                  refine ⟨466836471215516985798013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9959178052597695697024277 466836471215516985798013)
                  ·
                    rfl

theorem cell23_8182447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 6].length) (baseStart_8182447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182447 prefixEnd_8182447 := by exact prefixLift 8182447
  have htrace : WordTrace (prefixWord ++ tailWord_8182447) baseStart_8182447 baseEnd_8182447 := by
    simpa [prefixWord, tailWord_8182447, baseEnd_8182447] using wordTrace_append hprefix tailTrace_8182447
  have hstable : (prefixWord ++ tailWord_8182447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182447).length < 2 ^ (prefixWord ++ tailWord_8182447).sum := by decide
  have hdescent : baseEnd_8182447 < baseStart_8182447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182461 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_8182461 : Nat := 118140960795 + 8182461 * 2 ^ 59
def prefixEnd_8182461 : Nat := 4983230072969 + 3 ^ 40 * 8182461 * 2
def baseEnd_8182461 : Nat := 4201535429668815817407053

theorem tailTrace_8182461 : CollatzResearch.WordTrace tailWord_8182461 prefixEnd_8182461 4201535429668815817407053 := by
  unfold tailWord_8182461
  simp only [CollatzResearch.WordTrace]
  refine ⟨298438870409348724926987237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198959246939565816617991491 298438870409348724926987237)
  ·
    refine ⟨55957288201752885923810107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298438870409348724926987237 55957288201752885923810107)
    ·
      refine ⟨83935932302629328885715161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55957288201752885923810107 83935932302629328885715161)
      ·
        refine ⟨62951949226971996664286371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83935932302629328885715161 62951949226971996664286371)
        ·
          refine ⟨94427923840457994996429557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62951949226971996664286371 94427923840457994996429557)
          ·
            refine ⟨8852617860042937030915271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94427923840457994996429557 8852617860042937030915271)
            ·
              refine ⟨13278926790064405546372907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8852617860042937030915271 13278926790064405546372907)
              ·
                refine ⟨19918390185096608319559361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13278926790064405546372907 19918390185096608319559361)
                ·
                  refine ⟨14938792638822456239669521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19918390185096608319559361 14938792638822456239669521)
                  ·
                    refine ⟨11204094479116842179752141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14938792638822456239669521 11204094479116842179752141)
                    ·
                      refine ⟨4201535429668815817407053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204094479116842179752141 4201535429668815817407053)
                      ·
                        rfl

theorem cell23_8182461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_8182461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182461 prefixEnd_8182461 := by exact prefixLift 8182461
  have htrace : WordTrace (prefixWord ++ tailWord_8182461) baseStart_8182461 baseEnd_8182461 := by
    simpa [prefixWord, tailWord_8182461, baseEnd_8182461] using wordTrace_append hprefix tailTrace_8182461
  have hstable : (prefixWord ++ tailWord_8182461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182461).length < 2 ^ (prefixWord ++ tailWord_8182461).sum := by decide
  have hdescent : baseEnd_8182461 < baseStart_8182461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182468 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_8182468 : Nat := 118140960795 + 8182468 * 2 ^ 59
def prefixEnd_8182468 : Nat := 4983230072969 + 3 ^ 40 * 8182468 * 2
def baseEnd_8182468 : Nat := 1400513008011132430006507

theorem tailTrace_8182468 : CollatzResearch.WordTrace tailWord_8182468 prefixEnd_8182468 1400513008011132430006507 := by
  unfold tailWord_8182468
  simp only [CollatzResearch.WordTrace]
  refine ⟨149219562860161682561246029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198959417146882243414994705 149219562860161682561246029)
  ·
    refine ⟨55957336072560630960467261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149219562860161682561246029 55957336072560630960467261)
    ·
      refine ⟨20984001027210236610175223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55957336072560630960467261 20984001027210236610175223)
      ·
        refine ⟨31476001540815354915262835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984001027210236610175223 31476001540815354915262835)
        ·
          refine ⟨47214002311223032372894253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31476001540815354915262835 47214002311223032372894253)
          ·
            refine ⟨17705250866708637139835345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47214002311223032372894253 17705250866708637139835345)
            ·
              refine ⟨13278938150031477854876509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17705250866708637139835345 13278938150031477854876509)
              ·
                refine ⟨4979601806261804195578691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13278938150031477854876509 4979601806261804195578691)
                ·
                  refine ⟨7469402709392706293368037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979601806261804195578691 7469402709392706293368037)
                  ·
                    refine ⟨1400513008011132430006507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469402709392706293368037 1400513008011132430006507)
                    ·
                      rfl

theorem cell23_8182468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_8182468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182468 prefixEnd_8182468 := by exact prefixLift 8182468
  have htrace : WordTrace (prefixWord ++ tailWord_8182468) baseStart_8182468 baseEnd_8182468 := by
    simpa [prefixWord, tailWord_8182468, baseEnd_8182468] using wordTrace_append hprefix tailTrace_8182468
  have hstable : (prefixWord ++ tailWord_8182468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182468).length < 2 ^ (prefixWord ++ tailWord_8182468).sum := by decide
  have hdescent : baseEnd_8182468 < baseStart_8182468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182524 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_8182524 : Nat := 118140960795 + 8182524 * 2 ^ 59
def prefixEnd_8182524 : Nat := 4983230072969 + 3 ^ 40 * 8182524 * 2
def baseEnd_8182524 : Nat := 1400522592983349690306421

theorem tailTrace_8182524 : CollatzResearch.WordTrace tailWord_8182524 prefixEnd_8182524 1400522592983349690306421 := by
  unfold tailWord_8182524
  simp only [CollatzResearch.WordTrace]
  refine ⟨149220584104060243343265313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198960778805413657791020417 149220584104060243343265313)
  ·
    refine ⟨111915438078045182507448985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149220584104060243343265313 111915438078045182507448985)
    ·
      refine ⟨83936578558533886880586739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111915438078045182507448985 83936578558533886880586739)
      ·
        refine ⟨125904867837800830320880109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83936578558533886880586739 125904867837800830320880109)
        ·
          refine ⟨47214325439175311370330041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125904867837800830320880109 47214325439175311370330041)
          ·
            refine ⟨35410744079381483527747531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47214325439175311370330041 35410744079381483527747531)
            ·
              refine ⟨53116116119072225291621297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35410744079381483527747531 53116116119072225291621297)
              ·
                refine ⟨39837087089304168968715973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53116116119072225291621297 39837087089304168968715973)
                ·
                  refine ⟨7469453829244531681634245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39837087089304168968715973 7469453829244531681634245)
                  ·
                    refine ⟨1400522592983349690306421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469453829244531681634245 1400522592983349690306421)
                    ·
                      rfl

theorem cell23_8182524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_8182524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182524 prefixEnd_8182524 := by exact prefixLift 8182524
  have htrace : WordTrace (prefixWord ++ tailWord_8182524) baseStart_8182524 baseEnd_8182524 := by
    simpa [prefixWord, tailWord_8182524, baseEnd_8182524] using wordTrace_append hprefix tailTrace_8182524
  have hstable : (prefixWord ++ tailWord_8182524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182524).length < 2 ^ (prefixWord ++ tailWord_8182524).sum := by decide
  have hdescent : baseEnd_8182524 < baseStart_8182524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182527 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_8182527 : Nat := 118140960795 + 8182527 * 2 ^ 59
def prefixEnd_8182527 : Nat := 4983230072969 + 3 ^ 40 * 8182527 * 2
def baseEnd_8182527 : Nat := 4201569319392012559181749

theorem tailTrace_8182527 : CollatzResearch.WordTrace tailWord_8182527 prefixEnd_8182527 4201569319392012559181749 := by
  unfold tailWord_8182527
  simp only [CollatzResearch.WordTrace]
  refine ⟨298441277627109618198889835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198960851751406412132593223 298441277627109618198889835)
  ·
    refine ⟨447661916440664427298334753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298441277627109618198889835 447661916440664427298334753)
    ·
      refine ⟨335746437330498320473751065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447661916440664427298334753 335746437330498320473751065)
      ·
        refine ⟨251809827997873740355313299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335746437330498320473751065 251809827997873740355313299)
        ·
          refine ⟨377714741996810610532969949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251809827997873740355313299 377714741996810610532969949)
          ·
            refine ⟨141643028248803978949863731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377714741996810610532969949 141643028248803978949863731)
            ·
              refine ⟨212464542373205968424795597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141643028248803978949863731 212464542373205968424795597)
              ·
                refine ⟨79674203389952238159298349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212464542373205968424795597 79674203389952238159298349)
                ·
                  refine ⟨29877826271232089309736881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79674203389952238159298349 29877826271232089309736881)
                  ·
                    refine ⟨22408369703424066982302661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29877826271232089309736881 22408369703424066982302661)
                    ·
                      refine ⟨4201569319392012559181749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22408369703424066982302661 4201569319392012559181749)
                      ·
                        rfl

theorem cell23_8182527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_8182527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182527 prefixEnd_8182527 := by exact prefixLift 8182527
  have htrace : WordTrace (prefixWord ++ tailWord_8182527) baseStart_8182527 baseEnd_8182527 := by
    simpa [prefixWord, tailWord_8182527, baseEnd_8182527] using wordTrace_append hprefix tailTrace_8182527
  have hstable : (prefixWord ++ tailWord_8182527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182527).length < 2 ^ (prefixWord ++ tailWord_8182527).sum := by decide
  have hdescent : baseEnd_8182527 < baseStart_8182527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182581 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_8182581 : Nat := 118140960795 + 8182581 * 2 ^ 59
def prefixEnd_8182581 : Nat := 4983230072969 + 3 ^ 40 * 8182581 * 2
def baseEnd_8182581 : Nat := 4201597047347355347906501

theorem tailTrace_8182581 : CollatzResearch.WordTrace tailWord_8182581 prefixEnd_8182581 4201597047347355347906501 := by
  unfold tailWord_8182581
  simp only [CollatzResearch.WordTrace]
  refine ⟨298443247168913985421355597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198962164779275990280903731 298443247168913985421355597)
  ·
    refine ⟨111916217688342744533008349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298443247168913985421355597 111916217688342744533008349)
    ·
      refine ⟨41968581633128529199878131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111916217688342744533008349 41968581633128529199878131)
      ·
        refine ⟨62952872449692793799817197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41968581633128529199878131 62952872449692793799817197)
        ·
          refine ⟨23607327168634797674931449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62952872449692793799817197 23607327168634797674931449)
          ·
            refine ⟨17705495376476098256198587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23607327168634797674931449 17705495376476098256198587)
            ·
              refine ⟨26558243064714147384297881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17705495376476098256198587 26558243064714147384297881)
              ·
                refine ⟨19918682298535610538223411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26558243064714147384297881 19918682298535610538223411)
                ·
                  refine ⟨29878023447803415807335117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19918682298535610538223411 29878023447803415807335117)
                  ·
                    refine ⟨11204258792926280927750669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29878023447803415807335117 11204258792926280927750669)
                    ·
                      refine ⟨4201597047347355347906501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204258792926280927750669 4201597047347355347906501)
                      ·
                        rfl

theorem cell23_8182581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_8182581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182581 prefixEnd_8182581 := by exact prefixLift 8182581
  have htrace : WordTrace (prefixWord ++ tailWord_8182581) baseStart_8182581 baseEnd_8182581 := by
    simpa [prefixWord, tailWord_8182581, baseEnd_8182581] using wordTrace_append hprefix tailTrace_8182581
  have hstable : (prefixWord ++ tailWord_8182581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182581).length < 2 ^ (prefixWord ++ tailWord_8182581).sum := by decide
  have hdescent : baseEnd_8182581 < baseStart_8182581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182604 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_8182604 : Nat := 118140960795 + 8182604 * 2 ^ 59
def prefixEnd_8182604 : Nat := 4983230072969 + 3 ^ 40 * 8182604 * 2
def baseEnd_8182604 : Nat := 4201608857402408757918895

theorem tailTrace_8182604 : CollatzResearch.WordTrace tailWord_8182604 prefixEnd_8182604 4201608857402408757918895 := by
  unfold tailWord_8182604
  simp only [CollatzResearch.WordTrace]
  refine ⟨149222043023915330174721433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198962724031887106899628577 149222043023915330174721433)
  ·
    refine ⟨111916532267936497631041075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149222043023915330174721433 111916532267936497631041075)
    ·
      refine ⟨167874798401904746446561613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111916532267936497631041075 167874798401904746446561613)
      ·
        refine ⟨62953049400714279917460605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167874798401904746446561613 62953049400714279917460605)
        ·
          refine ⟨23607393525267854969047727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62953049400714279917460605 23607393525267854969047727)
          ·
            refine ⟨35411090287901782453571591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23607393525267854969047727 35411090287901782453571591)
            ·
              refine ⟨53116635431852673680357387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35411090287901782453571591 53116635431852673680357387)
              ·
                refine ⟨79674953147779010520536081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53116635431852673680357387 79674953147779010520536081)
                ·
                  refine ⟨59756214860834257890402061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79674953147779010520536081 59756214860834257890402061)
                  ·
                    refine ⟨22408580572812846708900773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59756214860834257890402061 22408580572812846708900773)
                    ·
                      refine ⟨4201608857402408757918895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22408580572812846708900773 4201608857402408757918895)
                      ·
                        rfl

theorem cell23_8182604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_8182604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182604 prefixEnd_8182604 := by exact prefixLift 8182604
  have htrace : WordTrace (prefixWord ++ tailWord_8182604) baseStart_8182604 baseEnd_8182604 := by
    simpa [prefixWord, tailWord_8182604, baseEnd_8182604] using wordTrace_append hprefix tailTrace_8182604
  have hstable : (prefixWord ++ tailWord_8182604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182604).length < 2 ^ (prefixWord ++ tailWord_8182604).sum := by decide
  have hdescent : baseEnd_8182604 < baseStart_8182604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182624 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_8182624 : Nat := 118140960795 + 8182624 * 2 ^ 59
def prefixEnd_8182624 : Nat := 4983230072969 + 3 ^ 40 * 8182624 * 2
def baseEnd_8182624 : Nat := 4201619127015498679668803

theorem tailTrace_8182624 : CollatzResearch.WordTrace tailWord_8182624 prefixEnd_8182624 4201619127015498679668803 := by
  unfold tailWord_8182624
  simp only [CollatzResearch.WordTrace]
  refine ⟨149222407753879101882585463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198963210338505469176780617 149222407753879101882585463)
  ·
    refine ⟨223833611630818652823878195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149222407753879101882585463 223833611630818652823878195)
    ·
      refine ⟨335750417446227979235817293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223833611630818652823878195 335750417446227979235817293)
      ·
        refine ⟨125906406542335492213431485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335750417446227979235817293 125906406542335492213431485)
        ·
          refine ⟨47214902453375809580036807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125906406542335492213431485 47214902453375809580036807)
          ·
            refine ⟨70822353680063714370055211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47214902453375809580036807 70822353680063714370055211)
            ·
              refine ⟨106233530520095571555082817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70822353680063714370055211 106233530520095571555082817)
              ·
                refine ⟨79675147890071678666312113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106233530520095571555082817 79675147890071678666312113)
                ·
                  refine ⟨59756360917553758999734085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79675147890071678666312113 59756360917553758999734085)
                  ·
                    refine ⟨11204317672041329812450141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59756360917553758999734085 11204317672041329812450141)
                    ·
                      refine ⟨4201619127015498679668803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204317672041329812450141 4201619127015498679668803)
                      ·
                        rfl

theorem cell23_8182624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_8182624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182624 prefixEnd_8182624 := by exact prefixLift 8182624
  have htrace : WordTrace (prefixWord ++ tailWord_8182624) baseStart_8182624 baseEnd_8182624 := by
    simpa [prefixWord, tailWord_8182624, baseEnd_8182624] using wordTrace_append hprefix tailTrace_8182624
  have hstable : (prefixWord ++ tailWord_8182624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182624).length < 2 ^ (prefixWord ++ tailWord_8182624).sum := by decide
  have hdescent : baseEnd_8182624 < baseStart_8182624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182661 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 5]
def baseStart_8182661 : Nat := 118140960795 + 8182661 * 2 ^ 59
def prefixEnd_8182661 : Nat := 4983230072969 + 3 ^ 40 * 8182661 * 2
def baseEnd_8182661 : Nat := 466848680644412781656237

theorem tailTrace_8182661 : CollatzResearch.WordTrace tailWord_8182661 prefixEnd_8182661 466848680644412781656237 := by
  unfold tailWord_8182661
  simp only [CollatzResearch.WordTrace]
  refine ⟨298446165008624159084267837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198964110005749439389511891 298446165008624159084267837)
  ·
    refine ⟨111917311878234059656600439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298446165008624159084267837 111917311878234059656600439)
    ·
      refine ⟨167875967817351089484900659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111917311878234059656600439 167875967817351089484900659)
      ·
        refine ⟨251813951726026634227350989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167875967817351089484900659 251813951726026634227350989)
        ·
          refine ⟨94430231897259987835256621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251813951726026634227350989 94430231897259987835256621)
          ·
            refine ⟨35411336961472495438221233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94430231897259987835256621 35411336961472495438221233)
            ·
              refine ⟨26558502721104371578665925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35411336961472495438221233 26558502721104371578665925)
              ·
                refine ⟨4979719260207069670999861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26558502721104371578665925 4979719260207069670999861)
                ·
                  refine ⟨466848680644412781656237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4979719260207069670999861 466848680644412781656237)
                  ·
                    rfl

theorem cell23_8182661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_8182661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182661 prefixEnd_8182661 := by exact prefixLift 8182661
  have htrace : WordTrace (prefixWord ++ tailWord_8182661) baseStart_8182661 baseEnd_8182661 := by
    simpa [prefixWord, tailWord_8182661, baseEnd_8182661] using wordTrace_append hprefix tailTrace_8182661
  have hstable : (prefixWord ++ tailWord_8182661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182661).length < 2 ^ (prefixWord ++ tailWord_8182661).sum := by decide
  have hdescent : baseEnd_8182661 < baseStart_8182661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182695 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 5]
def baseStart_8182695 : Nat := 118140960795 + 8182695 * 2 ^ 59
def prefixEnd_8182695 : Nat := 4983230072969 + 3 ^ 40 * 8182695 * 2
def baseEnd_8182695 : Nat := 466850620460218655764553

theorem tailTrace_8182695 : CollatzResearch.WordTrace tailWord_8182695 prefixEnd_8182695 466850620460218655764553 := by
  unfold tailWord_8182695
  simp only [CollatzResearch.WordTrace]
  refine ⟨298447405090500982891005539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198964936727000655260670359 298447405090500982891005539)
  ·
    refine ⟨447671107635751474336508309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298447405090500982891005539 447671107635751474336508309)
    ·
      refine ⟨20984583170425850359523827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 447671107635751474336508309 20984583170425850359523827)
      ·
        refine ⟨31476874755638775539285741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984583170425850359523827 31476874755638775539285741)
        ·
          refine ⟨11803828033364540827232153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31476874755638775539285741 11803828033364540827232153)
          ·
            refine ⟨8852871025023405620424115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11803828033364540827232153 8852871025023405620424115)
            ·
              refine ⟨13279306537535108430636173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8852871025023405620424115 13279306537535108430636173)
              ·
                refine ⟨4979739951575665661488565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13279306537535108430636173 4979739951575665661488565)
                ·
                  refine ⟨466850620460218655764553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4979739951575665661488565 466850620460218655764553)
                  ·
                    rfl

theorem cell23_8182695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 5].length) (baseStart_8182695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182695 prefixEnd_8182695 := by exact prefixLift 8182695
  have htrace : WordTrace (prefixWord ++ tailWord_8182695) baseStart_8182695 baseEnd_8182695 := by
    simpa [prefixWord, tailWord_8182695, baseEnd_8182695] using wordTrace_append hprefix tailTrace_8182695
  have hstable : (prefixWord ++ tailWord_8182695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182695).length < 2 ^ (prefixWord ++ tailWord_8182695).sum := by decide
  have hdescent : baseEnd_8182695 < baseStart_8182695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182708 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_8182708 : Nat := 118140960795 + 8182708 * 2 ^ 59
def prefixEnd_8182708 : Nat := 4983230072969 + 3 ^ 40 * 8182708 * 2
def baseEnd_8182708 : Nat := 1400554086463492117006139

theorem tailTrace_8182708 : CollatzResearch.WordTrace tailWord_8182708 prefixEnd_8182708 1400554086463492117006139 := by
  unfold tailWord_8182708
  simp only [CollatzResearch.WordTrace]
  refine ⟨149223939619726943055614389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198965252826302590740819185 149223939619726943055614389)
  ·
    refine ⟨13989744339349400911463849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149223939619726943055614389 13989744339349400911463849)
    ·
      refine ⟨10492308254512050683597887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13989744339349400911463849 10492308254512050683597887)
      ·
        refine ⟨15738462381768076025396831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10492308254512050683597887 15738462381768076025396831)
        ·
          refine ⟨23607693572652114038095247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15738462381768076025396831 23607693572652114038095247)
          ·
            refine ⟨35411540358978171057142871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23607693572652114038095247 35411540358978171057142871)
            ·
              refine ⟨53117310538467256585714307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35411540358978171057142871 53117310538467256585714307)
              ·
                refine ⟨79675965807700884878571461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53117310538467256585714307 79675965807700884878571461)
                ·
                  refine ⟨14939243588943915914732149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79675965807700884878571461 14939243588943915914732149)
                  ·
                    refine ⟨1400554086463492117006139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14939243588943915914732149 1400554086463492117006139)
                    ·
                      rfl

theorem cell23_8182708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_8182708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182708 prefixEnd_8182708 := by exact prefixLift 8182708
  have htrace : WordTrace (prefixWord ++ tailWord_8182708) baseStart_8182708 baseEnd_8182708 := by
    simpa [prefixWord, tailWord_8182708, baseEnd_8182708] using wordTrace_append hprefix tailTrace_8182708
  have hstable : (prefixWord ++ tailWord_8182708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182708).length < 2 ^ (prefixWord ++ tailWord_8182708).sum := by decide
  have hdescent : baseEnd_8182708 < baseStart_8182708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182711 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 4, 4, 2]
def baseStart_8182711 : Nat := 118140960795 + 8182711 * 2 ^ 59
def prefixEnd_8182711 : Nat := 4983230072969 + 3 ^ 40 * 8182711 * 2
def baseEnd_8182711 : Nat := 4201663799832439839280903

theorem tailTrace_8182711 : CollatzResearch.WordTrace tailWord_8182711 prefixEnd_8182711 4201663799832439839280903 := by
  unfold tailWord_8182711
  simp only [CollatzResearch.WordTrace]
  refine ⟨298447988658443017623587987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198965325772295345082391991 298447988658443017623587987)
  ·
    refine ⟨447671982987664526435381981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298447988658443017623587987 447671982987664526435381981)
    ·
      refine ⟨167876993620374197413268243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447671982987664526435381981 167876993620374197413268243)
      ·
        refine ⟨251815490430561296119902365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167876993620374197413268243 251815490430561296119902365)
        ·
          refine ⟨94430808911460486044963387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251815490430561296119902365 94430808911460486044963387)
          ·
            refine ⟨141646213367190729067445081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94430808911460486044963387 141646213367190729067445081)
            ·
              refine ⟨106234660025393046800583811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141646213367190729067445081 106234660025393046800583811)
              ·
                refine ⟨159351990038089570200875717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106234660025393046800583811 159351990038089570200875717)
                ·
                  refine ⟨29878498132141794412664197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159351990038089570200875717 29878498132141794412664197)
                  ·
                    refine ⟨5602218399776586452374537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29878498132141794412664197 5602218399776586452374537)
                    ·
                      refine ⟨4201663799832439839280903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602218399776586452374537 4201663799832439839280903)
                      ·
                        rfl

theorem cell23_8182711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_8182711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182711 prefixEnd_8182711 := by exact prefixLift 8182711
  have htrace : WordTrace (prefixWord ++ tailWord_8182711) baseStart_8182711 baseEnd_8182711 := by
    simpa [prefixWord, tailWord_8182711, baseEnd_8182711] using wordTrace_append hprefix tailTrace_8182711
  have hstable : (prefixWord ++ tailWord_8182711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182711).length < 2 ^ (prefixWord ++ tailWord_8182711).sum := by decide
  have hdescent : baseEnd_8182711 < baseStart_8182711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182771 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 5, 5, 2]
def baseStart_8182771 : Nat := 118140960795 + 8182771 * 2 ^ 59
def prefixEnd_8182771 : Nat := 4983230072969 + 3 ^ 40 * 8182771 * 2
def baseEnd_8182771 : Nat := 4201694608671709604530627

theorem tailTrace_8182771 : CollatzResearch.WordTrace tailWord_8182771 prefixEnd_8182771 4201694608671709604530627 := by
  unfold tailWord_8182771
  simp only [CollatzResearch.WordTrace]
  refine ⟨298450177038225647870772167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198966784692150431913848111 298450177038225647870772167)
  ·
    refine ⟨447675265557338471806158251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298450177038225647870772167 447675265557338471806158251)
    ·
      refine ⟨671512898336007707709237377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447675265557338471806158251 671512898336007707709237377)
      ·
        refine ⟨503634673752005780781928033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671512898336007707709237377 503634673752005780781928033)
        ·
          refine ⟨377726005314004335586446025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503634673752005780781928033 377726005314004335586446025)
          ·
            refine ⟨283294503985503251689834519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377726005314004335586446025 283294503985503251689834519)
            ·
              refine ⟨424941755978254877534751779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283294503985503251689834519 424941755978254877534751779)
              ·
                refine ⟨637412633967382316302127669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424941755978254877534751779 637412633967382316302127669)
                ·
                  refine ⟨59757434434442092153324469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637412633967382316302127669 59757434434442092153324469)
                  ·
                    refine ⟨5602259478228946139374169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59757434434442092153324469 5602259478228946139374169)
                    ·
                      refine ⟨4201694608671709604530627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602259478228946139374169 4201694608671709604530627)
                      ·
                        rfl

theorem cell23_8182771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5, 2].length) (baseStart_8182771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182771 prefixEnd_8182771 := by exact prefixLift 8182771
  have htrace : WordTrace (prefixWord ++ tailWord_8182771) baseStart_8182771 baseEnd_8182771 := by
    simpa [prefixWord, tailWord_8182771, baseEnd_8182771] using wordTrace_append hprefix tailTrace_8182771
  have hstable : (prefixWord ++ tailWord_8182771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182771).length < 2 ^ (prefixWord ++ tailWord_8182771).sum := by decide
  have hdescent : baseEnd_8182771 < baseStart_8182771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182805 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_8182805 : Nat := 118140960795 + 8182805 * 2 ^ 59
def prefixEnd_8182805 : Nat := 4983230072969 + 3 ^ 40 * 8182805 * 2
def baseEnd_8182805 : Nat := 4201712067013962471505471

theorem tailTrace_8182805 : CollatzResearch.WordTrace tailWord_8182805 prefixEnd_8182805 4201712067013962471505471 := by
  unfold tailWord_8182805
  simp only [CollatzResearch.WordTrace]
  refine ⟨298451417120102471677509869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198967611413401647785006579 298451417120102471677509869)
  ·
    refine ⟨111919281420038426879066201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298451417120102471677509869 111919281420038426879066201)
    ·
      refine ⟨83939461065028820159299651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111919281420038426879066201 83939461065028820159299651)
      ·
        refine ⟨125909191597543230238949477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83939461065028820159299651 125909191597543230238949477)
        ·
          refine ⟨23607973424539355669803027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125909191597543230238949477 23607973424539355669803027)
          ·
            refine ⟨35411960136809033504704541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23607973424539355669803027 35411960136809033504704541)
            ·
              refine ⟨13279485051303387564264203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35411960136809033504704541 13279485051303387564264203)
              ·
                refine ⟨19919227576955081346396305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13279485051303387564264203 19919227576955081346396305)
                ·
                  refine ⟨14939420682716311009797229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19919227576955081346396305 14939420682716311009797229)
                  ·
                    refine ⟨5602282756018616628673961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14939420682716311009797229 5602282756018616628673961)
                    ·
                      refine ⟨4201712067013962471505471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602282756018616628673961 4201712067013962471505471)
                      ·
                        rfl

theorem cell23_8182805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_8182805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182805 prefixEnd_8182805 := by exact prefixLift 8182805
  have htrace : WordTrace (prefixWord ++ tailWord_8182805) baseStart_8182805 baseEnd_8182805 := by
    simpa [prefixWord, tailWord_8182805, baseEnd_8182805] using wordTrace_append hprefix tailTrace_8182805
  have hstable : (prefixWord ++ tailWord_8182805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182805).length < 2 ^ (prefixWord ++ tailWord_8182805).sum := by decide
  have hdescent : baseEnd_8182805 < baseStart_8182805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182815 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 1, 5]
def baseStart_8182815 : Nat := 118140960795 + 8182815 * 2 ^ 59
def prefixEnd_8182815 : Nat := 4983230072969 + 3 ^ 40 * 8182815 * 2
def baseEnd_8182815 : Nat := 1400572400606835810793475

theorem tailTrace_8182815 : CollatzResearch.WordTrace tailWord_8182815 prefixEnd_8182815 1400572400606835810793475 := by
  unfold tailWord_8182815
  simp only [CollatzResearch.WordTrace]
  refine ⟨298451781850066243385373899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198967854566710828923582599 298451781850066243385373899)
  ·
    refine ⟨447677672775099365078060849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298451781850066243385373899 447677672775099365078060849)
    ·
      refine ⟨335758254581324523808545637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447677672775099365078060849 335758254581324523808545637)
      ·
        refine ⟨62954672733998348214102307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335758254581324523808545637 62954672733998348214102307)
        ·
          refine ⟨94432009100997522321153461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62954672733998348214102307 94432009100997522321153461)
          ·
            refine ⟨8853000853218517717608137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94432009100997522321153461 8853000853218517717608137)
            ·
              refine ⟨6639750639913888288206103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8853000853218517717608137 6639750639913888288206103)
              ·
                refine ⟨9959625959870832432309155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639750639913888288206103 9959625959870832432309155)
                ·
                  refine ⟨14939438939806248648463733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9959625959870832432309155 14939438939806248648463733)
                  ·
                    refine ⟨1400572400606835810793475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14939438939806248648463733 1400572400606835810793475)
                    ·
                      rfl

theorem cell23_8182815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 5].length) (baseStart_8182815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182815 prefixEnd_8182815 := by exact prefixLift 8182815
  have htrace : WordTrace (prefixWord ++ tailWord_8182815) baseStart_8182815 baseEnd_8182815 := by
    simpa [prefixWord, tailWord_8182815, baseEnd_8182815] using wordTrace_append hprefix tailTrace_8182815
  have hstable : (prefixWord ++ tailWord_8182815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182815).length < 2 ^ (prefixWord ++ tailWord_8182815).sum := by decide
  have hdescent : baseEnd_8182815 < baseStart_8182815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182821 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_8182821 : Nat := 118140960795 + 8182821 * 2 ^ 59
def prefixEnd_8182821 : Nat := 4983230072969 + 3 ^ 40 * 8182821 * 2
def baseEnd_8182821 : Nat := 4201720282704434408905397

theorem tailTrace_8182821 : CollatzResearch.WordTrace tailWord_8182821 prefixEnd_8182821 4201720282704434408905397 := by
  unfold tailWord_8182821
  simp only [CollatzResearch.WordTrace]
  refine ⟨298452000688044506410092317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198968000458696337606728211 298452000688044506410092317)
  ·
    refine ⟨111919500258016689903784619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298452000688044506410092317 111919500258016689903784619)
    ·
      refine ⟨167879250387025034855676929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111919500258016689903784619 167879250387025034855676929)
      ·
        refine ⟨125909437790268776141757697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167879250387025034855676929 125909437790268776141757697)
        ·
          refine ⟨94432078342701582106318273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125909437790268776141757697 94432078342701582106318273)
          ·
            refine ⟨70824058757026186579738705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94432078342701582106318273 70824058757026186579738705)
            ·
              refine ⟨53118044067769639934804029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70824058757026186579738705 53118044067769639934804029)
              ·
                refine ⟨19919266525413614975551511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53118044067769639934804029 19919266525413614975551511)
                ·
                  refine ⟨29878899788120422463327267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19919266525413614975551511 29878899788120422463327267)
                  ·
                    refine ⟨44818349682180633694990901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29878899788120422463327267 44818349682180633694990901)
                    ·
                      refine ⟨4201720282704434408905397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44818349682180633694990901 4201720282704434408905397)
                      ·
                        rfl

theorem cell23_8182821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_8182821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182821 prefixEnd_8182821 := by exact prefixLift 8182821
  have htrace : WordTrace (prefixWord ++ tailWord_8182821) baseStart_8182821 baseEnd_8182821 := by
    simpa [prefixWord, tailWord_8182821, baseEnd_8182821] using wordTrace_append hprefix tailTrace_8182821
  have hstable : (prefixWord ++ tailWord_8182821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182821).length < 2 ^ (prefixWord ++ tailWord_8182821).sum := by decide
  have hdescent : baseEnd_8182821 < baseStart_8182821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182838 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_8182838 : Nat := 118140960795 + 8182838 * 2 ^ 59
def prefixEnd_8182838 : Nat := 4983230072969 + 3 ^ 40 * 8182838 * 2
def baseEnd_8182838 : Nat := 4201729011875560842392819

theorem tailTrace_8182838 : CollatzResearch.WordTrace tailWord_8182838 prefixEnd_8182838 4201729011875560842392819 := by
  unfold tailWord_8182838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653288795561432394591323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198968413819321945542307445 18653288795561432394591323)
  ·
    refine ⟨27979933193342148591886985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18653288795561432394591323 27979933193342148591886985)
    ·
      refine ⟨20984949895006611443915239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27979933193342148591886985 20984949895006611443915239)
      ·
        refine ⟨31477424842509917165872859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984949895006611443915239 31477424842509917165872859)
        ·
          refine ⟨47216137263764875748809289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31477424842509917165872859 47216137263764875748809289)
          ·
            refine ⟨35412102947823656811606967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47216137263764875748809289 35412102947823656811606967)
            ·
              refine ⟨53118154421735485217410451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35412102947823656811606967 53118154421735485217410451)
              ·
                refine ⟨79677231632603227826115677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53118154421735485217410451 79677231632603227826115677)
                ·
                  refine ⟨29878961862226210434793379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79677231632603227826115677 29878961862226210434793379)
                  ·
                    refine ⟨44818442793339315652190069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29878961862226210434793379 44818442793339315652190069)
                    ·
                      refine ⟨4201729011875560842392819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44818442793339315652190069 4201729011875560842392819)
                      ·
                        rfl

theorem cell23_8182838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_8182838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182838 prefixEnd_8182838 := by exact prefixLift 8182838
  have htrace : WordTrace (prefixWord ++ tailWord_8182838) baseStart_8182838 baseEnd_8182838 := by
    simpa [prefixWord, tailWord_8182838, baseEnd_8182838] using wordTrace_append hprefix tailTrace_8182838
  have hstable : (prefixWord ++ tailWord_8182838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182838).length < 2 ^ (prefixWord ++ tailWord_8182838).sum := by decide
  have hdescent : baseEnd_8182838 < baseStart_8182838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182855 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_8182855 : Nat := 118140960795 + 8182855 * 2 ^ 59
def prefixEnd_8182855 : Nat := 4983230072969 + 3 ^ 40 * 8182855 * 2
def baseEnd_8182855 : Nat := 4201737741046687275880241

theorem tailTrace_8182855 : CollatzResearch.WordTrace tailWord_8182855 prefixEnd_8182855 4201737741046687275880241 := by
  unfold tailWord_8182855
  simp only [CollatzResearch.WordTrace]
  refine ⟨298453240769921330216830019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198968827179947553477886679 298453240769921330216830019)
  ·
    refine ⟨447679861154881995325245029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298453240769921330216830019 447679861154881995325245029)
    ·
      refine ⟨83939973966540374123483443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447679861154881995325245029 83939973966540374123483443)
      ·
        refine ⟨125909960949810561185225165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83939973966540374123483443 125909960949810561185225165)
        ·
          refine ⟨47216235356178960444459437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125909960949810561185225165 47216235356178960444459437)
          ·
            refine ⟨17706088258567110166672289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47216235356178960444459437 17706088258567110166672289)
            ·
              refine ⟨13279566193925332625004217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17706088258567110166672289 13279566193925332625004217)
              ·
                refine ⟨9959674645443999468753163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13279566193925332625004217 9959674645443999468753163)
                ·
                  refine ⟨14939511968165999203129745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9959674645443999468753163 14939511968165999203129745)
                  ·
                    refine ⟨11204633976124499402347309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14939511968165999203129745 11204633976124499402347309)
                    ·
                      refine ⟨4201737741046687275880241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204633976124499402347309 4201737741046687275880241)
                      ·
                        rfl

theorem cell23_8182855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_8182855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182855 prefixEnd_8182855 := by exact prefixLift 8182855
  have htrace : WordTrace (prefixWord ++ tailWord_8182855) baseStart_8182855 baseEnd_8182855 := by
    simpa [prefixWord, tailWord_8182855, baseEnd_8182855] using wordTrace_append hprefix tailTrace_8182855
  have hstable : (prefixWord ++ tailWord_8182855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182855).length < 2 ^ (prefixWord ++ tailWord_8182855).sum := by decide
  have hdescent : baseEnd_8182855 < baseStart_8182855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182868 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_8182868 : Nat := 118140960795 + 8182868 * 2 ^ 59
def prefixEnd_8182868 : Nat := 4983230072969 + 3 ^ 40 * 8182868 * 2
def baseEnd_8182868 : Nat := 4201744416295195725017681

theorem tailTrace_8182868 : CollatzResearch.WordTrace tailWord_8182868 prefixEnd_8182868 4201744416295195725017681 := by
  unfold tailWord_8182868
  simp only [CollatzResearch.WordTrace]
  refine ⟨149226857459437116718526629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198969143279249488958035505 149226857459437116718526629)
  ·
    refine ⟨27980035773644459384723743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149226857459437116718526629 27980035773644459384723743)
    ·
      refine ⟨41970053660466689077085615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27980035773644459384723743 41970053660466689077085615)
      ·
        refine ⟨62955080490700033615628423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41970053660466689077085615 62955080490700033615628423)
        ·
          refine ⟨94432620736050050423442635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62955080490700033615628423 94432620736050050423442635)
          ·
            refine ⟨141648931104075075635163953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94432620736050050423442635 141648931104075075635163953)
            ·
              refine ⟨106236698328056306726372965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141648931104075075635163953 106236698328056306726372965)
              ·
                refine ⟨19919380936510557511194931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106236698328056306726372965 19919380936510557511194931)
                ·
                  refine ⟨29879071404765836266792397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19919380936510557511194931 29879071404765836266792397)
                  ·
                    refine ⟨11204651776787188600047149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29879071404765836266792397 11204651776787188600047149)
                    ·
                      refine ⟨4201744416295195725017681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204651776787188600047149 4201744416295195725017681)
                      ·
                        rfl

theorem cell23_8182868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_8182868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182868 prefixEnd_8182868 := by exact prefixLift 8182868
  have htrace : WordTrace (prefixWord ++ tailWord_8182868) baseStart_8182868 baseEnd_8182868 := by
    simpa [prefixWord, tailWord_8182868, baseEnd_8182868] using wordTrace_append hprefix tailTrace_8182868
  have hstable : (prefixWord ++ tailWord_8182868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182868).length < 2 ^ (prefixWord ++ tailWord_8182868).sum := by decide
  have hdescent : baseEnd_8182868 < baseStart_8182868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182885 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_8182885 : Nat := 118140960795 + 8182885 * 2 ^ 59
def prefixEnd_8182885 : Nat := 4983230072969 + 3 ^ 40 * 8182885 * 2
def baseEnd_8182885 : Nat := 4201753145466322158505103

theorem tailTrace_8182885 : CollatzResearch.WordTrace tailWord_8182885 prefixEnd_8182885 4201753145466322158505103 := by
  unfold tailWord_8182885
  simp only [CollatzResearch.WordTrace]
  refine ⟨298454334959812645340422109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198969556639875096893614739 298454334959812645340422109)
  ·
    refine ⟨111920375609929742002658291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298454334959812645340422109 111920375609929742002658291)
    ·
      refine ⟨167880563414894613003987437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111920375609929742002658291 167880563414894613003987437)
      ·
        refine ⟨62955211280585479876495289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167880563414894613003987437 62955211280585479876495289)
        ·
          refine ⟨47216408460439109907371467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62955211280585479876495289 47216408460439109907371467)
          ·
            refine ⟨70824612690658664861057201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47216408460439109907371467 70824612690658664861057201)
            ·
              refine ⟨53118459517993998645792901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70824612690658664861057201 53118459517993998645792901)
              ·
                refine ⟨9959711159623874746086169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53118459517993998645792901 9959711159623874746086169)
                ·
                  refine ⟨7469783369717906059564627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9959711159623874746086169 7469783369717906059564627)
                  ·
                    refine ⟨11204675054576859089346941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7469783369717906059564627 11204675054576859089346941)
                    ·
                      refine ⟨4201753145466322158505103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204675054576859089346941 4201753145466322158505103)
                      ·
                        rfl

theorem cell23_8182885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_8182885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182885 prefixEnd_8182885 := by exact prefixLift 8182885
  have htrace : WordTrace (prefixWord ++ tailWord_8182885) baseStart_8182885 baseEnd_8182885 := by
    simpa [prefixWord, tailWord_8182885, baseEnd_8182885] using wordTrace_append hprefix tailTrace_8182885
  have hstable : (prefixWord ++ tailWord_8182885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182885).length < 2 ^ (prefixWord ++ tailWord_8182885).sum := by decide
  have hdescent : baseEnd_8182885 < baseStart_8182885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182902 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_8182902 : Nat := 118140960795 + 8182902 * 2 ^ 59
def prefixEnd_8182902 : Nat := 4983230072969 + 3 ^ 40 * 8182902 * 2
def baseEnd_8182902 : Nat := 4201761874637448591992525

theorem tailTrace_8182902 : CollatzResearch.WordTrace tailWord_8182902 prefixEnd_8182902 4201761874637448591992525 := by
  unfold tailWord_8182902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653434687546941077736935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198969970000500704829193973 18653434687546941077736935)
  ·
    refine ⟨27980152031320411616605403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18653434687546941077736935 27980152031320411616605403)
    ·
      refine ⟨41970228046980617424908105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27980152031320411616605403 41970228046980617424908105)
      ·
        refine ⟨31477671035235463068681079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41970228046980617424908105 31477671035235463068681079)
        ·
          refine ⟨47216506552853194603021619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31477671035235463068681079 47216506552853194603021619)
          ·
            refine ⟨70824759829279791904532429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47216506552853194603021619 70824759829279791904532429)
            ·
              refine ⟨26559284935979921964199661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70824759829279791904532429 26559284935979921964199661)
              ·
                refine ⟨9959731850992470736574873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26559284935979921964199661 9959731850992470736574873)
                ·
                  refine ⟨7469798888244353052431155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9959731850992470736574873 7469798888244353052431155)
                  ·
                    refine ⟨11204698332366529578646733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7469798888244353052431155 11204698332366529578646733)
                    ·
                      refine ⟨4201761874637448591992525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204698332366529578646733 4201761874637448591992525)
                      ·
                        rfl

theorem cell23_8182902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_8182902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182902 prefixEnd_8182902 := by exact prefixLift 8182902
  have htrace : WordTrace (prefixWord ++ tailWord_8182902) baseStart_8182902 baseEnd_8182902 := by
    simpa [prefixWord, tailWord_8182902, baseEnd_8182902] using wordTrace_append hprefix tailTrace_8182902
  have hstable : (prefixWord ++ tailWord_8182902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182902).length < 2 ^ (prefixWord ++ tailWord_8182902).sum := by decide
  have hdescent : baseEnd_8182902 < baseStart_8182902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8182971 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_8182971 : Nat := 118140960795 + 8182971 * 2 ^ 59
def prefixEnd_8182971 : Nat := 4983230072969 + 3 ^ 40 * 8182971 * 2
def baseEnd_8182971 : Nat := 4201797304802608822029707

theorem tailTrace_8182971 : CollatzResearch.WordTrace tailWord_8182971 prefixEnd_8182971 4201797304802608822029707 := by
  unfold tailWord_8182971
  simp only [CollatzResearch.WordTrace]
  refine ⟨298457471637501082028052767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198971647758334054685368511 298457471637501082028052767)
  ·
    refine ⟨447686207456251623042079151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298457471637501082028052767 447686207456251623042079151)
    ·
      refine ⟨671529311184377434563118727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447686207456251623042079151 671529311184377434563118727)
      ·
        refine ⟨1007293966776566151844678091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671529311184377434563118727 1007293966776566151844678091)
        ·
          refine ⟨1510940950164849227767017137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007293966776566151844678091 1510940950164849227767017137)
          ·
            refine ⟨1133205712623636920825262853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510940950164849227767017137 1133205712623636920825262853)
            ·
              refine ⟨212476071116931922654736785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1133205712623636920825262853 212476071116931922654736785)
              ·
                refine ⟨159357053337698941991052589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212476071116931922654736785 159357053337698941991052589)
                ·
                  refine ⟨59758895001637103246644721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159357053337698941991052589 59758895001637103246644721)
                  ·
                    refine ⟨44819171251227827434983541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59758895001637103246644721 44819171251227827434983541)
                    ·
                      refine ⟨4201797304802608822029707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44819171251227827434983541 4201797304802608822029707)
                      ·
                        rfl

theorem cell23_8182971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_8182971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8182971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8182971 prefixEnd_8182971 := by exact prefixLift 8182971
  have htrace : WordTrace (prefixWord ++ tailWord_8182971) baseStart_8182971 baseEnd_8182971 := by
    simpa [prefixWord, tailWord_8182971, baseEnd_8182971] using wordTrace_append hprefix tailTrace_8182971
  have hstable : (prefixWord ++ tailWord_8182971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8182971).length < 2 ^ (prefixWord ++ tailWord_8182971).sum := by decide
  have hdescent : baseEnd_8182971 < baseStart_8182971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8182971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183116 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 1, 1, 3]
def baseStart_8183116 : Nat := 118140960795 + 8183116 * 2 ^ 59
def prefixEnd_8183116 : Nat := 4983230072969 + 3 ^ 40 * 8183116 * 2
def baseEnd_8183116 : Nat := 4201871759497510754716541

theorem tailTrace_8183116 : CollatzResearch.WordTrace tailWord_8183116 prefixEnd_8183116 4201871759497510754716541 := by
  unfold tailWord_8183116
  simp only [CollatzResearch.WordTrace]
  refine ⟨149231380110987885896040601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198975173481317181194720801 149231380110987885896040601)
  ·
    refine ⟨111923535083240914422030451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149231380110987885896040601 111923535083240914422030451)
    ·
      refine ⟨167885302624861371633045677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111923535083240914422030451 167885302624861371633045677)
      ·
        refine ⟨62956988484323014362392129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167885302624861371633045677 62956988484323014362392129)
        ·
          refine ⟨47217741363242260771794097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62956988484323014362392129 47217741363242260771794097)
          ·
            refine ⟨35413306022431695578845573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47217741363242260771794097 35413306022431695578845573)
            ·
              refine ⟨6639994879205942921033545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35413306022431695578845573 6639994879205942921033545)
              ·
                refine ⟨4979996159404457190775159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6639994879205942921033545 4979996159404457190775159)
                ·
                  refine ⟨7469994239106685786162739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979996159404457190775159 7469994239106685786162739)
                  ·
                    refine ⟨11204991358660028679244109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7469994239106685786162739 11204991358660028679244109)
                    ·
                      refine ⟨4201871759497510754716541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11204991358660028679244109 4201871759497510754716541)
                      ·
                        rfl

theorem cell23_8183116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_8183116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183116 prefixEnd_8183116 := by exact prefixLift 8183116
  have htrace : WordTrace (prefixWord ++ tailWord_8183116) baseStart_8183116 baseEnd_8183116 := by
    simpa [prefixWord, tailWord_8183116, baseEnd_8183116] using wordTrace_append hprefix tailTrace_8183116
  have hstable : (prefixWord ++ tailWord_8183116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183116).length < 2 ^ (prefixWord ++ tailWord_8183116).sum := by decide
  have hdescent : baseEnd_8183116 < baseStart_8183116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183133 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_8183133 : Nat := 118140960795 + 8183133 * 2 ^ 59
def prefixEnd_8183133 : Nat := 4983230072969 + 3 ^ 40 * 8183133 * 2
def baseEnd_8183133 : Nat := 4201880488668637188203963

theorem tailTrace_8183133 : CollatzResearch.WordTrace tailWord_8183133 prefixEnd_8183133 4201880488668637188203963 := by
  unfold tailWord_8183133
  simp only [CollatzResearch.WordTrace]
  refine ⟨298463380262914183695450053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198975586841942789130300035 298463380262914183695450053)
  ·
    refine ⟨55961883799296409442896885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298463380262914183695450053 55961883799296409442896885)
    ·
      refine ⟨5246426606184038385271583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55961883799296409442896885 5246426606184038385271583)
      ·
        refine ⟨7869639909276057577907375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246426606184038385271583 7869639909276057577907375)
        ·
          refine ⟨11804459863914086366861063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869639909276057577907375 11804459863914086366861063)
          ·
            refine ⟨17706689795871129550291595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804459863914086366861063 17706689795871129550291595)
            ·
              refine ⟨26560034693806694325437393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17706689795871129550291595 26560034693806694325437393)
              ·
                refine ⟨19920026020355020744078045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26560034693806694325437393 19920026020355020744078045)
                ·
                  refine ⟨7470009757633132779029267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19920026020355020744078045 7470009757633132779029267)
                  ·
                    refine ⟨11205014636449699168543901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7470009757633132779029267 11205014636449699168543901)
                    ·
                      refine ⟨4201880488668637188203963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11205014636449699168543901 4201880488668637188203963)
                      ·
                        rfl

theorem cell23_8183133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_8183133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183133 prefixEnd_8183133 := by exact prefixLift 8183133
  have htrace : WordTrace (prefixWord ++ tailWord_8183133) baseStart_8183133 baseEnd_8183133 := by
    simpa [prefixWord, tailWord_8183133, baseEnd_8183133] using wordTrace_append hprefix tailTrace_8183133
  have hstable : (prefixWord ++ tailWord_8183133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183133).length < 2 ^ (prefixWord ++ tailWord_8183133).sum := by decide
  have hdescent : baseEnd_8183133 < baseStart_8183133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183139 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 3, 2, 2]
def baseStart_8183139 : Nat := 118140960795 + 8183139 * 2 ^ 59
def prefixEnd_8183139 : Nat := 4983230072969 + 3 ^ 40 * 8183139 * 2
def baseEnd_8183139 : Nat := 4201883569552564164728935

theorem tailTrace_8183139 : CollatzResearch.WordTrace tailWord_8183139 prefixEnd_8183139 4201883569552564164728935 := by
  unfold tailWord_8183139
  simp only [CollatzResearch.WordTrace]
  refine ⟨298463599100892446720168471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198975732733928297813445647 298463599100892446720168471)
  ·
    refine ⟨447695398651338670080252707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298463599100892446720168471 447695398651338670080252707)
    ·
      refine ⟨671543097977008005120379061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447695398651338670080252707 671543097977008005120379061)
      ·
        refine ⟨62957165435344500480035537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 671543097977008005120379061 62957165435344500480035537)
        ·
          refine ⟨47217874076508375360026653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62957165435344500480035537 47217874076508375360026653)
          ·
            refine ⟨17706702778690640760009995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47217874076508375360026653 17706702778690640760009995)
            ·
              refine ⟨26560054168035961140014993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17706702778690640760009995 26560054168035961140014993)
              ·
                refine ⟨19920040626026970855011245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26560054168035961140014993 19920040626026970855011245)
                ·
                  refine ⟨7470015234760114070629217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19920040626026970855011245 7470015234760114070629217)
                  ·
                    refine ⟨5602511426070085552971913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470015234760114070629217 5602511426070085552971913)
                    ·
                      refine ⟨4201883569552564164728935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602511426070085552971913 4201883569552564164728935)
                      ·
                        rfl

theorem cell23_8183139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_8183139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183139 prefixEnd_8183139 := by exact prefixLift 8183139
  have htrace : WordTrace (prefixWord ++ tailWord_8183139) baseStart_8183139 baseEnd_8183139 := by
    simpa [prefixWord, tailWord_8183139, baseEnd_8183139] using wordTrace_append hprefix tailTrace_8183139
  have hstable : (prefixWord ++ tailWord_8183139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183139).length < 2 ^ (prefixWord ++ tailWord_8183139).sum := by decide
  have hdescent : baseEnd_8183139 < baseStart_8183139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183166 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_8183166 : Nat := 118140960795 + 8183166 * 2 ^ 59
def prefixEnd_8183166 : Nat := 4983230072969 + 3 ^ 40 * 8183166 * 2
def baseEnd_8183166 : Nat := 1400632477843411853030437

theorem tailTrace_8183166 : CollatzResearch.WordTrace tailWord_8183166 prefixEnd_8183166 1400632477843411853030437 := by
  unfold tailWord_8183166
  simp only [CollatzResearch.WordTrace]
  refine ⟨37308072983974328791425169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198976389247863086887600901 37308072983974328791425169)
  ·
    refine ⟨27981054737980746593568877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37308072983974328791425169 27981054737980746593568877)
    ·
      refine ⟨10492895526742779972588329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27981054737980746593568877 10492895526742779972588329)
      ·
        refine ⟨7869671645057084979441247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10492895526742779972588329 7869671645057084979441247)
        ·
          refine ⟨11804507467585627469161871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869671645057084979441247 11804507467585627469161871)
          ·
            refine ⟨17706761201378441203742807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804507467585627469161871 17706761201378441203742807)
            ·
              refine ⟨26560141802067661805614211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17706761201378441203742807 26560141802067661805614211)
              ·
                refine ⟨39840212703101492708421317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26560141802067661805614211 39840212703101492708421317)
                ·
                  refine ⟨7470039881831529882828997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39840212703101492708421317 7470039881831529882828997)
                  ·
                    refine ⟨1400632477843411853030437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470039881831529882828997 1400632477843411853030437)
                    ·
                      rfl

theorem cell23_8183166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_8183166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183166 prefixEnd_8183166 := by exact prefixLift 8183166
  have htrace : WordTrace (prefixWord ++ tailWord_8183166) baseStart_8183166 baseEnd_8183166 := by
    simpa [prefixWord, tailWord_8183166, baseEnd_8183166] using wordTrace_append hprefix tailTrace_8183166
  have hstable : (prefixWord ++ tailWord_8183166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183166).length < 2 ^ (prefixWord ++ tailWord_8183166).sum := by decide
  have hdescent : baseEnd_8183166 < baseStart_8183166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183186 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8183186 : Nat := 118140960795 + 8183186 * 2 ^ 59
def prefixEnd_8183186 : Nat := 4983230072969 + 3 ^ 40 * 8183186 * 2
def baseEnd_8183186 : Nat := 4201907703143325480841219

theorem tailTrace_8183186 : CollatzResearch.WordTrace tailWord_8183186 prefixEnd_8183186 4201907703143325480841219 := by
  unfold tailWord_8183186
  simp only [CollatzResearch.WordTrace]
  refine ⟨74616328332930543436782353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198976875554481449164752941 74616328332930543436782353)
  ·
    refine ⟨55962246249697907577586765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74616328332930543436782353 55962246249697907577586765)
    ·
      refine ⟨20985842343636715341595037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55962246249697907577586765 20985842343636715341595037)
      ·
        refine ⟨7869690878863768253098139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20985842343636715341595037 7869690878863768253098139)
        ·
          refine ⟨11804536318295652379647209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869690878863768253098139 11804536318295652379647209)
          ·
            refine ⟨8853402238721739284735407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11804536318295652379647209 8853402238721739284735407)
            ·
              refine ⟨13280103358082608927103111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8853402238721739284735407 13280103358082608927103111)
              ·
                refine ⟨19920155037123913390654667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13280103358082608927103111 19920155037123913390654667)
                ·
                  refine ⟨29880232555685870085982001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19920155037123913390654667 29880232555685870085982001)
                  ·
                    refine ⟨22410174416764402564486501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29880232555685870085982001 22410174416764402564486501)
                    ·
                      refine ⟨4201907703143325480841219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22410174416764402564486501 4201907703143325480841219)
                      ·
                        rfl

theorem cell23_8183186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8183186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183186 prefixEnd_8183186 := by exact prefixLift 8183186
  have htrace : WordTrace (prefixWord ++ tailWord_8183186) baseStart_8183186 baseEnd_8183186 := by
    simpa [prefixWord, tailWord_8183186, baseEnd_8183186] using wordTrace_append hprefix tailTrace_8183186
  have hstable : (prefixWord ++ tailWord_8183186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183186).length < 2 ^ (prefixWord ++ tailWord_8183186).sum := by decide
  have hdescent : baseEnd_8183186 < baseStart_8183186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183196 : List Nat := [2, 2, 3, 4, 2, 1, 2, 7]
def baseStart_8183196 : Nat := 118140960795 + 8183196 * 2 ^ 59
def prefixEnd_8183196 : Nat := 4983230072969 + 3 ^ 40 * 8183196 * 2
def baseEnd_8183196 : Nat := 155626401405550757100599

theorem tailTrace_8183196 : CollatzResearch.WordTrace tailWord_8183196 prefixEnd_8183196 155626401405550757100599 := by
  unfold tailWord_8183196
  simp only [CollatzResearch.WordTrace]
  refine ⟨149232839030842972727496721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198977118707790630303328961 149232839030842972727496721)
  ·
    refine ⟨111924629273132229545622541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149232839030842972727496721 111924629273132229545622541)
    ·
      refine ⟨41971735977424586079608453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111924629273132229545622541 41971735977424586079608453)
      ·
        refine ⟨7869700495767109889926585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41971735977424586079608453 7869700495767109889926585)
        ·
          refine ⟨5902275371825332417444939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7869700495767109889926585 5902275371825332417444939)
          ·
            refine ⟨8853413057737998626167409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902275371825332417444939 8853413057737998626167409)
            ·
              refine ⟨6640059793303498969625557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8853413057737998626167409 6640059793303498969625557)
              ·
                refine ⟨155626401405550757100599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6640059793303498969625557 155626401405550757100599)
                ·
                  rfl

theorem cell23_8183196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 7].length) (baseStart_8183196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183196 prefixEnd_8183196 := by exact prefixLift 8183196
  have htrace : WordTrace (prefixWord ++ tailWord_8183196) baseStart_8183196 baseEnd_8183196 := by
    simpa [prefixWord, tailWord_8183196, baseEnd_8183196] using wordTrace_append hprefix tailTrace_8183196
  have hstable : (prefixWord ++ tailWord_8183196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183196).length < 2 ^ (prefixWord ++ tailWord_8183196).sum := by decide
  have hdescent : baseEnd_8183196 < baseStart_8183196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183199 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 1, 3, 2]
def baseStart_8183199 : Nat := 118140960795 + 8183199 * 2 ^ 59
def prefixEnd_8183199 : Nat := 4983230072969 + 3 ^ 40 * 8183199 * 2
def baseEnd_8183199 : Nat := 4201914378391833929978659

theorem tailTrace_8183199 : CollatzResearch.WordTrace tailWord_8183199 prefixEnd_8183199 4201914378391833929978659 := by
  unfold tailWord_8183199
  simp only [CollatzResearch.WordTrace]
  refine ⟨298465787480675076967352651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198977191653783384644901767 298465787480675076967352651)
  ·
    refine ⟨447698681221012615451028977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298465787480675076967352651 447698681221012615451028977)
    ·
      refine ⟨335774010915759461588271733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447698681221012615451028977 335774010915759461588271733)
      ·
        refine ⟨31478813523352449523900475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335774010915759461588271733 31478813523352449523900475)
        ·
          refine ⟨47218220285028674285850713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31478813523352449523900475 47218220285028674285850713)
          ·
            refine ⟨35413665213771505714388035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47218220285028674285850713 35413665213771505714388035)
            ·
              refine ⟨53120497820657258571582053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35413665213771505714388035 53120497820657258571582053)
              ·
                refine ⟨9960093341373235982171635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53120497820657258571582053 9960093341373235982171635)
                ·
                  refine ⟨14940140012059853973257453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9960093341373235982171635 14940140012059853973257453)
                  ·
                    refine ⟨5602552504522445239971545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14940140012059853973257453 5602552504522445239971545)
                    ·
                      refine ⟨4201914378391833929978659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602552504522445239971545 4201914378391833929978659)
                      ·
                        rfl

theorem cell23_8183199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_8183199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183199 prefixEnd_8183199 := by exact prefixLift 8183199
  have htrace : WordTrace (prefixWord ++ tailWord_8183199) baseStart_8183199 baseEnd_8183199 := by
    simpa [prefixWord, tailWord_8183199, baseEnd_8183199] using wordTrace_append hprefix tailTrace_8183199
  have hstable : (prefixWord ++ tailWord_8183199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183199).length < 2 ^ (prefixWord ++ tailWord_8183199).sum := by decide
  have hdescent : baseEnd_8183199 < baseStart_8183199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183212 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 1, 4, 2]
def baseStart_8183212 : Nat := 118140960795 + 8183212 * 2 ^ 59
def prefixEnd_8183212 : Nat := 4983230072969 + 3 ^ 40 * 8183212 * 2
def baseEnd_8183212 : Nat := 4201921053640342379116099

theorem tailTrace_8183212 : CollatzResearch.WordTrace tailWord_8183212 prefixEnd_8183212 4201921053640342379116099 := by
  unfold tailWord_8183212
  simp only [CollatzResearch.WordTrace]
  refine ⟨149233130814813990093787945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198977507753085320125050593 149233130814813990093787945)
  ·
    refine ⟨111924848111110492570340959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149233130814813990093787945 111924848111110492570340959)
    ·
      refine ⟨167887272166665738855511439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111924848111110492570340959 167887272166665738855511439)
      ·
        refine ⟨251830908249998608283267159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167887272166665738855511439 251830908249998608283267159)
        ·
          refine ⟨377746362374997912424900739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251830908249998608283267159 377746362374997912424900739)
          ·
            refine ⟨566619543562496868637351109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377746362374997912424900739 566619543562496868637351109)
            ·
              refine ⟨106241164417968162869503333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 566619543562496868637351109 106241164417968162869503333)
              ·
                refine ⟨19920218328369030538031875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106241164417968162869503333 19920218328369030538031875)
                ·
                  refine ⟨29880327492553545807047813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19920218328369030538031875 29880327492553545807047813)
                  ·
                    refine ⟨5602561404853789838821465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29880327492553545807047813 5602561404853789838821465)
                    ·
                      refine ⟨4201921053640342379116099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602561404853789838821465 4201921053640342379116099)
                      ·
                        rfl

theorem cell23_8183212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_8183212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183212 prefixEnd_8183212 := by exact prefixLift 8183212
  have htrace : WordTrace (prefixWord ++ tailWord_8183212) baseStart_8183212 baseEnd_8183212 := by
    simpa [prefixWord, tailWord_8183212, baseEnd_8183212] using wordTrace_append hprefix tailTrace_8183212
  have hstable : (prefixWord ++ tailWord_8183212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183212).length < 2 ^ (prefixWord ++ tailWord_8183212).sum := by decide
  have hdescent : baseEnd_8183212 < baseStart_8183212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183229 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_8183229 : Nat := 118140960795 + 8183229 * 2 ^ 59
def prefixEnd_8183229 : Nat := 4983230072969 + 3 ^ 40 * 8183229 * 2
def baseEnd_8183229 : Nat := 4201929782811468812603521

theorem tailTrace_8183229 : CollatzResearch.WordTrace tailWord_8183229 prefixEnd_8183229 4201929782811468812603521 := by
  unfold tailWord_8183229
  simp only [CollatzResearch.WordTrace]
  refine ⟨298466881670566392090944741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198977921113710928060629827 298466881670566392090944741)
  ·
    refine ⟨55962540313231198517052139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298466881670566392090944741 55962540313231198517052139)
    ·
      refine ⟨83943810469846797775578209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55962540313231198517052139 83943810469846797775578209)
      ·
        refine ⟨62957857852385098331683657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83943810469846797775578209 62957857852385098331683657)
        ·
          refine ⟨47218393389288823748762743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62957857852385098331683657 47218393389288823748762743)
          ·
            refine ⟨70827590083933235623144115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47218393389288823748762743 70827590083933235623144115)
            ·
              refine ⟨106241385125899853434716173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70827590083933235623144115 106241385125899853434716173)
              ·
                refine ⟨39840519422212445038018565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106241385125899853434716173 39840519422212445038018565)
                ·
                  refine ⟨7470097391664833444628481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39840519422212445038018565 7470097391664833444628481)
                  ·
                    refine ⟨5602573043748625083471361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470097391664833444628481 5602573043748625083471361)
                    ·
                      refine ⟨4201929782811468812603521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602573043748625083471361 4201929782811468812603521)
                      ·
                        rfl

theorem cell23_8183229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_8183229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183229 prefixEnd_8183229 := by exact prefixLift 8183229
  have htrace : WordTrace (prefixWord ++ tailWord_8183229) baseStart_8183229 baseEnd_8183229 := by
    simpa [prefixWord, tailWord_8183229, baseEnd_8183229] using wordTrace_append hprefix tailTrace_8183229
  have hstable : (prefixWord ++ tailWord_8183229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183229).length < 2 ^ (prefixWord ++ tailWord_8183229).sum := by decide
  have hdescent : baseEnd_8183229 < baseStart_8183229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183234 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8183234 : Nat := 118140960795 + 8183234 * 2 ^ 59
def prefixEnd_8183234 : Nat := 4983230072969 + 3 ^ 40 * 8183234 * 2
def baseEnd_8183234 : Nat := 1400644116738247097680333

theorem tailTrace_8183234 : CollatzResearch.WordTrace tailWord_8183234 prefixEnd_8183234 1400644116738247097680333 := by
  unfold tailWord_8183234
  simp only [CollatzResearch.WordTrace]
  refine ⟨74616766008887069486219189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198978042690365518629917837 74616766008887069486219189)
  ·
    refine ⟨6995321813333162764333049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74616766008887069486219189 6995321813333162764333049)
    ·
      refine ⟨5246491359999872073249787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6995321813333162764333049 5246491359999872073249787)
      ·
        refine ⟨7869737039999808109874681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246491359999872073249787 7869737039999808109874681)
        ·
          refine ⟨5902302779999856082406011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7869737039999808109874681 5902302779999856082406011)
          ·
            refine ⟨8853454169999784123609017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902302779999856082406011 8853454169999784123609017)
            ·
              refine ⟨6640090627499838092706763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8853454169999784123609017 6640090627499838092706763)
              ·
                refine ⟨9960135941249757139060145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640090627499838092706763 9960135941249757139060145)
                ·
                  refine ⟨7470101955937317854295109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960135941249757139060145 7470101955937317854295109)
                  ·
                    refine ⟨1400644116738247097680333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470101955937317854295109 1400644116738247097680333)
                    ·
                      rfl

theorem cell23_8183234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8183234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183234 prefixEnd_8183234 := by exact prefixLift 8183234
  have htrace : WordTrace (prefixWord ++ tailWord_8183234) baseStart_8183234 baseEnd_8183234 := by
    simpa [prefixWord, tailWord_8183234, baseEnd_8183234] using wordTrace_append hprefix tailTrace_8183234
  have hstable : (prefixWord ++ tailWord_8183234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183234).length < 2 ^ (prefixWord ++ tailWord_8183234).sum := by decide
  have hdescent : baseEnd_8183234 < baseStart_8183234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183235 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 7]
def baseStart_8183235 : Nat := 118140960795 + 8183235 * 2 ^ 59
def prefixEnd_8183235 : Nat := 4983230072969 + 3 ^ 40 * 8183235 * 2
def baseEnd_8183235 : Nat := 466881429299488421014277

theorem tailTrace_8183235 : CollatzResearch.WordTrace tailWord_8183235 prefixEnd_8183235 466881429299488421014277 := by
  unfold tailWord_8183235
  simp only [CollatzResearch.WordTrace]
  refine ⟨298467100508544655115663159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198978067005696436743775439 298467100508544655115663159)
  ·
    refine ⟨447700650762816982673494739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298467100508544655115663159 447700650762816982673494739)
    ·
      refine ⟨671550976144225474010242109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447700650762816982673494739 671550976144225474010242109)
      ·
        refine ⟨251831616054084552753840791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671550976144225474010242109 251831616054084552753840791)
        ·
          refine ⟨377747424081126829130761187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251831616054084552753840791 377747424081126829130761187)
          ·
            refine ⟨566621136121690243696141781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377747424081126829130761187 566621136121690243696141781)
            ·
              refine ⟨13280182877852115086628323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 566621136121690243696141781 13280182877852115086628323)
              ·
                refine ⟨19920274316778172629942485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13280182877852115086628323 19920274316778172629942485)
                ·
                  refine ⟨466881429299488421014277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19920274316778172629942485 466881429299488421014277)
                  ·
                    rfl

theorem cell23_8183235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 7].length) (baseStart_8183235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183235 prefixEnd_8183235 := by exact prefixLift 8183235
  have htrace : WordTrace (prefixWord ++ tailWord_8183235) baseStart_8183235 baseEnd_8183235 := by
    simpa [prefixWord, tailWord_8183235, baseEnd_8183235] using wordTrace_append hprefix tailTrace_8183235
  have hstable : (prefixWord ++ tailWord_8183235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183235).length < 2 ^ (prefixWord ++ tailWord_8183235).sum := by decide
  have hdescent : baseEnd_8183235 < baseStart_8183235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183286 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_8183286 : Nat := 118140960795 + 8183286 * 2 ^ 59
def prefixEnd_8183286 : Nat := 4983230072969 + 3 ^ 40 * 8183286 * 2
def baseEnd_8183286 : Nat := 466884339023197232176751

theorem tailTrace_8183286 : CollatzResearch.WordTrace tailWord_8183286 prefixEnd_8183286 466884339023197232176751 := by
  unfold tailWord_8183286
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654310039459993176610607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198979307087573260550513141 18654310039459993176610607)
  ·
    refine ⟨27981465059189989764915911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18654310039459993176610607 27981465059189989764915911)
    ·
      refine ⟨41972197588784984647373867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27981465059189989764915911 41972197588784984647373867)
      ·
        refine ⟨62958296383177476971060801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41972197588784984647373867 62958296383177476971060801)
        ·
          refine ⟨47218722287383107728295601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62958296383177476971060801 47218722287383107728295601)
          ·
            refine ⟨35414041715537330796221701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47218722287383107728295601 35414041715537330796221701)
            ·
              refine ⟨6640132821663249524291569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35414041715537330796221701 6640132821663249524291569)
              ·
                refine ⟨4980099616247437143218677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640132821663249524291569 4980099616247437143218677)
                ·
                  refine ⟨466884339023197232176751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980099616247437143218677 466884339023197232176751)
                  ·
                    rfl

theorem cell23_8183286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_8183286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183286 prefixEnd_8183286 := by exact prefixLift 8183286
  have htrace : WordTrace (prefixWord ++ tailWord_8183286) baseStart_8183286 baseEnd_8183286 := by
    simpa [prefixWord, tailWord_8183286, baseEnd_8183286] using wordTrace_append hprefix tailTrace_8183286
  have hstable : (prefixWord ++ tailWord_8183286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183286).length < 2 ^ (prefixWord ++ tailWord_8183286).sum := by decide
  have hdescent : baseEnd_8183286 < baseStart_8183286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183359 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 6]
def baseStart_8183359 : Nat := 118140960795 + 8183359 * 2 ^ 59
def prefixEnd_8183359 : Nat := 4983230072969 + 3 ^ 40 * 8183359 * 2
def baseEnd_8183359 : Nat := 466888503921839255997547

theorem tailTrace_8183359 : CollatzResearch.WordTrace tailWord_8183359 prefixEnd_8183359 466888503921839255997547 := by
  unfold tailWord_8183359
  simp only [CollatzResearch.WordTrace]
  refine ⟨298471623160095424293177131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198981082106730282862118087 298471623160095424293177131)
  ·
    refine ⟨447707434740143136439765697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298471623160095424293177131 447707434740143136439765697)
    ·
      refine ⟨335780576055107352329824273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447707434740143136439765697 335780576055107352329824273)
      ·
        refine ⟨251835432041330514247368205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335780576055107352329824273 251835432041330514247368205)
        ·
          refine ⟨94438287015498942842763077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251835432041330514247368205 94438287015498942842763077)
          ·
            refine ⟨17707178815406051783018077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94438287015498942842763077 17707178815406051783018077)
            ·
              refine ⟨6640192055777269418631779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17707178815406051783018077 6640192055777269418631779)
              ·
                refine ⟨9960288083665904127947669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640192055777269418631779 9960288083665904127947669)
                ·
                  refine ⟨466888503921839255997547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9960288083665904127947669 466888503921839255997547)
                  ·
                    rfl

theorem cell23_8183359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 6].length) (baseStart_8183359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183359 prefixEnd_8183359 := by exact prefixLift 8183359
  have htrace : WordTrace (prefixWord ++ tailWord_8183359) baseStart_8183359 baseEnd_8183359 := by
    simpa [prefixWord, tailWord_8183359, baseEnd_8183359] using wordTrace_append hprefix tailTrace_8183359
  have hstable : (prefixWord ++ tailWord_8183359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183359).length < 2 ^ (prefixWord ++ tailWord_8183359).sum := by decide
  have hdescent : baseEnd_8183359 < baseStart_8183359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183392 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_8183392 : Nat := 118140960795 + 8183392 * 2 ^ 59
def prefixEnd_8183392 : Nat := 4983230072969 + 3 ^ 40 * 8183392 * 2
def baseEnd_8183392 : Nat := 4202013480158151674865271

theorem tailTrace_8183392 : CollatzResearch.WordTrace tailWord_8183392 prefixEnd_8183392 4202013480158151674865271 := by
  unfold tailWord_8183392
  simp only [CollatzResearch.WordTrace]
  refine ⟨149236413384487935464564215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198981884512650580619418953 149236413384487935464564215)
  ·
    refine ⟨223854620076731903196846323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149236413384487935464564215 223854620076731903196846323)
    ·
      refine ⟨335781930115097854795269485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223854620076731903196846323 335781930115097854795269485)
      ·
        refine ⟨125918223793161695548226057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335781930115097854795269485 125918223793161695548226057)
        ·
          refine ⟨94438667844871271661169543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125918223793161695548226057 94438667844871271661169543)
          ·
            refine ⟨141658001767306907491754315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94438667844871271661169543 141658001767306907491754315)
            ·
              refine ⟨212487002650960361237631473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141658001767306907491754315 212487002650960361237631473)
              ·
                refine ⟨159365251988220270928223605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212487002650960361237631473 159365251988220270928223605)
                ·
                  refine ⟨14940492373895650399520963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159365251988220270928223605 14940492373895650399520963)
                  ·
                    refine ⟨22410738560843475599281445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14940492373895650399520963 22410738560843475599281445)
                    ·
                      refine ⟨4202013480158151674865271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22410738560843475599281445 4202013480158151674865271)
                      ·
                        rfl

theorem cell23_8183392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_8183392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183392 prefixEnd_8183392 := by exact prefixLift 8183392
  have htrace : WordTrace (prefixWord ++ tailWord_8183392) baseStart_8183392 baseEnd_8183392 := by
    simpa [prefixWord, tailWord_8183392, baseEnd_8183392] using wordTrace_append hprefix tailTrace_8183392
  have hstable : (prefixWord ++ tailWord_8183392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183392).length < 2 ^ (prefixWord ++ tailWord_8183392).sum := by decide
  have hdescent : baseEnd_8183392 < baseStart_8183392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183396 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_8183396 : Nat := 118140960795 + 8183396 * 2 ^ 59
def prefixEnd_8183396 : Nat := 4983230072969 + 3 ^ 40 * 8183396 * 2
def baseEnd_8183396 : Nat := 4202015534080769659215253

theorem tailTrace_8183396 : CollatzResearch.WordTrace tailWord_8183396 prefixEnd_8183396 4202015534080769659215253 := by
  unfold tailWord_8183396
  simp only [CollatzResearch.WordTrace]
  refine ⟨149236486330480689806137021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198981981773974253074849361 149236486330480689806137021)
  ·
    refine ⟨55963682373930258677301383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149236486330480689806137021 55963682373930258677301383)
    ·
      refine ⟨83945523560895388015952075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55963682373930258677301383 83945523560895388015952075)
      ·
        refine ⟨125918285341343082023928113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83945523560895388015952075 125918285341343082023928113)
        ·
          refine ⟨94438714006007311517946085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125918285341343082023928113 94438714006007311517946085)
          ·
            refine ⟨17707258876126370909614891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94438714006007311517946085 17707258876126370909614891)
            ·
              refine ⟨26560888314189556364422337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17707258876126370909614891 26560888314189556364422337)
              ·
                refine ⟨19920666235642167273316753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26560888314189556364422337 19920666235642167273316753)
                ·
                  refine ⟨14940499676731625454987565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19920666235642167273316753 14940499676731625454987565)
                  ·
                    refine ⟨5602687378774359545620337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14940499676731625454987565 5602687378774359545620337)
                    ·
                      refine ⟨4202015534080769659215253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602687378774359545620337 4202015534080769659215253)
                      ·
                        rfl

theorem cell23_8183396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_8183396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183396 prefixEnd_8183396 := by exact prefixLift 8183396
  have htrace : WordTrace (prefixWord ++ tailWord_8183396) baseStart_8183396 baseEnd_8183396 := by
    simpa [prefixWord, tailWord_8183396, baseEnd_8183396] using wordTrace_append hprefix tailTrace_8183396
  have hstable : (prefixWord ++ tailWord_8183396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183396).length < 2 ^ (prefixWord ++ tailWord_8183396).sum := by decide
  have hdescent : baseEnd_8183396 < baseStart_8183396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183419 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 2, 4]
def baseStart_8183419 : Nat := 118140960795 + 8183419 * 2 ^ 59
def prefixEnd_8183419 : Nat := 4983230072969 + 3 ^ 40 * 8183419 * 2
def baseEnd_8183419 : Nat := 1400675781378607689742549

theorem tailTrace_8183419 : CollatzResearch.WordTrace tailWord_8183419 prefixEnd_8183419 1400675781378607689742549 := by
  unfold tailWord_8183419
  simp only [CollatzResearch.WordTrace]
  refine ⟨298473811539878054540361311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198982541026585369693574207 298473811539878054540361311)
  ·
    refine ⟨447710717309817081810541967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298473811539878054540361311 447710717309817081810541967)
    ·
      refine ⟨671566075964725622715812951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447710717309817081810541967 671566075964725622715812951)
      ·
        refine ⟨1007349113947088434073719427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671566075964725622715812951 1007349113947088434073719427)
        ·
          refine ⟨1511023670920632651110579141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007349113947088434073719427 1511023670920632651110579141)
          ·
            refine ⟨283316938297618622083233589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1511023670920632651110579141 283316938297618622083233589)
            ·
              refine ⟨26560962965401745820303149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283316938297618622083233589 26560962965401745820303149)
              ·
                refine ⟨9960361112025654682613681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26560962965401745820303149 9960361112025654682613681)
                ·
                  refine ⟨7470270834019241011960261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960361112025654682613681 7470270834019241011960261)
                  ·
                    refine ⟨1400675781378607689742549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470270834019241011960261 1400675781378607689742549)
                    ·
                      rfl

theorem cell23_8183419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 4].length) (baseStart_8183419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183419 prefixEnd_8183419 := by exact prefixLift 8183419
  have htrace : WordTrace (prefixWord ++ tailWord_8183419) baseStart_8183419 baseEnd_8183419 := by
    simpa [prefixWord, tailWord_8183419, baseEnd_8183419] using wordTrace_append hprefix tailTrace_8183419
  have hstable : (prefixWord ++ tailWord_8183419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183419).length < 2 ^ (prefixWord ++ tailWord_8183419).sum := by decide
  have hdescent : baseEnd_8183419 < baseStart_8183419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183429 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_8183429 : Nat := 118140960795 + 8183429 * 2 ^ 59
def prefixEnd_8183429 : Nat := 4983230072969 + 3 ^ 40 * 8183429 * 2
def baseEnd_8183429 : Nat := 4202032478942368030102601

theorem tailTrace_8183429 : CollatzResearch.WordTrace tailWord_8183429 prefixEnd_8183429 4202032478942368030102601 := by
  unfold tailWord_8183429
  simp only [CollatzResearch.WordTrace]
  refine ⟨298474176269841826248225341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198982784179894550832150227 298474176269841826248225341)
  ·
    refine ⟨111927816101190684843084503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298474176269841826248225341 111927816101190684843084503)
    ·
      refine ⟨167891724151786027264626755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111927816101190684843084503 167891724151786027264626755)
      ·
        refine ⟨251837586227679040896940133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167891724151786027264626755 251837586227679040896940133)
        ·
          refine ⟨47219547417689820168176275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251837586227679040896940133 47219547417689820168176275)
          ·
            refine ⟨70829321126534730252264413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47219547417689820168176275 70829321126534730252264413)
            ·
              refine ⟨26560995422450523844599155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70829321126534730252264413 26560995422450523844599155)
              ·
                refine ⟨39841493133675785766898733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26560995422450523844599155 39841493133675785766898733)
                ·
                  refine ⟨14940559925128419662587025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39841493133675785766898733 14940559925128419662587025)
                  ·
                    refine ⟨11205419943846314746940269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14940559925128419662587025 11205419943846314746940269)
                    ·
                      refine ⟨4202032478942368030102601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11205419943846314746940269 4202032478942368030102601)
                      ·
                        rfl

theorem cell23_8183429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_8183429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183429 prefixEnd_8183429 := by exact prefixLift 8183429
  have htrace : WordTrace (prefixWord ++ tailWord_8183429) baseStart_8183429 baseEnd_8183429 := by
    simpa [prefixWord, tailWord_8183429, baseEnd_8183429] using wordTrace_append hprefix tailTrace_8183429
  have hstable : (prefixWord ++ tailWord_8183429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183429).length < 2 ^ (prefixWord ++ tailWord_8183429).sum := by decide
  have hdescent : baseEnd_8183429 < baseStart_8183429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183460 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_8183460 : Nat := 118140960795 + 8183460 * 2 ^ 59
def prefixEnd_8183460 : Nat := 4983230072969 + 3 ^ 40 * 8183460 * 2
def baseEnd_8183460 : Nat := 4202048396842657408814959

theorem tailTrace_8183460 : CollatzResearch.WordTrace tailWord_8183460 prefixEnd_8183460 4202048396842657408814959 := by
  unfold tailWord_8183460
  simp only [CollatzResearch.WordTrace]
  refine ⟨149237653466364759271301917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198983537955153012361735889 149237653466364759271301917)
  ·
    refine ⟨55964120049886784726738219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149237653466364759271301917 55964120049886784726738219)
    ·
      refine ⟨83946180074830177090107329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55964120049886784726738219 83946180074830177090107329)
      ·
        refine ⟨62959635056122632817580497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83946180074830177090107329 62959635056122632817580497)
        ·
          refine ⟨47219726292091974613185373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62959635056122632817580497 47219726292091974613185373)
          ·
            refine ⟨17707397359534490479944515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47219726292091974613185373 17707397359534490479944515)
            ·
              refine ⟨26561096039301735719916773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17707397359534490479944515 26561096039301735719916773)
              ·
                refine ⟨4980205507369075447484395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26561096039301735719916773 4980205507369075447484395)
                ·
                  refine ⟨7470308261053613171226593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980205507369075447484395 7470308261053613171226593)
                  ·
                    refine ⟨5602731195790209878419945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470308261053613171226593 5602731195790209878419945)
                    ·
                      refine ⟨4202048396842657408814959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602731195790209878419945 4202048396842657408814959)
                      ·
                        rfl

theorem cell23_8183460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_8183460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183460 prefixEnd_8183460 := by exact prefixLift 8183460
  have htrace : WordTrace (prefixWord ++ tailWord_8183460) baseStart_8183460 baseEnd_8183460 := by
    simpa [prefixWord, tailWord_8183460, baseEnd_8183460] using wordTrace_append hprefix tailTrace_8183460
  have hstable : (prefixWord ++ tailWord_8183460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183460).length < 2 ^ (prefixWord ++ tailWord_8183460).sum := by decide
  have hdescent : baseEnd_8183460 < baseStart_8183460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183494 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_8183494 : Nat := 118140960795 + 8183494 * 2 ^ 59
def prefixEnd_8183494 : Nat := 4983230072969 + 3 ^ 40 * 8183494 * 2
def baseEnd_8183494 : Nat := 4202065855184910275789803

theorem tailTrace_8183494 : CollatzResearch.WordTrace tailWord_8183494 prefixEnd_8183494 4202065855184910275789803 := by
  unfold tailWord_8183494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327392094206448198416923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198984364676404228232894357 9327392094206448198416923)
  ·
    refine ⟨13991088141309672297625385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327392094206448198416923 13991088141309672297625385)
    ·
      refine ⟨10493316105982254223219039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13991088141309672297625385 10493316105982254223219039)
      ·
        refine ⟨15739974158973381334828559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10493316105982254223219039 15739974158973381334828559)
        ·
          refine ⟨23609961238460072002242839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15739974158973381334828559 23609961238460072002242839)
          ·
            refine ⟨35414941857690108003364259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23609961238460072002242839 35414941857690108003364259)
            ·
              refine ⟨53122412786535162005046389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35414941857690108003364259 53122412786535162005046389)
              ·
                refine ⟨4980226198737671437973099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53122412786535162005046389 4980226198737671437973099)
                ·
                  refine ⟨7470339298106507156959649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980226198737671437973099 7470339298106507156959649)
                  ·
                    refine ⟨5602754473579880367719737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470339298106507156959649 5602754473579880367719737)
                    ·
                      refine ⟨4202065855184910275789803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602754473579880367719737 4202065855184910275789803)
                      ·
                        rfl

theorem cell23_8183494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_8183494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183494 prefixEnd_8183494 := by exact prefixLift 8183494
  have htrace : WordTrace (prefixWord ++ tailWord_8183494) baseStart_8183494 baseEnd_8183494 := by
    simpa [prefixWord, tailWord_8183494, baseEnd_8183494] using wordTrace_append hprefix tailTrace_8183494
  have hstable : (prefixWord ++ tailWord_8183494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183494).length < 2 ^ (prefixWord ++ tailWord_8183494).sum := by decide
  have hdescent : baseEnd_8183494 < baseStart_8183494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183527 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8183527 : Nat := 118140960795 + 8183527 * 2 ^ 59
def prefixEnd_8183527 : Nat := 4983230072969 + 3 ^ 40 * 8183527 * 2
def baseEnd_8183527 : Nat := 4202082800046508646677151

theorem tailTrace_8183527 : CollatzResearch.WordTrace tailWord_8183527 prefixEnd_8183527 4202082800046508646677151 := by
  unfold tailWord_8183527
  simp only [CollatzResearch.WordTrace]
  refine ⟨298477750623486788985292835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198985167082324525990195223 298477750623486788985292835)
  ·
    refine ⟨447716625935230183477939253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298477750623486788985292835 447716625935230183477939253)
    ·
      refine ⟨41973433681427829701056805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 447716625935230183477939253 41973433681427829701056805)
      ·
        refine ⟨7870018815267718068948151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41973433681427829701056805 7870018815267718068948151)
        ·
          refine ⟨11805028222901577103422227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870018815267718068948151 11805028222901577103422227)
          ·
            refine ⟨17707542334352365655133341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11805028222901577103422227 17707542334352365655133341)
            ·
              refine ⟨6640328375382137120675003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17707542334352365655133341 6640328375382137120675003)
              ·
                refine ⟨9960492563073205681012505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640328375382137120675003 9960492563073205681012505)
                ·
                  refine ⟨7470369422304904260759379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960492563073205681012505 7470369422304904260759379)
                  ·
                    refine ⟨11205554133457356391139069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7470369422304904260759379 11205554133457356391139069)
                    ·
                      refine ⟨4202082800046508646677151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11205554133457356391139069 4202082800046508646677151)
                      ·
                        rfl

theorem cell23_8183527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8183527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183527 prefixEnd_8183527 := by exact prefixLift 8183527
  have htrace : WordTrace (prefixWord ++ tailWord_8183527) baseStart_8183527 baseEnd_8183527 := by
    simpa [prefixWord, tailWord_8183527, baseEnd_8183527] using wordTrace_append hprefix tailTrace_8183527
  have hstable : (prefixWord ++ tailWord_8183527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183527).length < 2 ^ (prefixWord ++ tailWord_8183527).sum := by decide
  have hdescent : baseEnd_8183527 < baseStart_8183527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183533 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_8183533 : Nat := 118140960795 + 8183533 * 2 ^ 59
def prefixEnd_8183533 : Nat := 4983230072969 + 3 ^ 40 * 8183533 * 2
def baseEnd_8183533 : Nat := 4202085880930435623202123

theorem tailTrace_8183533 : CollatzResearch.WordTrace tailWord_8183533 prefixEnd_8183533 4202085880930435623202123 := by
  unfold tailWord_8183533
  simp only [CollatzResearch.WordTrace]
  refine ⟨298477969461465052010011253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198985312974310034673340835 298477969461465052010011253)
  ·
    refine ⟨27982309637012348625938555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298477969461465052010011253 27982309637012348625938555)
    ·
      refine ⟨41973464455518522938907833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27982309637012348625938555 41973464455518522938907833)
      ·
        refine ⟨31480098341638892204180875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41973464455518522938907833 31480098341638892204180875)
        ·
          refine ⟨47220147512458338306271313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31480098341638892204180875 47220147512458338306271313)
          ·
            refine ⟨35415110634343753729703485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47220147512458338306271313 35415110634343753729703485)
            ·
              refine ⟨13280666487878907648638807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35415110634343753729703485 13280666487878907648638807)
              ·
                refine ⟨19920999731818361472958211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13280666487878907648638807 19920999731818361472958211)
                ·
                  refine ⟨29881499597727542209437317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19920999731818361472958211 29881499597727542209437317)
                  ·
                    refine ⟨5602781174573914164269497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29881499597727542209437317 5602781174573914164269497)
                    ·
                      refine ⟨4202085880930435623202123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602781174573914164269497 4202085880930435623202123)
                      ·
                        rfl

theorem cell23_8183533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_8183533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183533 prefixEnd_8183533 := by exact prefixLift 8183533
  have htrace : WordTrace (prefixWord ++ tailWord_8183533) baseStart_8183533 baseEnd_8183533 := by
    simpa [prefixWord, tailWord_8183533, baseEnd_8183533] using wordTrace_append hprefix tailTrace_8183533
  have hstable : (prefixWord ++ tailWord_8183533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183533).length < 2 ^ (prefixWord ++ tailWord_8183533).sum := by decide
  have hdescent : baseEnd_8183533 < baseStart_8183533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183549 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_8183549 : Nat := 118140960795 + 8183549 * 2 ^ 59
def prefixEnd_8183549 : Nat := 4983230072969 + 3 ^ 40 * 8183549 * 2
def baseEnd_8183549 : Nat := 4202094096620907560602049

theorem tailTrace_8183549 : CollatzResearch.WordTrace tailWord_8183549 prefixEnd_8183549 4202094096620907560602049 := by
  unfold tailWord_8183549
  simp only [CollatzResearch.WordTrace]
  refine ⟨298478553029407086742593701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198985702019604724495062467 298478553029407086742593701)
  ·
    refine ⟨55964728693013828764236319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298478553029407086742593701 55964728693013828764236319)
    ·
      refine ⟨83947093039520743146354479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55964728693013828764236319 83947093039520743146354479)
      ·
        refine ⟨125920639559281114719531719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83947093039520743146354479 125920639559281114719531719)
        ·
          refine ⟨188880959338921672079297579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125920639559281114719531719 188880959338921672079297579)
          ·
            refine ⟨283321439008382508118946369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188880959338921672079297579 283321439008382508118946369)
            ·
              refine ⟨212491079256286881089209777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283321439008382508118946369 212491079256286881089209777)
              ·
                refine ⟨159368309442215160816907333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212491079256286881089209777 159368309442215160816907333)
                ·
                  refine ⟨29881558020415342653170125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159368309442215160816907333 29881558020415342653170125)
                  ·
                    refine ⟨11205584257655753494938797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29881558020415342653170125 11205584257655753494938797)
                    ·
                      refine ⟨4202094096620907560602049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11205584257655753494938797 4202094096620907560602049)
                      ·
                        rfl

theorem cell23_8183549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_8183549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183549 prefixEnd_8183549 := by exact prefixLift 8183549
  have htrace : WordTrace (prefixWord ++ tailWord_8183549) baseStart_8183549 baseEnd_8183549 := by
    simpa [prefixWord, tailWord_8183549, baseEnd_8183549] using wordTrace_append hprefix tailTrace_8183549
  have hstable : (prefixWord ++ tailWord_8183549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183549).length < 2 ^ (prefixWord ++ tailWord_8183549).sum := by decide
  have hdescent : baseEnd_8183549 < baseStart_8183549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183573 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 5]
def baseStart_8183573 : Nat := 118140960795 + 8183573 * 2 ^ 59
def prefixEnd_8183573 : Nat := 4983230072969 + 3 ^ 40 * 8183573 * 2
def baseEnd_8183573 : Nat := 466900713350735051855771

theorem tailTrace_8183573 : CollatzResearch.WordTrace tailWord_8183573 prefixEnd_8183573 466900713350735051855771 := by
  unfold tailWord_8183573
  simp only [CollatzResearch.WordTrace]
  refine ⟨298479428381320138841467373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198986285587546759227644915 298479428381320138841467373)
  ·
    refine ⟨111929785642995052065550265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298479428381320138841467373 111929785642995052065550265)
    ·
      refine ⟨83947339232246289049162699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111929785642995052065550265 83947339232246289049162699)
      ·
        refine ⟨125921008848369433573744049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83947339232246289049162699 125921008848369433573744049)
        ·
          refine ⟨94440756636277075180308037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125921008848369433573744049 94440756636277075180308037)
          ·
            refine ⟨17707641869301951596307757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94440756636277075180308037 17707641869301951596307757)
            ·
              refine ⟨6640365700988231848615409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17707641869301951596307757 6640365700988231848615409)
              ·
                refine ⟨4980274275741173886461557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640365700988231848615409 4980274275741173886461557)
                ·
                  refine ⟨466900713350735051855771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980274275741173886461557 466900713350735051855771)
                  ·
                    rfl

theorem cell23_8183573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_8183573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183573 prefixEnd_8183573 := by exact prefixLift 8183573
  have htrace : WordTrace (prefixWord ++ tailWord_8183573) baseStart_8183573 baseEnd_8183573 := by
    simpa [prefixWord, tailWord_8183573, baseEnd_8183573] using wordTrace_append hprefix tailTrace_8183573
  have hstable : (prefixWord ++ tailWord_8183573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183573).length < 2 ^ (prefixWord ++ tailWord_8183573).sum := by decide
  have hdescent : baseEnd_8183573 < baseStart_8183573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183626 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_8183626 : Nat := 118140960795 + 8183626 * 2 ^ 59
def prefixEnd_8183626 : Nat := 4983230072969 + 3 ^ 40 * 8183626 * 2
def baseEnd_8183626 : Nat := 4202133634631303759339195

theorem tailTrace_8183626 : CollatzResearch.WordTrace tailWord_8183626 prefixEnd_8183626 4202133634631303759339195 := by
  unfold tailWord_8183626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74620340362532032223286683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198987574300085419262097821 74620340362532032223286683)
  ·
    refine ⟨111930510543798048334930025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74620340362532032223286683 111930510543798048334930025)
    ·
      refine ⟨83947882907848536251197519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111930510543798048334930025 83947882907848536251197519)
      ·
        refine ⟨125921824361772804376796279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83947882907848536251197519 125921824361772804376796279)
        ·
          refine ⟨188882736542659206565194419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125921824361772804376796279 188882736542659206565194419)
          ·
            refine ⟨283324104813988809847791629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188882736542659206565194419 283324104813988809847791629)
            ·
              refine ⟨106246539305245803692921861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283324104813988809847791629 106246539305245803692921861)
              ·
                refine ⟨19921226119733588192422849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106246539305245803692921861 19921226119733588192422849)
                ·
                  refine ⟨14940919589800191144317137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19921226119733588192422849 14940919589800191144317137)
                  ·
                    refine ⟨11205689692350143358237853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14940919589800191144317137 11205689692350143358237853)
                    ·
                      refine ⟨4202133634631303759339195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11205689692350143358237853 4202133634631303759339195)
                      ·
                        rfl

theorem cell23_8183626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_8183626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183626 prefixEnd_8183626 := by exact prefixLift 8183626
  have htrace : WordTrace (prefixWord ++ tailWord_8183626) baseStart_8183626 baseEnd_8183626 := by
    simpa [prefixWord, tailWord_8183626, baseEnd_8183626] using wordTrace_append hprefix tailTrace_8183626
  have hstable : (prefixWord ++ tailWord_8183626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183626).length < 2 ^ (prefixWord ++ tailWord_8183626).sum := by decide
  have hdescent : baseEnd_8183626 < baseStart_8183626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183696 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 6, 2]
def baseStart_8183696 : Nat := 118140960795 + 8183696 * 2 ^ 59
def prefixEnd_8183696 : Nat := 4983230072969 + 3 ^ 40 * 8183696 * 2
def baseEnd_8183696 : Nat := 4202169578277118485463873

theorem tailTrace_8183696 : CollatzResearch.WordTrace tailWord_8183696 prefixEnd_8183696 4202169578277118485463873 := by
  unfold tailWord_8183696
  simp only [CollatzResearch.WordTrace]
  refine ⟨149241957279937265424097471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198989276373249687232129961 149241957279937265424097471)
  ·
    refine ⟨223862935919905898136146207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149241957279937265424097471 223862935919905898136146207)
    ·
      refine ⟨335794403879858847204219311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223862935919905898136146207 335794403879858847204219311)
      ·
        refine ⟨503691605819788270806328967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335794403879858847204219311 503691605819788270806328967)
        ·
          refine ⟨755537408729682406209493451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503691605819788270806328967 755537408729682406209493451)
          ·
            refine ⟨1133306113094523609314240177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755537408729682406209493451 1133306113094523609314240177)
            ·
              refine ⟨849979584820892706985680133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133306113094523609314240177 849979584820892706985680133)
              ·
                refine ⟨159371172153917382559815025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 849979584820892706985680133 159371172153917382559815025)
                ·
                  refine ⟨119528379115438036919861269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159371172153917382559815025 119528379115438036919861269)
                  ·
                    refine ⟨5602892771036157980618497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119528379115438036919861269 5602892771036157980618497)
                    ·
                      refine ⟨4202169578277118485463873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602892771036157980618497 4202169578277118485463873)
                      ·
                        rfl

theorem cell23_8183696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 6, 2].length) (baseStart_8183696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183696 prefixEnd_8183696 := by exact prefixLift 8183696
  have htrace : WordTrace (prefixWord ++ tailWord_8183696) baseStart_8183696 baseEnd_8183696 := by
    simpa [prefixWord, tailWord_8183696, baseEnd_8183696] using wordTrace_append hprefix tailTrace_8183696
  have hstable : (prefixWord ++ tailWord_8183696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183696).length < 2 ^ (prefixWord ++ tailWord_8183696).sum := by decide
  have hdescent : baseEnd_8183696 < baseStart_8183696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183733 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_8183733 : Nat := 118140960795 + 8183733 * 2 ^ 59
def prefixEnd_8183733 : Nat := 4983230072969 + 3 ^ 40 * 8183733 * 2
def baseEnd_8183733 : Nat := 4202188577061334840701203

theorem tailTrace_8183733 : CollatzResearch.WordTrace tailWord_8183733 prefixEnd_8183733 4202188577061334840701203 := by
  unfold tailWord_8183733
  simp only [CollatzResearch.WordTrace]
  refine ⟨298485264060740486167291853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198990176040493657444861235 298485264060740486167291853)
  ·
    refine ⟨111931974022777682312734445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298485264060740486167291853 111931974022777682312734445)
    ·
      refine ⟨41974490258541630867275417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111931974022777682312734445 41974490258541630867275417)
      ·
        refine ⟨31480867693906223150456563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41974490258541630867275417 31480867693906223150456563)
        ·
          refine ⟨47221301540859334725684845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31480867693906223150456563 47221301540859334725684845)
          ·
            refine ⟨17707988077822250522131817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47221301540859334725684845 17707988077822250522131817)
            ·
              refine ⟨13280991058366687891598863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17707988077822250522131817 13280991058366687891598863)
              ·
                refine ⟨19921486587550031837398295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13280991058366687891598863 19921486587550031837398295)
                ·
                  refine ⟨29882229881325047756097443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19921486587550031837398295 29882229881325047756097443)
                  ·
                    refine ⟨44823344821987571634146165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29882229881325047756097443 44823344821987571634146165)
                    ·
                      refine ⟨4202188577061334840701203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44823344821987571634146165 4202188577061334840701203)
                      ·
                        rfl

theorem cell23_8183733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_8183733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183733 prefixEnd_8183733 := by exact prefixLift 8183733
  have htrace : WordTrace (prefixWord ++ tailWord_8183733) baseStart_8183733 baseEnd_8183733 := by
    simpa [prefixWord, tailWord_8183733, baseEnd_8183733] using wordTrace_append hprefix tailTrace_8183733
  have hstable : (prefixWord ++ tailWord_8183733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183733).length < 2 ^ (prefixWord ++ tailWord_8183733).sum := by decide
  have hdescent : baseEnd_8183733 < baseStart_8183733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183739 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_8183739 : Nat := 118140960795 + 8183739 * 2 ^ 59
def prefixEnd_8183739 : Nat := 4983230072969 + 3 ^ 40 * 8183739 * 2
def baseEnd_8183739 : Nat := 4202191657945261817226175

theorem tailTrace_8183739 : CollatzResearch.WordTrace tailWord_8183739 prefixEnd_8183739 4202191657945261817226175 := by
  unfold tailWord_8183739
  simp only [CollatzResearch.WordTrace]
  refine ⟨298485482898718749192010271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198990321932479166128006847 298485482898718749192010271)
  ·
    refine ⟨447728224348078123788015407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298485482898718749192010271 447728224348078123788015407)
    ·
      refine ⟨671592336522117185682023111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447728224348078123788015407 671592336522117185682023111)
      ·
        refine ⟨1007388504783175778523034667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671592336522117185682023111 1007388504783175778523034667)
        ·
          refine ⟨1511082757174763667784552001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007388504783175778523034667 1511082757174763667784552001)
          ·
            refine ⟨1133312067881072750838414001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511082757174763667784552001 1133312067881072750838414001)
            ·
              refine ⟨849984050910804563128810501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133312067881072750838414001 849984050910804563128810501)
              ·
                refine ⟨159372009545775855586651969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 849984050910804563128810501 159372009545775855586651969)
                ·
                  refine ⟨119529007159331891689988977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159372009545775855586651969 119529007159331891689988977)
                  ·
                    refine ⟨89646755369498918767491733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119529007159331891689988977 89646755369498918767491733)
                    ·
                      refine ⟨4202191657945261817226175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89646755369498918767491733 4202191657945261817226175)
                      ·
                        rfl

theorem cell23_8183739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_8183739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183739 prefixEnd_8183739 := by exact prefixLift 8183739
  have htrace : WordTrace (prefixWord ++ tailWord_8183739) baseStart_8183739 baseEnd_8183739 := by
    simpa [prefixWord, tailWord_8183739, baseEnd_8183739] using wordTrace_append hprefix tailTrace_8183739
  have hstable : (prefixWord ++ tailWord_8183739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183739).length < 2 ^ (prefixWord ++ tailWord_8183739).sum := by decide
  have hdescent : baseEnd_8183739 < baseStart_8183739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183798 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_8183798 : Nat := 118140960795 + 8183798 * 2 ^ 59
def prefixEnd_8183798 : Nat := 4983230072969 + 3 ^ 40 * 8183798 * 2
def baseEnd_8183798 : Nat := 4202221953303877086388405

theorem tailTrace_8183798 : CollatzResearch.WordTrace tailWord_8183798 prefixEnd_8183798 4202221953303877086388405 := by
  unfold tailWord_8183798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655477175344062641775503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198991756537003334845605365 18655477175344062641775503)
  ·
    refine ⟨27983215763016093962663255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18655477175344062641775503 27983215763016093962663255)
    ·
      refine ⟨41974823644524140943994883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27983215763016093962663255 41974823644524140943994883)
      ·
        refine ⟨62962235466786211415992325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41974823644524140943994883 62962235466786211415992325)
        ·
          refine ⟨11805419150022414640498561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62962235466786211415992325 11805419150022414640498561)
          ·
            refine ⟨8854064362516810980373921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11805419150022414640498561 8854064362516810980373921)
            ·
              refine ⟨6640548271887608235280441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854064362516810980373921 6640548271887608235280441)
              ·
                refine ⟨4980411203915706176460331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640548271887608235280441 4980411203915706176460331)
                ·
                  refine ⟨7470616805873559264690497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980411203915706176460331 7470616805873559264690497)
                  ·
                    refine ⟨5602962604405169448517873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470616805873559264690497 5602962604405169448517873)
                    ·
                      refine ⟨4202221953303877086388405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602962604405169448517873 4202221953303877086388405)
                      ·
                        rfl

theorem cell23_8183798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_8183798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183798 prefixEnd_8183798 := by exact prefixLift 8183798
  have htrace : WordTrace (prefixWord ++ tailWord_8183798) baseStart_8183798 baseEnd_8183798 := by
    simpa [prefixWord, tailWord_8183798, baseEnd_8183798] using wordTrace_append hprefix tailTrace_8183798
  have hstable : (prefixWord ++ tailWord_8183798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183798).length < 2 ^ (prefixWord ++ tailWord_8183798).sum := by decide
  have hdescent : baseEnd_8183798 < baseStart_8183798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183820 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 1, 4, 2]
def baseStart_8183820 : Nat := 118140960795 + 8183820 * 2 ^ 59
def prefixEnd_8183820 : Nat := 4983230072969 + 3 ^ 40 * 8183820 * 2
def baseEnd_8183820 : Nat := 4202233249878276000313303

theorem tailTrace_8183820 : CollatzResearch.WordTrace tailWord_8183820 prefixEnd_8183820 4202233249878276000313303 := by
  unfold tailWord_8183820
  simp only [CollatzResearch.WordTrace]
  refine ⟨149244218605712650012854457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198992291474283533350472609 149244218605712650012854457)
  ·
    refine ⟨111933163954284487509640843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149244218605712650012854457 111933163954284487509640843)
    ·
      refine ⟨167899745931426731264461265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111933163954284487509640843 167899745931426731264461265)
      ·
        refine ⟨125924809448570048448345949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167899745931426731264461265 125924809448570048448345949)
        ·
          refine ⟨47221803543213768168129731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125924809448570048448345949 47221803543213768168129731)
          ·
            refine ⟨70832705314820652252194597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47221803543213768168129731 70832705314820652252194597)
            ·
              refine ⟨13281132246528872297286487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70832705314820652252194597 13281132246528872297286487)
              ·
                refine ⟨19921698369793308445929731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13281132246528872297286487 19921698369793308445929731)
                ·
                  refine ⟨29882547554689962668894597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19921698369793308445929731 29882547554689962668894597)
                  ·
                    refine ⟨5602977666504368000417737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29882547554689962668894597 5602977666504368000417737)
                    ·
                      refine ⟨4202233249878276000313303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602977666504368000417737 4202233249878276000313303)
                      ·
                        rfl

theorem cell23_8183820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_8183820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183820 prefixEnd_8183820 := by exact prefixLift 8183820
  have htrace : WordTrace (prefixWord ++ tailWord_8183820) baseStart_8183820 baseEnd_8183820 := by
    simpa [prefixWord, tailWord_8183820, baseEnd_8183820] using wordTrace_append hprefix tailTrace_8183820
  have hstable : (prefixWord ++ tailWord_8183820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183820).length < 2 ^ (prefixWord ++ tailWord_8183820).sum := by decide
  have hdescent : baseEnd_8183820 < baseStart_8183820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183841 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_8183841 : Nat := 118140960795 + 8183841 * 2 ^ 59
def prefixEnd_8183841 : Nat := 4983230072969 + 3 ^ 40 * 8183841 * 2
def baseEnd_8183841 : Nat := 4202244032972020418150707

theorem tailTrace_8183841 : CollatzResearch.WordTrace tailWord_8183841 prefixEnd_8183841 4202244032972020418150707 := by
  unfold tailWord_8183841
  simp only [CollatzResearch.WordTrace]
  refine ⟨298489203144349220612223377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198992802096232813741482251 298489203144349220612223377)
  ·
    refine ⟨223866902358261915459167533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298489203144349220612223377 223866902358261915459167533)
    ·
      refine ⟨83950088384348218297187825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223866902358261915459167533 83950088384348218297187825)
      ·
        refine ⟨62962566288261163722890869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83950088384348218297187825 62962566288261163722890869)
        ·
          refine ⟨5902740589524484099021019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62962566288261163722890869 5902740589524484099021019)
          ·
            refine ⟨8854110884286726148531529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902740589524484099021019 8854110884286726148531529)
            ·
              refine ⟨6640583163215044611398647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854110884286726148531529 6640583163215044611398647)
              ·
                refine ⟨9960874744822566917097971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640583163215044611398647 9960874744822566917097971)
                ·
                  refine ⟨14941312117233850375646957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9960874744822566917097971 14941312117233850375646957)
                  ·
                    refine ⟨5602992043962693890867609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14941312117233850375646957 5602992043962693890867609)
                    ·
                      refine ⟨4202244032972020418150707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5602992043962693890867609 4202244032972020418150707)
                      ·
                        rfl

theorem cell23_8183841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_8183841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183841 prefixEnd_8183841 := by exact prefixLift 8183841
  have htrace : WordTrace (prefixWord ++ tailWord_8183841) baseStart_8183841 baseEnd_8183841 := by
    simpa [prefixWord, tailWord_8183841, baseEnd_8183841] using wordTrace_append hprefix tailTrace_8183841
  have hstable : (prefixWord ++ tailWord_8183841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183841).length < 2 ^ (prefixWord ++ tailWord_8183841).sum := by decide
  have hdescent : baseEnd_8183841 < baseStart_8183841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183854 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_8183854 : Nat := 118140960795 + 8183854 * 2 ^ 59
def prefixEnd_8183854 : Nat := 4983230072969 + 3 ^ 40 * 8183854 * 2
def baseEnd_8183854 : Nat := 4202250708220528867288147

theorem tailTrace_8183854 : CollatzResearch.WordTrace tailWord_8183854 prefixEnd_8183854 4202250708220528867288147 := by
  unfold tailWord_8183854
  simp only [CollatzResearch.WordTrace]
  refine ⟨37311209661662765479055827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198993118195534749221631077 37311209661662765479055827)
  ·
    refine ⟨55966814492494148218583741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37311209661662765479055827 55966814492494148218583741)
    ·
      refine ⟨20987555434685305581968903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55966814492494148218583741 20987555434685305581968903)
      ·
        refine ⟨31481333152027958372953355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20987555434685305581968903 31481333152027958372953355)
        ·
          refine ⟨47221999728041937559430033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31481333152027958372953355 47221999728041937559430033)
          ·
            refine ⟨35416499796031453169572525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47221999728041937559430033 35416499796031453169572525)
            ·
              refine ⟨13281187423511794938589697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35416499796031453169572525 13281187423511794938589697)
              ·
                refine ⟨9960890567633846203942273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13281187423511794938589697 9960890567633846203942273)
                ·
                  refine ⟨7470667925725384652956705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960890567633846203942273 7470667925725384652956705)
                  ·
                    refine ⟨5603000944294038489717529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470667925725384652956705 5603000944294038489717529)
                    ·
                      refine ⟨4202250708220528867288147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603000944294038489717529 4202250708220528867288147)
                      ·
                        rfl

theorem cell23_8183854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_8183854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183854 prefixEnd_8183854 := by exact prefixLift 8183854
  have htrace : WordTrace (prefixWord ++ tailWord_8183854) baseStart_8183854 baseEnd_8183854 := by
    simpa [prefixWord, tailWord_8183854, baseEnd_8183854] using wordTrace_append hprefix tailTrace_8183854
  have hstable : (prefixWord ++ tailWord_8183854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183854).length < 2 ^ (prefixWord ++ tailWord_8183854).sum := by decide
  have hdescent : baseEnd_8183854 < baseStart_8183854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183863 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 7, 2]
def baseStart_8183863 : Nat := 118140960795 + 8183863 * 2 ^ 59
def prefixEnd_8183863 : Nat := 4983230072969 + 3 ^ 40 * 8183863 * 2
def baseEnd_8183863 : Nat := 4202255329546419332075605

theorem tailTrace_8183863 : CollatzResearch.WordTrace tailWord_8183863 prefixEnd_8183863 4202255329546419332075605 := by
  unfold tailWord_8183863
  simp only [CollatzResearch.WordTrace]
  refine ⟨298490005550269518369524243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198993337033513012246349495 298490005550269518369524243)
  ·
    refine ⟨447735008325404277554286365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298490005550269518369524243 447735008325404277554286365)
    ·
      refine ⟨167900628122026604082857387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447735008325404277554286365 167900628122026604082857387)
      ·
        refine ⟨251850942183039906124286081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167900628122026604082857387 251850942183039906124286081)
        ·
          refine ⟨188888206637279929593214561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251850942183039906124286081 188888206637279929593214561)
          ·
            refine ⟨141666154977959947194910921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188888206637279929593214561 141666154977959947194910921)
            ·
              refine ⟨106249616233469960396183191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141666154977959947194910921 106249616233469960396183191)
              ·
                refine ⟨159374424350204940594274787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106249616233469960396183191 159374424350204940594274787)
                ·
                  refine ⟨239061636525307410891412181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159374424350204940594274787 239061636525307410891412181)
                  ·
                    refine ⟨5603007106061892442767473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 239061636525307410891412181 5603007106061892442767473)
                    ·
                      refine ⟨4202255329546419332075605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603007106061892442767473 4202255329546419332075605)
                      ·
                        rfl

theorem cell23_8183863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_8183863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183863 prefixEnd_8183863 := by exact prefixLift 8183863
  have htrace : WordTrace (prefixWord ++ tailWord_8183863) baseStart_8183863 baseEnd_8183863 := by
    simpa [prefixWord, tailWord_8183863, baseEnd_8183863] using wordTrace_append hprefix tailTrace_8183863
  have hstable : (prefixWord ++ tailWord_8183863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183863).length < 2 ^ (prefixWord ++ tailWord_8183863).sum := by decide
  have hdescent : baseEnd_8183863 < baseStart_8183863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183866 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_8183866 : Nat := 118140960795 + 8183866 * 2 ^ 59
def prefixEnd_8183866 : Nat := 4983230072969 + 3 ^ 40 * 8183866 * 2
def baseEnd_8183866 : Nat := 4202256869988382820338091

theorem tailTrace_8183866 : CollatzResearch.WordTrace tailWord_8183866 prefixEnd_8183866 4202256869988382820338091 := by
  unfold tailWord_8183866
  simp only [CollatzResearch.WordTrace]
  refine ⟨74622528742314662470470863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198993409979505766587922301 74622528742314662470470863)
  ·
    refine ⟨111933793113471993705706295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74622528742314662470470863 111933793113471993705706295)
    ·
      refine ⟨167900689670207990558559443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111933793113471993705706295 167900689670207990558559443)
      ·
        refine ⟨251851034505311985837839165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167900689670207990558559443 251851034505311985837839165)
        ·
          refine ⟨94444137939491994689189687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251851034505311985837839165 94444137939491994689189687)
          ·
            refine ⟨141666206909237992033784531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94444137939491994689189687 141666206909237992033784531)
            ·
              refine ⟨212499310363856988050676797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141666206909237992033784531 212499310363856988050676797)
              ·
                refine ⟨79687241386446370519003799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212499310363856988050676797 79687241386446370519003799)
                ·
                  refine ⟨119530862079669555778505699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79687241386446370519003799 119530862079669555778505699)
                  ·
                    refine ⟨179296293119504333667758549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119530862079669555778505699 179296293119504333667758549)
                    ·
                      refine ⟨4202256869988382820338091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179296293119504333667758549 4202256869988382820338091)
                      ·
                        rfl

theorem cell23_8183866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_8183866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183866 prefixEnd_8183866 := by exact prefixLift 8183866
  have htrace : WordTrace (prefixWord ++ tailWord_8183866) baseStart_8183866 baseEnd_8183866 := by
    simpa [prefixWord, tailWord_8183866, baseEnd_8183866] using wordTrace_append hprefix tailTrace_8183866
  have hstable : (prefixWord ++ tailWord_8183866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183866).length < 2 ^ (prefixWord ++ tailWord_8183866).sum := by decide
  have hdescent : baseEnd_8183866 < baseStart_8183866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183873 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_8183873 : Nat := 118140960795 + 8183873 * 2 ^ 59
def prefixEnd_8183873 : Nat := 4983230072969 + 3 ^ 40 * 8183873 * 2
def baseEnd_8183873 : Nat := 1400753488117654764316853

theorem tailTrace_8183873 : CollatzResearch.WordTrace tailWord_8183873 prefixEnd_8183873 1400753488117654764316853 := by
  unfold tailWord_8183873
  simp only [CollatzResearch.WordTrace]
  refine ⟨298490370280233290077388273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198993580186822193384925515 298490370280233290077388273)
  ·
    refine ⟨223867777710174967558041205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298490370280233290077388273 223867777710174967558041205)
    ·
      refine ⟨20987604160328903208566363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223867777710174967558041205 20987604160328903208566363)
      ·
        refine ⟨31481406240493354812849545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20987604160328903208566363 31481406240493354812849545)
        ·
          refine ⟨23611054680370016109637159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31481406240493354812849545 23611054680370016109637159)
          ·
            refine ⟨35416582020555024164455739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23611054680370016109637159 35416582020555024164455739)
            ·
              refine ⟨53124873030832536246683609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35416582020555024164455739 53124873030832536246683609)
              ·
                refine ⟨39843654773124402185012707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53124873030832536246683609 39843654773124402185012707)
                ·
                  refine ⟨59765482159686603277519061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39843654773124402185012707 59765482159686603277519061)
                  ·
                    refine ⟨1400753488117654764316853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59765482159686603277519061 1400753488117654764316853)
                    ·
                      rfl

theorem cell23_8183873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_8183873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183873 prefixEnd_8183873 := by exact prefixLift 8183873
  have htrace : WordTrace (prefixWord ++ tailWord_8183873) baseStart_8183873 baseEnd_8183873 := by
    simpa [prefixWord, tailWord_8183873, baseEnd_8183873] using wordTrace_append hprefix tailTrace_8183873
  have hstable : (prefixWord ++ tailWord_8183873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183873).length < 2 ^ (prefixWord ++ tailWord_8183873).sum := by decide
  have hdescent : baseEnd_8183873 < baseStart_8183873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183893 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_8183893 : Nat := 118140960795 + 8183893 * 2 ^ 59
def prefixEnd_8183893 : Nat := 4983230072969 + 3 ^ 40 * 8183893 * 2
def baseEnd_8183893 : Nat := 4202270733966054214700467

theorem tailTrace_8183893 : CollatzResearch.WordTrace tailWord_8183893 prefixEnd_8183893 4202270733966054214700467 := by
  unfold tailWord_8183893
  simp only [CollatzResearch.WordTrace]
  refine ⟨298491099740160833493116333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198994066493440555662077555 298491099740160833493116333)
  ·
    refine ⟨111934162402560312559918625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298491099740160833493116333 111934162402560312559918625)
    ·
      refine ⟨83950621801920234419938969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111934162402560312559918625 83950621801920234419938969)
      ·
        refine ⟨62962966351440175814954227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83950621801920234419938969 62962966351440175814954227)
        ·
          refine ⟨94444449527160263722431341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62962966351440175814954227 94444449527160263722431341)
          ·
            refine ⟨35416668572685098895911753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94444449527160263722431341 35416668572685098895911753)
            ·
              refine ⟨26562501429513824171933815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35416668572685098895911753 26562501429513824171933815)
              ·
                refine ⟨39843752144270736257900723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26562501429513824171933815 39843752144270736257900723)
                ·
                  refine ⟨59765628216406104386851085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39843752144270736257900723 59765628216406104386851085)
                  ·
                    refine ⟨22412110581152289145069157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59765628216406104386851085 22412110581152289145069157)
                    ·
                      refine ⟨4202270733966054214700467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22412110581152289145069157 4202270733966054214700467)
                      ·
                        rfl

theorem cell23_8183893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_8183893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183893 prefixEnd_8183893 := by exact prefixLift 8183893
  have htrace : WordTrace (prefixWord ++ tailWord_8183893) baseStart_8183893 baseEnd_8183893 := by
    simpa [prefixWord, tailWord_8183893, baseEnd_8183893] using wordTrace_append hprefix tailTrace_8183893
  have hstable : (prefixWord ++ tailWord_8183893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183893).length < 2 ^ (prefixWord ++ tailWord_8183893).sum := by decide
  have hdescent : baseEnd_8183893 < baseStart_8183893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183894 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_8183894 : Nat := 118140960795 + 8183894 * 2 ^ 59
def prefixEnd_8183894 : Nat := 4983230072969 + 3 ^ 40 * 8183894 * 2
def baseEnd_8183894 : Nat := 466919027494078745643107

theorem tailTrace_8183894 : CollatzResearch.WordTrace tailWord_8183894 prefixEnd_8183894 466919027494078745643107 := by
  unfold tailWord_8183894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655696013322325666493921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198994090808771473775935157 18655696013322325666493921)
  ·
    refine ⟨13991772009991744249870441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18655696013322325666493921 13991772009991744249870441)
    ·
      refine ⟨10493829007493808187402831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13991772009991744249870441 10493829007493808187402831)
      ·
        refine ⟨15740743511240712281104247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10493829007493808187402831 15740743511240712281104247)
        ·
          refine ⟨23611115266861068421656371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15740743511240712281104247 23611115266861068421656371)
          ·
            refine ⟨35416672900291602632484557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23611115266861068421656371 35416672900291602632484557)
            ·
              refine ⟨13281252337609350987181709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35416672900291602632484557 13281252337609350987181709)
              ·
                refine ⟨4980469626603506620193141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13281252337609350987181709 4980469626603506620193141)
                ·
                  refine ⟨466919027494078745643107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980469626603506620193141 466919027494078745643107)
                  ·
                    rfl

theorem cell23_8183894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_8183894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183894 prefixEnd_8183894 := by exact prefixLift 8183894
  have htrace : WordTrace (prefixWord ++ tailWord_8183894) baseStart_8183894 baseEnd_8183894 := by
    simpa [prefixWord, tailWord_8183894, baseEnd_8183894] using wordTrace_append hprefix tailTrace_8183894
  have hstable : (prefixWord ++ tailWord_8183894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183894).length < 2 ^ (prefixWord ++ tailWord_8183894).sum := by decide
  have hdescent : baseEnd_8183894 < baseStart_8183894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183920 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 3, 4]
def baseStart_8183920 : Nat := 118140960795 + 8183920 * 2 ^ 59
def prefixEnd_8183920 : Nat := 4983230072969 + 3 ^ 40 * 8183920 * 2
def baseEnd_8183920 : Nat := 1400761532647908536354281

theorem tailTrace_8183920 : CollatzResearch.WordTrace tailWord_8183920 prefixEnd_8183920 1400761532647908536354281 := by
  unfold tailWord_8183920
  simp only [CollatzResearch.WordTrace]
  refine ⟨149246042255531508552174607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198994723007375344736232809 149246042255531508552174607)
  ·
    refine ⟨223869063383297262828261911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149246042255531508552174607 223869063383297262828261911)
    ·
      refine ⟨335803595074945894242392867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223869063383297262828261911 335803595074945894242392867)
      ·
        refine ⟨503705392612418841363589301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335803595074945894242392867 503705392612418841363589301)
        ·
          refine ⟨47222380557414266377836497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503705392612418841363589301 47222380557414266377836497)
          ·
            refine ⟨35416785418060699783377373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47222380557414266377836497 35416785418060699783377373)
            ·
              refine ⟨13281294531772762418766515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35416785418060699783377373 13281294531772762418766515)
              ·
                refine ⟨19921941797659143628149773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13281294531772762418766515 19921941797659143628149773)
                ·
                  refine ⟨7470728174122178860556165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19921941797659143628149773 7470728174122178860556165)
                  ·
                    refine ⟨1400761532647908536354281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470728174122178860556165 1400761532647908536354281)
                    ·
                      rfl

theorem cell23_8183920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_8183920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183920 prefixEnd_8183920 := by exact prefixLift 8183920
  have htrace : WordTrace (prefixWord ++ tailWord_8183920) baseStart_8183920 baseEnd_8183920 := by
    simpa [prefixWord, tailWord_8183920, baseEnd_8183920] using wordTrace_append hprefix tailTrace_8183920
  have hstable : (prefixWord ++ tailWord_8183920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183920).length < 2 ^ (prefixWord ++ tailWord_8183920).sum := by decide
  have hdescent : baseEnd_8183920 < baseStart_8183920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8183943 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_8183943 : Nat := 118140960795 + 8183943 * 2 ^ 59
def prefixEnd_8183943 : Nat := 4983230072969 + 3 ^ 40 * 8183943 * 2
def baseEnd_8183943 : Nat := 4202296407998779019075237

theorem tailTrace_8183943 : CollatzResearch.WordTrace tailWord_8183943 prefixEnd_8183943 4202296407998779019075237 := by
  unfold tailWord_8183943
  simp only [CollatzResearch.WordTrace]
  refine ⟨298492923389979692032436483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198995282259986461354957655 298492923389979692032436483)
  ·
    refine ⟨447739385084969538048654725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298492923389979692032436483 447739385084969538048654725)
    ·
      refine ⟨83951134703431788384122761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447739385084969538048654725 83951134703431788384122761)
      ·
        refine ⟨62963351027573841288092071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83951134703431788384122761 62963351027573841288092071)
        ·
          refine ⟨94445026541360761932138107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62963351027573841288092071 94445026541360761932138107)
          ·
            refine ⟨141667539812041142898207161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94445026541360761932138107 141667539812041142898207161)
            ·
              refine ⟨106250654859030857173655371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141667539812041142898207161 106250654859030857173655371)
              ·
                refine ⟨159375982288546285760483057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106250654859030857173655371 159375982288546285760483057)
                ·
                  refine ⟨119531986716409714320362293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159375982288546285760483057 119531986716409714320362293)
                  ·
                    refine ⟨11206123754663410717533965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119531986716409714320362293 11206123754663410717533965)
                    ·
                      refine ⟨4202296407998779019075237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11206123754663410717533965 4202296407998779019075237)
                      ·
                        rfl

theorem cell23_8183943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_8183943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8183943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8183943 prefixEnd_8183943 := by exact prefixLift 8183943
  have htrace : WordTrace (prefixWord ++ tailWord_8183943) baseStart_8183943 baseEnd_8183943 := by
    simpa [prefixWord, tailWord_8183943, baseEnd_8183943] using wordTrace_append hprefix tailTrace_8183943
  have hstable : (prefixWord ++ tailWord_8183943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8183943).length < 2 ^ (prefixWord ++ tailWord_8183943).sum := by decide
  have hdescent : baseEnd_8183943 < baseStart_8183943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8183943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184000 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_8184000 : Nat := 118140960795 + 8184000 * 2 ^ 59
def prefixEnd_8184000 : Nat := 4983230072969 + 3 ^ 40 * 8184000 * 2
def baseEnd_8184000 : Nat := 4202325676396085296062475

theorem tailTrace_8184000 : CollatzResearch.WordTrace tailWord_8184000 prefixEnd_8184000 4202325676396085296062475 := by
  unfold tailWord_8184000
  simp only [CollatzResearch.WordTrace]
  refine ⟨149247501175386595383630727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198996668233848793844840969 149247501175386595383630727)
  ·
    refine ⟨223871251763079893075446091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149247501175386595383630727 223871251763079893075446091)
    ·
      refine ⟨335806877644619839613169137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223871251763079893075446091 335806877644619839613169137)
      ·
        refine ⟨251855158233464879709876853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335806877644619839613169137 251855158233464879709876853)
        ·
          refine ⟨23611421084387332472800955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251855158233464879709876853 23611421084387332472800955)
          ·
            refine ⟨35417131626580998709201433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23611421084387332472800955 35417131626580998709201433)
            ·
              refine ⟨26562848719935749031901075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35417131626580998709201433 26562848719935749031901075)
              ·
                refine ⟨39844273079903623547851613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26562848719935749031901075 39844273079903623547851613)
                ·
                  refine ⟨14941602404963858830444355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39844273079903623547851613 14941602404963858830444355)
                  ·
                    refine ⟨22412403607445788245666533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14941602404963858830444355 22412403607445788245666533)
                    ·
                      refine ⟨4202325676396085296062475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22412403607445788245666533 4202325676396085296062475)
                      ·
                        rfl

theorem cell23_8184000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_8184000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184000 prefixEnd_8184000 := by exact prefixLift 8184000
  have htrace : WordTrace (prefixWord ++ tailWord_8184000) baseStart_8184000 baseEnd_8184000 := by
    simpa [prefixWord, tailWord_8184000, baseEnd_8184000] using wordTrace_append hprefix tailTrace_8184000
  have hstable : (prefixWord ++ tailWord_8184000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184000).length < 2 ^ (prefixWord ++ tailWord_8184000).sum := by decide
  have hdescent : baseEnd_8184000 < baseStart_8184000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184004 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_8184004 : Nat := 118140960795 + 8184004 * 2 ^ 59
def prefixEnd_8184004 : Nat := 4983230072969 + 3 ^ 40 * 8184004 * 2
def baseEnd_8184004 : Nat := 4202327730318703280412457

theorem tailTrace_8184004 : CollatzResearch.WordTrace tailWord_8184004 prefixEnd_8184004 4202327730318703280412457 := by
  unfold tailWord_8184004
  simp only [CollatzResearch.WordTrace]
  refine ⟨149247574121379349725203533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198996765495172466300271377 149247574121379349725203533)
  ·
    refine ⟨55967840295517256146951325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149247574121379349725203533 55967840295517256146951325)
    ·
      refine ⟨20987940110818971055106747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55967840295517256146951325 20987940110818971055106747)
      ·
        refine ⟨31481910166228456582660121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20987940110818971055106747 31481910166228456582660121)
        ·
          refine ⟨23611432624671342436995091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31481910166228456582660121 23611432624671342436995091)
          ·
            refine ⟨35417148937007013655492637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23611432624671342436995091 35417148937007013655492637)
            ·
              refine ⟨13281430851377630120809739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35417148937007013655492637 13281430851377630120809739)
              ·
                refine ⟨19922146277066445181214609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13281430851377630120809739 19922146277066445181214609)
                ·
                  refine ⟨14941609707799833885910957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19922146277066445181214609 14941609707799833885910957)
                  ·
                    refine ⟨5603103640424937707216609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14941609707799833885910957 5603103640424937707216609)
                    ·
                      refine ⟨4202327730318703280412457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603103640424937707216609 4202327730318703280412457)
                      ·
                        rfl

theorem cell23_8184004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_8184004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184004 prefixEnd_8184004 := by exact prefixLift 8184004
  have htrace : WordTrace (prefixWord ++ tailWord_8184004) baseStart_8184004 baseEnd_8184004 := by
    simpa [prefixWord, tailWord_8184004, baseEnd_8184004] using wordTrace_append hprefix tailTrace_8184004
  have hstable : (prefixWord ++ tailWord_8184004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184004).length < 2 ^ (prefixWord ++ tailWord_8184004).sum := by decide
  have hdescent : baseEnd_8184004 < baseStart_8184004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184010 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_8184010 : Nat := 118140960795 + 8184010 * 2 ^ 59
def prefixEnd_8184010 : Nat := 4983230072969 + 3 ^ 40 * 8184010 * 2
def baseEnd_8184010 : Nat := 1400776937067543418979143

theorem tailTrace_8184010 : CollatzResearch.WordTrace tailWord_8184010 prefixEnd_8184010 1400776937067543418979143 := by
  unfold tailWord_8184010
  simp only [CollatzResearch.WordTrace]
  refine ⟨74623841770184240618781371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198996911387157974983416989 74623841770184240618781371)
  ·
    refine ⟨111935762655276360928172057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74623841770184240618781371 111935762655276360928172057)
    ·
      refine ⟨83951821991457270696129043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111935762655276360928172057 83951821991457270696129043)
      ·
        refine ⟨125927732987185906044193565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83951821991457270696129043 125927732987185906044193565)
        ·
          refine ⟨47222899870194714766572587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125927732987185906044193565 47222899870194714766572587)
          ·
            refine ⟨70834349805292072149858881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47222899870194714766572587 70834349805292072149858881)
            ·
              refine ⟨53125762353969054112394161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70834349805292072149858881 53125762353969054112394161)
              ·
                refine ⟨39844321765476790584295621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53125762353969054112394161 39844321765476790584295621)
                ·
                  refine ⟨7470810331026898234555429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39844321765476790584295621 7470810331026898234555429)
                  ·
                    refine ⟨1400776937067543418979143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470810331026898234555429 1400776937067543418979143)
                    ·
                      rfl

theorem cell23_8184010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_8184010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184010 prefixEnd_8184010 := by exact prefixLift 8184010
  have htrace : WordTrace (prefixWord ++ tailWord_8184010) baseStart_8184010 baseEnd_8184010 := by
    simpa [prefixWord, tailWord_8184010, baseEnd_8184010] using wordTrace_append hprefix tailTrace_8184010
  have hstable : (prefixWord ++ tailWord_8184010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184010).length < 2 ^ (prefixWord ++ tailWord_8184010).sum := by decide
  have hdescent : baseEnd_8184010 < baseStart_8184010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184014 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_8184014 : Nat := 118140960795 + 8184014 * 2 ^ 59
def prefixEnd_8184014 : Nat := 4983230072969 + 3 ^ 40 * 8184014 * 2
def baseEnd_8184014 : Nat := 1400777621708416080429137

theorem tailTrace_8184014 : CollatzResearch.WordTrace tailWord_8184014 prefixEnd_8184014 1400777621708416080429137 := by
  unfold tailWord_8184014
  simp only [CollatzResearch.WordTrace]
  refine ⟨37311939121590308894783887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198997008648481647438847397 37311939121590308894783887)
  ·
    refine ⟨55967908682385463342175831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37311939121590308894783887 55967908682385463342175831)
    ·
      refine ⟨83951863023578195013263747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55967908682385463342175831 83951863023578195013263747)
      ·
        refine ⟨125927794535367292519895621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83951863023578195013263747 125927794535367292519895621)
        ·
          refine ⟨23611461475381367347480429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125927794535367292519895621 23611461475381367347480429)
          ·
            refine ⟨8854298053268012755305161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23611461475381367347480429 8854298053268012755305161)
            ·
              refine ⟨6640723539951009566478871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854298053268012755305161 6640723539951009566478871)
              ·
                refine ⟨9961085309926514349718307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640723539951009566478871 9961085309926514349718307)
                ·
                  refine ⟨14941627964889771524577461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9961085309926514349718307 14941627964889771524577461)
                  ·
                    refine ⟨1400777621708416080429137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14941627964889771524577461 1400777621708416080429137)
                    ·
                      rfl

theorem cell23_8184014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_8184014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184014 prefixEnd_8184014 := by exact prefixLift 8184014
  have htrace : WordTrace (prefixWord ++ tailWord_8184014) baseStart_8184014 baseEnd_8184014 := by
    simpa [prefixWord, tailWord_8184014, baseEnd_8184014] using wordTrace_append hprefix tailTrace_8184014
  have hstable : (prefixWord ++ tailWord_8184014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184014).length < 2 ^ (prefixWord ++ tailWord_8184014).sum := by decide
  have hdescent : baseEnd_8184014 < baseStart_8184014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184017 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 1, 1, 4]
def baseStart_8184017 : Nat := 118140960795 + 8184017 * 2 ^ 59
def prefixEnd_8184017 : Nat := 4983230072969 + 3 ^ 40 * 8184017 * 2
def baseEnd_8184017 : Nat := 4202334405567211729549897

theorem tailTrace_8184017 : CollatzResearch.WordTrace tailWord_8184017 prefixEnd_8184017 4202334405567211729549897 := by
  unfold tailWord_8184017
  simp only [CollatzResearch.WordTrace]
  refine ⟨298495622391711602670630305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198997081594474401780420203 298495622391711602670630305)
  ·
    refine ⟨223871716793783702002972729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298495622391711602670630305 223871716793783702002972729)
    ·
      refine ⟨167903787595337776502229547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223871716793783702002972729 167903787595337776502229547)
      ·
        refine ⟨251855681393006664753344321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167903787595337776502229547 251855681393006664753344321)
        ·
          refine ⟨188891761044754998565008241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251855681393006664753344321 188891761044754998565008241)
          ·
            refine ⟨141668820783566248923756181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188891761044754998565008241 141668820783566248923756181)
            ·
              refine ⟨6640725974229667918301071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141668820783566248923756181 6640725974229667918301071)
              ·
                refine ⟨9961088961344501877451607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640725974229667918301071 9961088961344501877451607)
                ·
                  refine ⟨14941633442016752816177411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9961088961344501877451607 14941633442016752816177411)
                  ·
                    refine ⟨22412450163025129224266117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14941633442016752816177411 22412450163025129224266117)
                    ·
                      refine ⟨4202334405567211729549897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22412450163025129224266117 4202334405567211729549897)
                      ·
                        rfl

theorem cell23_8184017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_8184017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184017 prefixEnd_8184017 := by exact prefixLift 8184017
  have htrace : WordTrace (prefixWord ++ tailWord_8184017) baseStart_8184017 baseEnd_8184017 := by
    simpa [prefixWord, tailWord_8184017, baseEnd_8184017] using wordTrace_append hprefix tailTrace_8184017
  have hstable : (prefixWord ++ tailWord_8184017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184017).length < 2 ^ (prefixWord ++ tailWord_8184017).sum := by decide
  have hdescent : baseEnd_8184017 < baseStart_8184017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184047 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 4]
def baseStart_8184047 : Nat := 118140960795 + 8184047 * 2 ^ 59
def prefixEnd_8184047 : Nat := 4983230072969 + 3 ^ 40 * 8184047 * 2
def baseEnd_8184047 : Nat := 4202349809986846612174759

theorem tailTrace_8184047 : CollatzResearch.WordTrace tailWord_8184047 prefixEnd_8184047 4202349809986846612174759 := by
  unfold tailWord_8184047
  simp only [CollatzResearch.WordTrace]
  refine ⟨298496716581602917794222395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198997811054401945196148263 298496716581602917794222395)
  ·
    refine ⟨447745074872404376691333593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298496716581602917794222395 447745074872404376691333593)
    ·
      refine ⟨335808806154303282518500195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447745074872404376691333593 335808806154303282518500195)
      ·
        refine ⟨503713209231454923777750293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335808806154303282518500195 503713209231454923777750293)
        ·
          refine ⟨23611556682724449552082045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 503713209231454923777750293 23611556682724449552082045)
          ·
            refine ⟨8854333756021668582030767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23611556682724449552082045 8854333756021668582030767)
            ·
              refine ⟨13281500634032502873046151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8854333756021668582030767 13281500634032502873046151)
              ·
                refine ⟨19922250951048754309569227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13281500634032502873046151 19922250951048754309569227)
                ·
                  refine ⟨29883376426573131464353841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19922250951048754309569227 29883376426573131464353841)
                  ·
                    refine ⟨22412532319929848598265381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29883376426573131464353841 22412532319929848598265381)
                    ·
                      refine ⟨4202349809986846612174759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22412532319929848598265381 4202349809986846612174759)
                      ·
                        rfl

theorem cell23_8184047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_8184047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184047 prefixEnd_8184047 := by exact prefixLift 8184047
  have htrace : WordTrace (prefixWord ++ tailWord_8184047) baseStart_8184047 baseEnd_8184047 := by
    simpa [prefixWord, tailWord_8184047, baseEnd_8184047] using wordTrace_append hprefix tailTrace_8184047
  have hstable : (prefixWord ++ tailWord_8184047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184047).length < 2 ^ (prefixWord ++ tailWord_8184047).sum := by decide
  have hdescent : baseEnd_8184047 < baseStart_8184047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184063 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_8184063 : Nat := 118140960795 + 8184063 * 2 ^ 59
def prefixEnd_8184063 : Nat := 4983230072969 + 3 ^ 40 * 8184063 * 2
def baseEnd_8184063 : Nat := 4202358025677318549574685

theorem tailTrace_8184063 : CollatzResearch.WordTrace tailWord_8184063 prefixEnd_8184063 4202358025677318549574685 := by
  unfold tailWord_8184063
  simp only [CollatzResearch.WordTrace]
  refine ⟨298497300149544952526804843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198998200099696635017869895 298497300149544952526804843)
  ·
    refine ⟨447745950224317428790207265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298497300149544952526804843 447745950224317428790207265)
    ·
      refine ⟨335809462668238071592655449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447745950224317428790207265 335809462668238071592655449)
      ·
        refine ⟨251857097001178553694491587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335809462668238071592655449 251857097001178553694491587)
        ·
          refine ⟨377785645501767830541737381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251857097001178553694491587 377785645501767830541737381)
          ·
            refine ⟨70834808531581468226575759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377785645501767830541737381 70834808531581468226575759)
            ·
              refine ⟨106252212797372202339863639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70834808531581468226575759 106252212797372202339863639)
              ·
                refine ⟨159378319196058303509795459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106252212797372202339863639 159378319196058303509795459)
                ·
                  refine ⟨239067478794087455264693189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159378319196058303509795459 239067478794087455264693189)
                  ·
                    refine ⟨44825152273891397862129973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239067478794087455264693189 44825152273891397862129973)
                    ·
                      refine ⟨4202358025677318549574685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44825152273891397862129973 4202358025677318549574685)
                      ·
                        rfl

theorem cell23_8184063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_8184063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184063 prefixEnd_8184063 := by exact prefixLift 8184063
  have htrace : WordTrace (prefixWord ++ tailWord_8184063) baseStart_8184063 baseEnd_8184063 := by
    simpa [prefixWord, tailWord_8184063, baseEnd_8184063] using wordTrace_append hprefix tailTrace_8184063
  have hstable : (prefixWord ++ tailWord_8184063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184063).length < 2 ^ (prefixWord ++ tailWord_8184063).sum := by decide
  have hdescent : baseEnd_8184063 < baseStart_8184063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184083 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 4, 6]
def baseStart_8184083 : Nat := 118140960795 + 8184083 * 2 ^ 59
def prefixEnd_8184083 : Nat := 4983230072969 + 3 ^ 40 * 8184083 * 2
def baseEnd_8184083 : Nat := 1400789431763469490441531

theorem tailTrace_8184083 : CollatzResearch.WordTrace tailWord_8184083 prefixEnd_8184083 1400789431763469490441531 := by
  unfold tailWord_8184083
  simp only [CollatzResearch.WordTrace]
  refine ⟨298498029609472495942532903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198998686406314997295021935 298498029609472495942532903)
  ·
    refine ⟨447747044414208743913799355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298498029609472495942532903 447747044414208743913799355)
    ·
      refine ⟨671620566621313115870699033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447747044414208743913799355 671620566621313115870699033)
      ·
        refine ⟨503715424965984836903024275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671620566621313115870699033 503715424965984836903024275)
        ·
          refine ⟨755573137448977255354536413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503715424965984836903024275 755573137448977255354536413)
          ·
            refine ⟨283339926543366470757951155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 755573137448977255354536413 283339926543366470757951155)
            ·
              refine ⟨425009889815049706136926733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283339926543366470757951155 425009889815049706136926733)
              ·
                refine ⟨159378708680643639801347525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425009889815049706136926733 159378708680643639801347525)
                ·
                  refine ⟨29883507877620682462752661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159378708680643639801347525 29883507877620682462752661)
                  ·
                    refine ⟨1400789431763469490441531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29883507877620682462752661 1400789431763469490441531)
                    ·
                      rfl

theorem cell23_8184083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 6].length) (baseStart_8184083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184083 prefixEnd_8184083 := by exact prefixLift 8184083
  have htrace : WordTrace (prefixWord ++ tailWord_8184083) baseStart_8184083 baseEnd_8184083 := by
    simpa [prefixWord, tailWord_8184083, baseEnd_8184083] using wordTrace_append hprefix tailTrace_8184083
  have hstable : (prefixWord ++ tailWord_8184083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184083).length < 2 ^ (prefixWord ++ tailWord_8184083).sum := by decide
  have hdescent : baseEnd_8184083 < baseStart_8184083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184241 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 1, 4]
def baseStart_8184241 : Nat := 118140960795 + 8184241 * 2 ^ 59
def prefixEnd_8184241 : Nat := 4983230072969 + 3 ^ 40 * 8184241 * 2
def baseEnd_8184241 : Nat := 1400816475077939617716289

theorem tailTrace_8184241 : CollatzResearch.WordTrace tailWord_8184241 prefixEnd_8184241 1400816475077939617716289 := by
  unfold tailWord_8184241
  simp only [CollatzResearch.WordTrace]
  refine ⟨298503792342900088926784577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199002528228600059284523051 298503792342900088926784577)
  ·
    refine ⟨223877844257175066695088433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298503792342900088926784577 223877844257175066695088433)
    ·
      refine ⟨167908383192881300021316325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223877844257175066695088433 167908383192881300021316325)
      ·
        refine ⟨31482821848665243753996811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167908383192881300021316325 31482821848665243753996811)
        ·
          refine ⟨47224232772997865630995217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31482821848665243753996811 47224232772997865630995217)
          ·
            refine ⟨35418174579748399223246413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47224232772997865630995217 35418174579748399223246413)
            ·
              refine ⟨13281815467405649708717405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35418174579748399223246413 13281815467405649708717405)
              ·
                refine ⟨4980680800277118640769027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13281815467405649708717405 4980680800277118640769027)
                ·
                  refine ⟨7471021200415677961153541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980680800277118640769027 7471021200415677961153541)
                  ·
                    refine ⟨1400816475077939617716289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7471021200415677961153541 1400816475077939617716289)
                    ·
                      rfl

theorem cell23_8184241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_8184241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184241 prefixEnd_8184241 := by exact prefixLift 8184241
  have htrace : WordTrace (prefixWord ++ tailWord_8184241) baseStart_8184241 baseEnd_8184241 := by
    simpa [prefixWord, tailWord_8184241, baseEnd_8184241] using wordTrace_append hprefix tailTrace_8184241
  have hstable : (prefixWord ++ tailWord_8184241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184241).length < 2 ^ (prefixWord ++ tailWord_8184241).sum := by decide
  have hdescent : baseEnd_8184241 < baseStart_8184241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184297 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 4, 4]
def baseStart_8184297 : Nat := 118140960795 + 8184297 * 2 ^ 59
def prefixEnd_8184297 : Nat := 4983230072969 + 3 ^ 40 * 8184297 * 2
def baseEnd_8184297 : Nat := 1400826060050156878016203

theorem tailTrace_8184297 : CollatzResearch.WordTrace tailWord_8184297 prefixEnd_8184297 1400826060050156878016203 := by
  unfold tailWord_8184297
  simp only [CollatzResearch.WordTrace]
  refine ⟨298505834830697210490823145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199003889887131473660548763 298505834830697210490823145)
  ·
    refine ⟨223879376123022907868117359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298505834830697210490823145 223879376123022907868117359)
    ·
      refine ⟨335819064184534361802176039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223879376123022907868117359 335819064184534361802176039)
      ·
        refine ⟨503728596276801542703264059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335819064184534361802176039 503728596276801542703264059)
        ·
          refine ⟨755592894415202314054896089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503728596276801542703264059 755592894415202314054896089)
          ·
            refine ⟨566694670811401735541172067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755592894415202314054896089 566694670811401735541172067)
            ·
              refine ⟨850042006217102603311758101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566694670811401735541172067 850042006217102603311758101)
              ·
                refine ⟨39845719041426684530238661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850042006217102603311758101 39845719041426684530238661)
                ·
                  refine ⟨7471072320267503349419749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39845719041426684530238661 7471072320267503349419749)
                  ·
                    refine ⟨1400826060050156878016203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7471072320267503349419749 1400826060050156878016203)
                    ·
                      rfl

theorem cell23_8184297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_8184297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184297 prefixEnd_8184297 := by exact prefixLift 8184297
  have htrace : WordTrace (prefixWord ++ tailWord_8184297) baseStart_8184297 baseEnd_8184297 := by
    simpa [prefixWord, tailWord_8184297, baseEnd_8184297] using wordTrace_append hprefix tailTrace_8184297
  have hstable : (prefixWord ++ tailWord_8184297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184297).length < 2 ^ (prefixWord ++ tailWord_8184297).sum := by decide
  have hdescent : baseEnd_8184297 < baseStart_8184297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184317 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_8184317 : Nat := 118140960795 + 8184317 * 2 ^ 59
def prefixEnd_8184317 : Nat := 4983230072969 + 3 ^ 40 * 8184317 * 2
def baseEnd_8184317 : Nat := 4202488449763560555798517

theorem tailTrace_8184317 : CollatzResearch.WordTrace tailWord_8184317 prefixEnd_8184317 4202488449763560555798517 := by
  unfold tailWord_8184317
  simp only [CollatzResearch.WordTrace]
  refine ⟨298506564290624753906551205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199004376193749835937700803 298506564290624753906551205)
  ·
    refine ⟨55969980804492141357478351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298506564290624753906551205 55969980804492141357478351)
    ·
      refine ⟨83954971206738212036217527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55969980804492141357478351 83954971206738212036217527)
      ·
        refine ⟨125932456810107318054326291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83954971206738212036217527 125932456810107318054326291)
        ·
          refine ⟨188898685215160977081489437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125932456810107318054326291 188898685215160977081489437)
          ·
            refine ⟨70837006955685366405558539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188898685215160977081489437 70837006955685366405558539)
            ·
              refine ⟨106255510433528049608337809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70837006955685366405558539 106255510433528049608337809)
              ·
                refine ⟨79691632825146037206253357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106255510433528049608337809 79691632825146037206253357)
                ·
                  refine ⟨29884362309429763952345009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79691632825146037206253357 29884362309429763952345009)
                  ·
                    refine ⟨22413271732072322964258757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29884362309429763952345009 22413271732072322964258757)
                    ·
                      refine ⟨4202488449763560555798517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22413271732072322964258757 4202488449763560555798517)
                      ·
                        rfl

theorem cell23_8184317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_8184317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184317 prefixEnd_8184317 := by exact prefixLift 8184317
  have htrace : WordTrace (prefixWord ++ tailWord_8184317) baseStart_8184317 baseEnd_8184317 := by
    simpa [prefixWord, tailWord_8184317, baseEnd_8184317] using wordTrace_append hprefix tailTrace_8184317
  have hstable : (prefixWord ++ tailWord_8184317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184317).length < 2 ^ (prefixWord ++ tailWord_8184317).sum := by decide
  have hdescent : baseEnd_8184317 < baseStart_8184317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184334 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_8184334 : Nat := 118140960795 + 8184334 * 2 ^ 59
def prefixEnd_8184334 : Nat := 4983230072969 + 3 ^ 40 * 8184334 * 2
def baseEnd_8184334 : Nat := 4202497178934686989285939

theorem tailTrace_8184334 : CollatzResearch.WordTrace tailWord_8184334 prefixEnd_8184334 4202497178934686989285939 := by
  unfold tailWord_8184334
  simp only [CollatzResearch.WordTrace]
  refine ⟨37313398041445395726240007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199004789554375443873280037 37313398041445395726240007)
  ·
    refine ⟨55970097062168093589360011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37313398041445395726240007 55970097062168093589360011)
    ·
      refine ⟨83955145593252140384040017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55970097062168093589360011 83955145593252140384040017)
      ·
        refine ⟨62966359194939105288030013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83955145593252140384040017 62966359194939105288030013)
        ·
          refine ⟨23612384698102164483011255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62966359194939105288030013 23612384698102164483011255)
          ·
            refine ⟨35418577047153246724516883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23612384698102164483011255 35418577047153246724516883)
            ·
              refine ⟨53127865570729870086775325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35418577047153246724516883 53127865570729870086775325)
              ·
                refine ⟨19922949589023701282540747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53127865570729870086775325 19922949589023701282540747)
                ·
                  refine ⟨29884424383535551923811121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19922949589023701282540747 29884424383535551923811121)
                  ·
                    refine ⟨22413318287651663942858341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29884424383535551923811121 22413318287651663942858341)
                    ·
                      refine ⟨4202497178934686989285939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22413318287651663942858341 4202497178934686989285939)
                      ·
                        rfl

theorem cell23_8184334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_8184334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184334 prefixEnd_8184334 := by exact prefixLift 8184334
  have htrace : WordTrace (prefixWord ++ tailWord_8184334) baseStart_8184334 baseEnd_8184334 := by
    simpa [prefixWord, tailWord_8184334, baseEnd_8184334] using wordTrace_append hprefix tailTrace_8184334
  have hstable : (prefixWord ++ tailWord_8184334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184334).length < 2 ^ (prefixWord ++ tailWord_8184334).sum := by decide
  have hdescent : baseEnd_8184334 < baseStart_8184334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184344 : List Nat := [2, 1, 2, 3, 3, 2, 3, 7]
def baseStart_8184344 : Nat := 118140960795 + 8184344 * 2 ^ 59
def prefixEnd_8184344 : Nat := 4983230072969 + 3 ^ 40 * 8184344 * 2
def baseEnd_8184344 : Nat := 155648233842267850005959

theorem tailTrace_8184344 : CollatzResearch.WordTrace tailWord_8184344 prefixEnd_8184344 155648233842267850005959 := by
  unfold tailWord_8184344
  simp only [CollatzResearch.WordTrace]
  refine ⟨149253774530763468758892043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199005032707684625011856057 149253774530763468758892043)
  ·
    refine ⟨223880661796145203138338065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149253774530763468758892043 223880661796145203138338065)
    ·
      refine ⟨167910496347108902353753549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223880661796145203138338065 167910496347108902353753549)
      ·
        refine ⟨62966436130165838382657581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167910496347108902353753549 62966436130165838382657581)
        ·
          refine ⟨23612413548812189393496593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62966436130165838382657581 23612413548812189393496593)
          ·
            refine ⟨17709310161609142045122445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23612413548812189393496593 17709310161609142045122445)
            ·
              refine ⟨6640991310603428266920917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17709310161609142045122445 6640991310603428266920917)
              ·
                refine ⟨155648233842267850005959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6640991310603428266920917 155648233842267850005959)
                ·
                  rfl

theorem cell23_8184344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 7].length) (baseStart_8184344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184344 prefixEnd_8184344 := by exact prefixLift 8184344
  have htrace : WordTrace (prefixWord ++ tailWord_8184344) baseStart_8184344 baseEnd_8184344 := by
    simpa [prefixWord, tailWord_8184344, baseEnd_8184344] using wordTrace_append hprefix tailTrace_8184344
  have hstable : (prefixWord ++ tailWord_8184344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184344).length < 2 ^ (prefixWord ++ tailWord_8184344).sum := by decide
  have hdescent : baseEnd_8184344 < baseStart_8184344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184355 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 1, 2, 2]
def baseStart_8184355 : Nat := 118140960795 + 8184355 * 2 ^ 59
def prefixEnd_8184355 : Nat := 4983230072969 + 3 ^ 40 * 8184355 * 2
def baseEnd_8184355 : Nat := 4202507962028431407123343

theorem tailTrace_8184355 : CollatzResearch.WordTrace tailWord_8184355 prefixEnd_8184355 4202507962028431407123343 := by
  unfold tailWord_8184355
  simp only [CollatzResearch.WordTrace]
  refine ⟨298507950264487086396434519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199005300176324724264289679 298507950264487086396434519)
  ·
    refine ⟨447761925396730629594651779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298507950264487086396434519 447761925396730629594651779)
    ·
      refine ⟨671642888095095944391977669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447761925396730629594651779 671642888095095944391977669)
      ·
        refine ⟨125933041517830489573495813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 671642888095095944391977669 125933041517830489573495813)
        ·
          refine ⟨23612445284593216795030465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125933041517830489573495813 23612445284593216795030465)
          ·
            refine ⟨17709333963444912596272849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23612445284593216795030465 17709333963444912596272849)
            ·
              refine ⟨13282000472583684447204637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17709333963444912596272849 13282000472583684447204637)
              ·
                refine ⟨4980750177218881667701739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13282000472583684447204637 4980750177218881667701739)
                ·
                  refine ⟨7471125265828322501552609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980750177218881667701739 7471125265828322501552609)
                  ·
                    refine ⟨5603343949371241876164457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471125265828322501552609 5603343949371241876164457)
                    ·
                      refine ⟨4202507962028431407123343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603343949371241876164457 4202507962028431407123343)
                      ·
                        rfl

theorem cell23_8184355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_8184355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184355 prefixEnd_8184355 := by exact prefixLift 8184355
  have htrace : WordTrace (prefixWord ++ tailWord_8184355) baseStart_8184355 baseEnd_8184355 := by
    simpa [prefixWord, tailWord_8184355, baseEnd_8184355] using wordTrace_append hprefix tailTrace_8184355
  have hstable : (prefixWord ++ tailWord_8184355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184355).length < 2 ^ (prefixWord ++ tailWord_8184355).sum := by decide
  have hdescent : baseEnd_8184355 < baseStart_8184355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184365 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_8184365 : Nat := 118140960795 + 8184365 * 2 ^ 59
def prefixEnd_8184365 : Nat := 4983230072969 + 3 ^ 40 * 8184365 * 2
def baseEnd_8184365 : Nat := 1400837698944992122666099

theorem tailTrace_8184365 : CollatzResearch.WordTrace tailWord_8184365 prefixEnd_8184365 1400837698944992122666099 := by
  unfold tailWord_8184365
  simp only [CollatzResearch.WordTrace]
  refine ⟨298508314994450858104298549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199005543329633905402865699 298508314994450858104298549)
  ·
    refine ⟨27985154530729767947277989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298508314994450858104298549 27985154530729767947277989)
    ·
      refine ⟨5247216474511831490114623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27985154530729767947277989 5247216474511831490114623)
      ·
        refine ⟨7870824711767747235171935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247216474511831490114623 7870824711767747235171935)
        ·
          refine ⟨11806237067651620852757903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870824711767747235171935 11806237067651620852757903)
          ·
            refine ⟨17709355601477431279136855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806237067651620852757903 17709355601477431279136855)
            ·
              refine ⟨26564033402216146918705283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17709355601477431279136855 26564033402216146918705283)
              ·
                refine ⟨39846050103324220378057925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26564033402216146918705283 39846050103324220378057925)
                ·
                  refine ⟨7471134394373291320885861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39846050103324220378057925 7471134394373291320885861)
                  ·
                    refine ⟨1400837698944992122666099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7471134394373291320885861 1400837698944992122666099)
                    ·
                      rfl

theorem cell23_8184365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_8184365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184365 prefixEnd_8184365 := by exact prefixLift 8184365
  have htrace : WordTrace (prefixWord ++ tailWord_8184365) baseStart_8184365 baseEnd_8184365 := by
    simpa [prefixWord, tailWord_8184365, baseEnd_8184365] using wordTrace_append hprefix tailTrace_8184365
  have hstable : (prefixWord ++ tailWord_8184365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184365).length < 2 ^ (prefixWord ++ tailWord_8184365).sum := by decide
  have hdescent : baseEnd_8184365 < baseStart_8184365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184372 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_8184372 : Nat := 118140960795 + 8184372 * 2 ^ 59
def prefixEnd_8184372 : Nat := 4983230072969 + 3 ^ 40 * 8184372 * 2
def baseEnd_8184372 : Nat := 4202516691199557840610765

theorem tailTrace_8184372 : CollatzResearch.WordTrace tailWord_8184372 prefixEnd_8184372 4202516691199557840610765 := by
  unfold tailWord_8184372
  simp only [CollatzResearch.WordTrace]
  refine ⟨149254285152712749149901685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199005713536950332199868913 149254285152712749149901685)
  ·
    refine ⟨13992589233066820232803283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149254285152712749149901685 13992589233066820232803283)
    ·
      refine ⟨20988883849600230349204925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13992589233066820232803283 20988883849600230349204925)
      ·
        refine ⟨7870831443600086380951847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20988883849600230349204925 7870831443600086380951847)
        ·
          refine ⟨11806247165400129571427771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870831443600086380951847 11806247165400129571427771)
          ·
            refine ⟨17709370748100194357141657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806247165400129571427771 17709370748100194357141657)
            ·
              refine ⟨13282028061075145767856243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17709370748100194357141657 13282028061075145767856243)
              ·
                refine ⟨19923042091612718651784365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13282028061075145767856243 19923042091612718651784365)
                ·
                  refine ⟨7471140784354769494419137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19923042091612718651784365 7471140784354769494419137)
                  ·
                    refine ⟨5603355588266077120814353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471140784354769494419137 5603355588266077120814353)
                    ·
                      refine ⟨4202516691199557840610765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603355588266077120814353 4202516691199557840610765)
                      ·
                        rfl

theorem cell23_8184372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_8184372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184372 prefixEnd_8184372 := by exact prefixLift 8184372
  have htrace : WordTrace (prefixWord ++ tailWord_8184372) baseStart_8184372 baseEnd_8184372 := by
    simpa [prefixWord, tailWord_8184372, baseEnd_8184372] using wordTrace_append hprefix tailTrace_8184372
  have hstable : (prefixWord ++ tailWord_8184372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184372).length < 2 ^ (prefixWord ++ tailWord_8184372).sum := by decide
  have hdescent : baseEnd_8184372 < baseStart_8184372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184444 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_8184444 : Nat := 118140960795 + 8184444 * 2 ^ 59
def prefixEnd_8184444 : Nat := 4983230072969 + 3 ^ 40 * 8184444 * 2
def baseEnd_8184444 : Nat := 4202553661806681558910433

theorem tailTrace_8184444 : CollatzResearch.WordTrace tailWord_8184444 prefixEnd_8184444 4202553661806681558910433 := by
  unfold tailWord_8184444
  simp only [CollatzResearch.WordTrace]
  refine ⟨149255598180582327298212193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199007464240776436397616257 149255598180582327298212193)
  ·
    refine ⟨111941698635436745473659145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149255598180582327298212193 111941698635436745473659145)
    ·
      refine ⟨83956273976577559105244359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111941698635436745473659145 83956273976577559105244359)
      ·
        refine ⟨125934410964866338657866539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83956273976577559105244359 125934410964866338657866539)
        ·
          refine ⟨188901616447299507986799809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125934410964866338657866539 188901616447299507986799809)
          ·
            refine ⟨141676212335474630990099857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188901616447299507986799809 141676212335474630990099857)
            ·
              refine ⟨106257159251605973242574893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141676212335474630990099857 106257159251605973242574893)
              ·
                refine ⟨39846434719352239965965585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106257159251605973242574893 39846434719352239965965585)
                ·
                  refine ⟨29884826039514179974474189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39846434719352239965965585 29884826039514179974474189)
                  ·
                    refine ⟨11206809764817817490427821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29884826039514179974474189 11206809764817817490427821)
                    ·
                      refine ⟨4202553661806681558910433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11206809764817817490427821 4202553661806681558910433)
                      ·
                        rfl

theorem cell23_8184444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_8184444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184444 prefixEnd_8184444 := by exact prefixLift 8184444
  have htrace : WordTrace (prefixWord ++ tailWord_8184444) baseStart_8184444 baseEnd_8184444 := by
    simpa [prefixWord, tailWord_8184444, baseEnd_8184444] using wordTrace_append hprefix tailTrace_8184444
  have hstable : (prefixWord ++ tailWord_8184444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184444).length < 2 ^ (prefixWord ++ tailWord_8184444).sum := by decide
  have hdescent : baseEnd_8184444 < baseStart_8184444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184445 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_8184445 : Nat := 118140960795 + 8184445 * 2 ^ 59
def prefixEnd_8184445 : Nat := 4983230072969 + 3 ^ 40 * 8184445 * 2
def baseEnd_8184445 : Nat := 4202554175287336054997929

theorem tailTrace_8184445 : CollatzResearch.WordTrace tailWord_8184445 prefixEnd_8184445 4202554175287336054997929 := by
  unfold tailWord_8184445
  simp only [CollatzResearch.WordTrace]
  refine ⟨298511232834161031767210789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199007488556107354511473859 298511232834161031767210789)
  ·
    refine ⟨55970856156405193456352023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298511232834161031767210789 55970856156405193456352023)
    ·
      refine ⟨83956284234607790184528035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55970856156405193456352023 83956284234607790184528035)
      ·
        refine ⟨125934426351911685276792053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83956284234607790184528035 125934426351911685276792053)
        ·
          refine ⟨11806352470491720494699255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125934426351911685276792053 11806352470491720494699255)
          ·
            refine ⟨17709528705737580742048883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806352470491720494699255 17709528705737580742048883)
            ·
              refine ⟨26564293058606371113073325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17709528705737580742048883 26564293058606371113073325)
              ·
                refine ⟨9961609896977389167402497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26564293058606371113073325 9961609896977389167402497)
                ·
                  refine ⟨7471207422733041875551873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9961609896977389167402497 7471207422733041875551873)
                  ·
                    refine ⟨5603405567049781406663905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471207422733041875551873 5603405567049781406663905)
                    ·
                      refine ⟨4202554175287336054997929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603405567049781406663905 4202554175287336054997929)
                      ·
                        rfl

theorem cell23_8184445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_8184445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184445 prefixEnd_8184445 := by exact prefixLift 8184445
  have htrace : WordTrace (prefixWord ++ tailWord_8184445) baseStart_8184445 baseEnd_8184445 := by
    simpa [prefixWord, tailWord_8184445, baseEnd_8184445] using wordTrace_append hprefix tailTrace_8184445
  have hstable : (prefixWord ++ tailWord_8184445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184445).length < 2 ^ (prefixWord ++ tailWord_8184445).sum := by decide
  have hdescent : baseEnd_8184445 < baseStart_8184445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184447 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 1, 7]
def baseStart_8184447 : Nat := 118140960795 + 8184447 * 2 ^ 59
def prefixEnd_8184447 : Nat := 4983230072969 + 3 ^ 40 * 8184447 * 2
def baseEnd_8184447 : Nat := 1400851734082881682390973

theorem tailTrace_8184447 : CollatzResearch.WordTrace tailWord_8184447 prefixEnd_8184447 1400851734082881682390973 := by
  unfold tailWord_8184447
  simp only [CollatzResearch.WordTrace]
  refine ⟨298511305780153786108783595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199007537186769190739189063 298511305780153786108783595)
  ·
    refine ⟨447766958670230679163175393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298511305780153786108783595 447766958670230679163175393)
    ·
      refine ⟨335825219002673009372381545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447766958670230679163175393 335825219002673009372381545)
      ·
        refine ⟨251868914252004757029286159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335825219002673009372381545 251868914252004757029286159)
        ·
          refine ⟨377803371378007135543929239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251868914252004757029286159 377803371378007135543929239)
          ·
            refine ⟨566705057067010703315893859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377803371378007135543929239 566705057067010703315893859)
            ·
              refine ⟨850057585600516054973840789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566705057067010703315893859 850057585600516054973840789)
              ·
                refine ⟨39846449325024190076898787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850057585600516054973840789 39846449325024190076898787)
                ·
                  refine ⟨59769673987536285115348181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39846449325024190076898787 59769673987536285115348181)
                  ·
                    refine ⟨1400851734082881682390973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59769673987536285115348181 1400851734082881682390973)
                    ·
                      rfl

theorem cell23_8184447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_8184447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184447 prefixEnd_8184447 := by exact prefixLift 8184447
  have htrace : WordTrace (prefixWord ++ tailWord_8184447) baseStart_8184447 baseEnd_8184447 := by
    simpa [prefixWord, tailWord_8184447, baseEnd_8184447] using wordTrace_append hprefix tailTrace_8184447
  have hstable : (prefixWord ++ tailWord_8184447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184447).length < 2 ^ (prefixWord ++ tailWord_8184447).sum := by decide
  have hdescent : baseEnd_8184447 < baseStart_8184447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184457 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_8184457 : Nat := 118140960795 + 8184457 * 2 ^ 59
def prefixEnd_8184457 : Nat := 4983230072969 + 3 ^ 40 * 8184457 * 2
def baseEnd_8184457 : Nat := 4202560337055190008047873

theorem tailTrace_8184457 : CollatzResearch.WordTrace tailWord_8184457 prefixEnd_8184457 4202560337055190008047873 := by
  unfold tailWord_8184457
  simp only [CollatzResearch.WordTrace]
  refine ⟨298511670510117557816647625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199007780340078371877765083 298511670510117557816647625)
  ·
    refine ⟨223883752882588168362485719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298511670510117557816647625 223883752882588168362485719)
    ·
      refine ⟨335825629323882252543728579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223883752882588168362485719 335825629323882252543728579)
      ·
        refine ⟨503738443985823378815592869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335825629323882252543728579 503738443985823378815592869)
        ·
          refine ⟨94450958247341883527923663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503738443985823378815592869 94450958247341883527923663)
          ·
            refine ⟨141676437371012825291885495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94450958247341883527923663 141676437371012825291885495)
            ·
              refine ⟨212514656056519237937828243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141676437371012825291885495 212514656056519237937828243)
              ·
                refine ⟨318771984084778856906742365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212514656056519237937828243 318771984084778856906742365)
                ·
                  refine ⟨119539494031792071340028387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318771984084778856906742365 119539494031792071340028387)
                  ·
                    refine ⟨179309241047688107010042581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119539494031792071340028387 179309241047688107010042581)
                    ·
                      refine ⟨4202560337055190008047873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179309241047688107010042581 4202560337055190008047873)
                      ·
                        rfl

theorem cell23_8184457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_8184457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184457 prefixEnd_8184457 := by exact prefixLift 8184457
  have htrace : WordTrace (prefixWord ++ tailWord_8184457) baseStart_8184457 baseEnd_8184457 := by
    simpa [prefixWord, tailWord_8184457, baseEnd_8184457] using wordTrace_append hprefix tailTrace_8184457
  have hstable : (prefixWord ++ tailWord_8184457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184457).length < 2 ^ (prefixWord ++ tailWord_8184457).sum := by decide
  have hdescent : baseEnd_8184457 < baseStart_8184457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184507 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 12]
def baseStart_8184507 : Nat := 118140960795 + 8184507 * 2 ^ 59
def prefixEnd_8184507 : Nat := 4983230072969 + 3 ^ 40 * 8184507 * 2
def baseEnd_8184507 : Nat := 466954001231990534713627

theorem tailTrace_8184507 : CollatzResearch.WordTrace tailWord_8184507 prefixEnd_8184507 466954001231990534713627 := by
  unfold tailWord_8184507
  simp only [CollatzResearch.WordTrace]
  refine ⟨298513494159936416355967775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199008996106624277570645183 298513494159936416355967775)
  ·
    refine ⟨447770241239904624533951663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298513494159936416355967775 447770241239904624533951663)
    ·
      refine ⟨671655361859856936800927495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447770241239904624533951663 671655361859856936800927495)
      ·
        refine ⟨1007483042789785405201391243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671655361859856936800927495 1007483042789785405201391243)
        ·
          refine ⟨1511224564184678107802086865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007483042789785405201391243 1511224564184678107802086865)
          ·
            refine ⟨1133418423138508580851565149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511224564184678107802086865 1133418423138508580851565149)
            ·
              refine ⟨425031908676940717819336931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133418423138508580851565149 425031908676940717819336931)
              ·
                refine ⟨637547863015411076729005397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425031908676940717819336931 637547863015411076729005397)
                ·
                  refine ⟨466954001231990534713627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 637547863015411076729005397 466954001231990534713627)
                  ·
                    rfl

theorem cell23_8184507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 12].length) (baseStart_8184507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184507 prefixEnd_8184507 := by exact prefixLift 8184507
  have htrace : WordTrace (prefixWord ++ tailWord_8184507) baseStart_8184507 baseEnd_8184507 := by
    simpa [prefixWord, tailWord_8184507, baseEnd_8184507] using wordTrace_append hprefix tailTrace_8184507
  have hstable : (prefixWord ++ tailWord_8184507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184507).length < 2 ^ (prefixWord ++ tailWord_8184507).sum := by decide
  have hdescent : baseEnd_8184507 < baseStart_8184507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184511 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 3, 4]
def baseStart_8184511 : Nat := 118140960795 + 8184511 * 2 ^ 59
def prefixEnd_8184511 : Nat := 4983230072969 + 3 ^ 40 * 8184511 * 2
def baseEnd_8184511 : Nat := 1400862688336844265590875

theorem tailTrace_8184511 : CollatzResearch.WordTrace tailWord_8184511 prefixEnd_8184511 1400862688336844265590875 := by
  unfold tailWord_8184511
  simp only [CollatzResearch.WordTrace]
  refine ⟨298513640051921925039113387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199009093367947950026075591 298513640051921925039113387)
  ·
    refine ⟨447770460077882887558670081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298513640051921925039113387 447770460077882887558670081)
    ·
      refine ⟨335827845058412165669002561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447770460077882887558670081 335827845058412165669002561)
      ·
        refine ⟨251870883793809124251751921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335827845058412165669002561 251870883793809124251751921)
        ·
          refine ⟨188903162845356843188813941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251870883793809124251751921 188903162845356843188813941)
          ·
            refine ⟨17709671516752204048951307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188903162845356843188813941 17709671516752204048951307)
            ·
              refine ⟨26564507275128306073426961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17709671516752204048951307 26564507275128306073426961)
              ·
                refine ⟨19923380456346229555070221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26564507275128306073426961 19923380456346229555070221)
                ·
                  refine ⟨7471267671129836083151333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19923380456346229555070221 7471267671129836083151333)
                  ·
                    refine ⟨1400862688336844265590875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7471267671129836083151333 1400862688336844265590875)
                    ·
                      rfl

theorem cell23_8184511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_8184511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184511 prefixEnd_8184511 := by exact prefixLift 8184511
  have htrace : WordTrace (prefixWord ++ tailWord_8184511) baseStart_8184511 baseEnd_8184511 := by
    simpa [prefixWord, tailWord_8184511, baseEnd_8184511] using wordTrace_append hprefix tailTrace_8184511
  have hstable : (prefixWord ++ tailWord_8184511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184511).length < 2 ^ (prefixWord ++ tailWord_8184511).sum := by decide
  have hdescent : baseEnd_8184511 < baseStart_8184511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184558 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_8184558 : Nat := 118140960795 + 8184558 * 2 ^ 59
def prefixEnd_8184558 : Nat := 4983230072969 + 3 ^ 40 * 8184558 * 2
def baseEnd_8184558 : Nat := 466956910955699345876101

theorem tailTrace_8184558 : CollatzResearch.WordTrace tailWord_8184558 prefixEnd_8184558 466956910955699345876101 := by
  unfold tailWord_8184558
  simp only [CollatzResearch.WordTrace]
  refine ⟨37314419285343956508259291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199010236188501101377382885 37314419285343956508259291)
  ·
    refine ⟨55971628928015934762388937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37314419285343956508259291 55971628928015934762388937)
    ·
      refine ⟨41978721696011951071791703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55971628928015934762388937 41978721696011951071791703)
      ·
        refine ⟨62968082544017926607687555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41978721696011951071791703 62968082544017926607687555)
        ·
          refine ⟨94452123816026889911531333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62968082544017926607687555 94452123816026889911531333)
          ·
            refine ⟨17709773215505041858412125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94452123816026889911531333 17709773215505041858412125)
            ·
              refine ⟨6641164955814390696904547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17709773215505041858412125 6641164955814390696904547)
              ·
                refine ⟨9961747433721586045356821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641164955814390696904547 9961747433721586045356821)
                ·
                  refine ⟨466956910955699345876101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9961747433721586045356821 466956910955699345876101)
                  ·
                    rfl

theorem cell23_8184558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_8184558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184558 prefixEnd_8184558 := by exact prefixLift 8184558
  have htrace : WordTrace (prefixWord ++ tailWord_8184558) baseStart_8184558 baseEnd_8184558 := by
    simpa [prefixWord, tailWord_8184558, baseEnd_8184558] using wordTrace_append hprefix tailTrace_8184558
  have hstable : (prefixWord ++ tailWord_8184558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184558).length < 2 ^ (prefixWord ++ tailWord_8184558).sum := by decide
  have hdescent : baseEnd_8184558 < baseStart_8184558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184561 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 3, 5, 2]
def baseStart_8184561 : Nat := 118140960795 + 8184561 * 2 ^ 59
def prefixEnd_8184561 : Nat := 4983230072969 + 3 ^ 40 * 8184561 * 2
def baseEnd_8184561 : Nat := 4202613739043257601147395

theorem tailTrace_8184561 : CollatzResearch.WordTrace tailWord_8184561 prefixEnd_8184561 4202613739043257601147395 := by
  unfold tailWord_8184561
  simp only [CollatzResearch.WordTrace]
  refine ⟨298515463701740783578433537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199010309134493855718955691 298515463701740783578433537)
  ·
    refine ⟨223886597776305587683825153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298515463701740783578433537 223886597776305587683825153)
    ·
      refine ⟨167914948332229190762868865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223886597776305587683825153 167914948332229190762868865)
      ·
        refine ⟨125936211249171893072151649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167914948332229190762868865 125936211249171893072151649)
        ·
          refine ⟨94452158436878919804113737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125936211249171893072151649 94452158436878919804113737)
          ·
            refine ⟨70839118827659189853085303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94452158436878919804113737 70839118827659189853085303)
            ·
              refine ⟨106258678241488784779627955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70839118827659189853085303 106258678241488784779627955)
              ·
                refine ⟨159388017362233177169441933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106258678241488784779627955 159388017362233177169441933)
                ·
                  refine ⟨59770506510837441438540725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159388017362233177169441933 59770506510837441438540725)
                  ·
                    refine ⟨5603484985391010134863193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59770506510837441438540725 5603484985391010134863193)
                    ·
                      refine ⟨4202613739043257601147395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603484985391010134863193 4202613739043257601147395)
                      ·
                        rfl

theorem cell23_8184561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_8184561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184561 prefixEnd_8184561 := by exact prefixLift 8184561
  have htrace : WordTrace (prefixWord ++ tailWord_8184561) baseStart_8184561 baseEnd_8184561 := by
    simpa [prefixWord, tailWord_8184561, baseEnd_8184561] using wordTrace_append hprefix tailTrace_8184561
  have hstable : (prefixWord ++ tailWord_8184561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184561).length < 2 ^ (prefixWord ++ tailWord_8184561).sum := by decide
  have hdescent : baseEnd_8184561 < baseStart_8184561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184585 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 1, 1, 3]
def baseStart_8184585 : Nat := 118140960795 + 8184585 * 2 ^ 59
def prefixEnd_8184585 : Nat := 4983230072969 + 3 ^ 40 * 8184585 * 2
def baseEnd_8184585 : Nat := 4202626062578965507247285

theorem tailTrace_8184585 : CollatzResearch.WordTrace tailWord_8184585 prefixEnd_8184585 4202626062578965507247285 := by
  unfold tailWord_8184585
  simp only [CollatzResearch.WordTrace]
  refine ⟨298516339053653835677307209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199010892702435890451538139 298516339053653835677307209)
  ·
    refine ⟨223887254290240376757980407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298516339053653835677307209 223887254290240376757980407)
    ·
      refine ⟨335830881435360565136970611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223887254290240376757980407 335830881435360565136970611)
      ·
        refine ⟨503746322153040847705455917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335830881435360565136970611 503746322153040847705455917)
        ·
          refine ⟨188904870807390317889545969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503746322153040847705455917 188904870807390317889545969)
          ·
            refine ⟨141678653105542738417159477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188904870807390317889545969 141678653105542738417159477)
            ·
              refine ⟨13282373728644631726608701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141678653105542738417159477 13282373728644631726608701)
              ·
                refine ⟨4980890148241736897478263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13282373728644631726608701 4980890148241736897478263)
                ·
                  refine ⟨7471335222362605346217395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980890148241736897478263 7471335222362605346217395)
                  ·
                    refine ⟨11207002833543908019326093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471335222362605346217395 11207002833543908019326093)
                    ·
                      refine ⟨4202626062578965507247285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207002833543908019326093 4202626062578965507247285)
                      ·
                        rfl

theorem cell23_8184585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 1, 3].length) (baseStart_8184585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184585 prefixEnd_8184585 := by exact prefixLift 8184585
  have htrace : WordTrace (prefixWord ++ tailWord_8184585) baseStart_8184585 baseEnd_8184585 := by
    simpa [prefixWord, tailWord_8184585, baseEnd_8184585] using wordTrace_append hprefix tailTrace_8184585
  have hstable : (prefixWord ++ tailWord_8184585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184585).length < 2 ^ (prefixWord ++ tailWord_8184585).sum := by decide
  have hdescent : baseEnd_8184585 < baseStart_8184585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184591 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 4]
def baseStart_8184591 : Nat := 118140960795 + 8184591 * 2 ^ 59
def prefixEnd_8184591 : Nat := 4983230072969 + 3 ^ 40 * 8184591 * 2
def baseEnd_8184591 : Nat := 4202629143462892483772257

theorem tailTrace_8184591 : CollatzResearch.WordTrace tailWord_8184591 prefixEnd_8184591 4202629143462892483772257 := by
  unfold tailWord_8184591
  simp only [CollatzResearch.WordTrace]
  refine ⟨298516557891632098702025627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199011038594421399134683751 298516557891632098702025627)
  ·
    refine ⟨447774836837448148053038441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298516557891632098702025627 447774836837448148053038441)
    ·
      refine ⟨335831127628086111039778831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447774836837448148053038441 335831127628086111039778831)
      ·
        refine ⟨503746691442129166559668247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335831127628086111039778831 503746691442129166559668247)
        ·
          refine ⟨755620037163193749839502371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503746691442129166559668247 755620037163193749839502371)
          ·
            refine ⟨1133430055744790624759253557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755620037163193749839502371 1133430055744790624759253557)
            ·
              refine ⟨106259067726074121071180021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1133430055744790624759253557 106259067726074121071180021)
              ·
                refine ⟨9961787599319448850423127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106259067726074121071180021 9961787599319448850423127)
                ·
                  refine ⟨14942681398979173275634691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9961787599319448850423127 14942681398979173275634691)
                  ·
                    refine ⟨22414022098468759913452037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14942681398979173275634691 22414022098468759913452037)
                    ·
                      refine ⟨4202629143462892483772257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22414022098468759913452037 4202629143462892483772257)
                      ·
                        rfl

theorem cell23_8184591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_8184591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184591 prefixEnd_8184591 := by exact prefixLift 8184591
  have htrace : WordTrace (prefixWord ++ tailWord_8184591) baseStart_8184591 baseEnd_8184591 := by
    simpa [prefixWord, tailWord_8184591, baseEnd_8184591] using wordTrace_append hprefix tailTrace_8184591
  have hstable : (prefixWord ++ tailWord_8184591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184591).length < 2 ^ (prefixWord ++ tailWord_8184591).sum := by decide
  have hdescent : baseEnd_8184591 < baseStart_8184591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184602 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3]
def baseStart_8184602 : Nat := 118140960795 + 8184602 * 2 ^ 59
def prefixEnd_8184602 : Nat := 4983230072969 + 3 ^ 40 * 8184602 * 2
def baseEnd_8184602 : Nat := 4202634791750091940734707

theorem tailTrace_8184602 : CollatzResearch.WordTrace tailWord_8184602 prefixEnd_8184602 4202634791750091940734707 := by
  unfold tailWord_8184602
  simp only [CollatzResearch.WordTrace]
  refine ⟨74629239773648061895169015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199011306063061498387117373 74629239773648061895169015)
  ·
    refine ⟨111943859660472092842753523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74629239773648061895169015 111943859660472092842753523)
    ·
      refine ⟨167915789490708139264130285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111943859660472092842753523 167915789490708139264130285)
      ·
        refine ⟨62968421059015552224048857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167915789490708139264130285 62968421059015552224048857)
        ·
          refine ⟨47226315794261664168036643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62968421059015552224048857 47226315794261664168036643)
          ·
            refine ⟨70839473691392496252054965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47226315794261664168036643 70839473691392496252054965)
            ·
              refine ⟨6641200658568046523630153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70839473691392496252054965 6641200658568046523630153)
              ·
                refine ⟨4980900493926034892722615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6641200658568046523630153 4980900493926034892722615)
                ·
                  refine ⟨7471350740889052339083923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980900493926034892722615 7471350740889052339083923)
                  ·
                    refine ⟨11207026111333578508625885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471350740889052339083923 11207026111333578508625885)
                    ·
                      refine ⟨4202634791750091940734707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207026111333578508625885 4202634791750091940734707)
                      ·
                        rfl

theorem cell23_8184602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_8184602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184602 prefixEnd_8184602 := by exact prefixLift 8184602
  have htrace : WordTrace (prefixWord ++ tailWord_8184602) baseStart_8184602 baseEnd_8184602 := by
    simpa [prefixWord, tailWord_8184602, baseEnd_8184602] using wordTrace_append hprefix tailTrace_8184602
  have hstable : (prefixWord ++ tailWord_8184602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184602).length < 2 ^ (prefixWord ++ tailWord_8184602).sum := by decide
  have hdescent : baseEnd_8184602 < baseStart_8184602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184611 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 3]
def baseStart_8184611 : Nat := 118140960795 + 8184611 * 2 ^ 59
def prefixEnd_8184611 : Nat := 4983230072969 + 3 ^ 40 * 8184611 * 2
def baseEnd_8184611 : Nat := 4202639413075982405522165

theorem tailTrace_8184611 : CollatzResearch.WordTrace tailWord_8184611 prefixEnd_8184611 4202639413075982405522165 := by
  unfold tailWord_8184611
  simp only [CollatzResearch.WordTrace]
  refine ⟨298517287351559642117753687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199011524901039761411835791 298517287351559642117753687)
  ·
    refine ⟨447775931027339463176630531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298517287351559642117753687 447775931027339463176630531)
    ·
      refine ⟨671663896541009194764945797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447775931027339463176630531 671663896541009194764945797)
      ·
        refine ⟨125936980601439224018427337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 671663896541009194764945797 125936980601439224018427337)
        ·
          refine ⟨94452735451079418013820503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125936980601439224018427337 94452735451079418013820503)
          ·
            refine ⟨141679103176619127020730755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94452735451079418013820503 141679103176619127020730755)
            ·
              refine ⟨212518654764928690531096133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141679103176619127020730755 212518654764928690531096133)
              ·
                refine ⟨39847247768424129474580525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212518654764928690531096133 39847247768424129474580525)
                ·
                  refine ⟨14942717913159048552967697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39847247768424129474580525 14942717913159048552967697)
                  ·
                    refine ⟨11207038434869286414725773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14942717913159048552967697 11207038434869286414725773)
                    ·
                      refine ⟨4202639413075982405522165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207038434869286414725773 4202639413075982405522165)
                      ·
                        rfl

theorem cell23_8184611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_8184611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184611 prefixEnd_8184611 := by exact prefixLift 8184611
  have htrace : WordTrace (prefixWord ++ tailWord_8184611) baseStart_8184611 baseEnd_8184611 := by
    simpa [prefixWord, tailWord_8184611, baseEnd_8184611] using wordTrace_append hprefix tailTrace_8184611
  have hstable : (prefixWord ++ tailWord_8184611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184611).length < 2 ^ (prefixWord ++ tailWord_8184611).sum := by decide
  have hdescent : baseEnd_8184611 < baseStart_8184611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184653 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_8184653 : Nat := 118140960795 + 8184653 * 2 ^ 59
def prefixEnd_8184653 : Nat := 4983230072969 + 3 ^ 40 * 8184653 * 2
def baseEnd_8184653 : Nat := 4202660979263471241196973

theorem tailTrace_8184653 : CollatzResearch.WordTrace tailWord_8184653 prefixEnd_8184653 4202660979263471241196973 := by
  unfold tailWord_8184653
  simp only [CollatzResearch.WordTrace]
  refine ⟨298518819217407483290782613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199012546144938322193855075 298518819217407483290782613)
  ·
    refine ⟨13993069650815975779255435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298518819217407483290782613 13993069650815975779255435)
    ·
      refine ⟨20989604476223963668883153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13993069650815975779255435 20989604476223963668883153)
      ·
        refine ⟨15742203357167972751662365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20989604476223963668883153 15742203357167972751662365)
        ·
          refine ⟨5903326258937989781873387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15742203357167972751662365 5903326258937989781873387)
          ·
            refine ⟨8854989388406984672810081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903326258937989781873387 8854989388406984672810081)
            ·
              refine ⟨6641242041305238504607561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854989388406984672810081 6641242041305238504607561)
              ·
                refine ⟨4980931530978928878455671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6641242041305238504607561 4980931530978928878455671)
                ·
                  refine ⟨7471397296468393317683507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980931530978928878455671 7471397296468393317683507)
                  ·
                    refine ⟨11207095944702589976525261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471397296468393317683507 11207095944702589976525261)
                    ·
                      refine ⟨4202660979263471241196973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207095944702589976525261 4202660979263471241196973)
                      ·
                        rfl

theorem cell23_8184653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_8184653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184653 prefixEnd_8184653 := by exact prefixLift 8184653
  have htrace : WordTrace (prefixWord ++ tailWord_8184653) baseStart_8184653 baseEnd_8184653 := by
    simpa [prefixWord, tailWord_8184653, baseEnd_8184653] using wordTrace_append hprefix tailTrace_8184653
  have hstable : (prefixWord ++ tailWord_8184653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184653).length < 2 ^ (prefixWord ++ tailWord_8184653).sum := by decide
  have hdescent : baseEnd_8184653 < baseStart_8184653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184675 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 3]
def baseStart_8184675 : Nat := 118140960795 + 8184675 * 2 ^ 59
def prefixEnd_8184675 : Nat := 4983230072969 + 3 ^ 40 * 8184675 * 2
def baseEnd_8184675 : Nat := 4202672275837870155121871

theorem tailTrace_8184675 : CollatzResearch.WordTrace tailWord_8184675 prefixEnd_8184675 4202672275837870155121871 := by
  unfold tailWord_8184675
  simp only [CollatzResearch.WordTrace]
  refine ⟨298519621623327781048083479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199013081082218520698722319 298519621623327781048083479)
  ·
    refine ⟨447779432434991671572125219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298519621623327781048083479 447779432434991671572125219)
    ·
      refine ⟨671669148652487507358187829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447779432434991671572125219 671669148652487507358187829)
      ·
        refine ⟨62968982686170703814830109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 671669148652487507358187829 62968982686170703814830109)
        ·
          refine ⟨23613368507314013930561291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62968982686170703814830109 23613368507314013930561291)
          ·
            refine ⟨35420052760971020895841937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23613368507314013930561291 35420052760971020895841937)
            ·
              refine ⟨26565039570728265671881453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35420052760971020895841937 26565039570728265671881453)
              ·
                refine ⟨9961889839023099626955545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26565039570728265671881453 9961889839023099626955545)
                ·
                  refine ⟨7471417379267324720216659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9961889839023099626955545 7471417379267324720216659)
                  ·
                    refine ⟨11207126068900987080324989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471417379267324720216659 11207126068900987080324989)
                    ·
                      refine ⟨4202672275837870155121871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207126068900987080324989 4202672275837870155121871)
                      ·
                        rfl

theorem cell23_8184675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_8184675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184675 prefixEnd_8184675 := by exact prefixLift 8184675
  have htrace : WordTrace (prefixWord ++ tailWord_8184675) baseStart_8184675 baseEnd_8184675 := by
    simpa [prefixWord, tailWord_8184675, baseEnd_8184675] using wordTrace_append hprefix tailTrace_8184675
  have hstable : (prefixWord ++ tailWord_8184675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184675).length < 2 ^ (prefixWord ++ tailWord_8184675).sum := by decide
  have hdescent : baseEnd_8184675 < baseStart_8184675 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184685 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_8184685 : Nat := 118140960795 + 8184685 * 2 ^ 59
def prefixEnd_8184685 : Nat := 4983230072969 + 3 ^ 40 * 8184685 * 2
def baseEnd_8184685 : Nat := 4202677410644415115996825

theorem tailTrace_8184685 : CollatzResearch.WordTrace tailWord_8184685 prefixEnd_8184685 4202677410644415115996825 := by
  unfold tailWord_8184685
  simp only [CollatzResearch.WordTrace]
  refine ⟨298519986353291552755947509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199013324235527701837298339 298519986353291552755947509)
  ·
    refine ⟨27986248720621083070870079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298519986353291552755947509 27986248720621083070870079)
    ·
      refine ⟨41979373080931624606305119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27986248720621083070870079 41979373080931624606305119)
      ·
        refine ⟨62969059621397436909457679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41979373080931624606305119 62969059621397436909457679)
        ·
          refine ⟨94453589432096155364186519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62969059621397436909457679 94453589432096155364186519)
          ·
            refine ⟨141680384148144233046279779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94453589432096155364186519 141680384148144233046279779)
            ·
              refine ⟨212520576222216349569419669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141680384148144233046279779 212520576222216349569419669)
              ·
                refine ⟨9961902010416391386066547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212520576222216349569419669 9961902010416391386066547)
                ·
                  refine ⟨14942853015624587079099821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9961902010416391386066547 14942853015624587079099821)
                  ·
                    refine ⟨5603569880859220154662433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14942853015624587079099821 5603569880859220154662433)
                    ·
                      refine ⟨4202677410644415115996825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603569880859220154662433 4202677410644415115996825)
                      ·
                        rfl

theorem cell23_8184685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_8184685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184685 prefixEnd_8184685 := by exact prefixLift 8184685
  have htrace : WordTrace (prefixWord ++ tailWord_8184685) baseStart_8184685 baseEnd_8184685 := by
    simpa [prefixWord, tailWord_8184685, baseEnd_8184685] using wordTrace_append hprefix tailTrace_8184685
  have hstable : (prefixWord ++ tailWord_8184685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184685).length < 2 ^ (prefixWord ++ tailWord_8184685).sum := by decide
  have hdescent : baseEnd_8184685 < baseStart_8184685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184701 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_8184701 : Nat := 118140960795 + 8184701 * 2 ^ 59
def prefixEnd_8184701 : Nat := 4983230072969 + 3 ^ 40 * 8184701 * 2
def baseEnd_8184701 : Nat := 4202685626334887053396751

theorem tailTrace_8184701 : CollatzResearch.WordTrace tailWord_8184701 prefixEnd_8184701 4202685626334887053396751 := by
  unfold tailWord_8184701
  simp only [CollatzResearch.WordTrace]
  refine ⟨298520569921233587488529957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199013713280822391659019971 298520569921233587488529957)
  ·
    refine ⟨55972606860231297654099367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298520569921233587488529957 55972606860231297654099367)
    ·
      refine ⟨83958910290346946481149051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55972606860231297654099367 83958910290346946481149051)
      ·
        refine ⟨125938365435520419721723577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83958910290346946481149051 125938365435520419721723577)
        ·
          refine ⟨94453774076640314791292683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125938365435520419721723577 94453774076640314791292683)
          ·
            refine ⟨141680661114960472186939025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94453774076640314791292683 141680661114960472186939025)
            ·
              refine ⟨106260495836220354140204269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141680661114960472186939025 106260495836220354140204269)
              ·
                refine ⟨39847685938582632802576601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106260495836220354140204269 39847685938582632802576601)
                ·
                  refine ⟨29885764453936974601932451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39847685938582632802576601 29885764453936974601932451)
                  ·
                    refine ⟨44828646680905461902898677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29885764453936974601932451 44828646680905461902898677)
                    ·
                      refine ⟨4202685626334887053396751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44828646680905461902898677 4202685626334887053396751)
                      ·
                        rfl

theorem cell23_8184701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_8184701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184701 prefixEnd_8184701 := by exact prefixLift 8184701
  have htrace : WordTrace (prefixWord ++ tailWord_8184701) baseStart_8184701 baseEnd_8184701 := by
    simpa [prefixWord, tailWord_8184701, baseEnd_8184701] using wordTrace_append hprefix tailTrace_8184701
  have hstable : (prefixWord ++ tailWord_8184701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184701).length < 2 ^ (prefixWord ++ tailWord_8184701).sum := by decide
  have hdescent : baseEnd_8184701 < baseStart_8184701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184738 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_8184738 : Nat := 118140960795 + 8184738 * 2 ^ 59
def prefixEnd_8184738 : Nat := 4983230072969 + 3 ^ 40 * 8184738 * 2
def baseEnd_8184738 : Nat := 466967180568789267626009

theorem tailTrace_8184738 : CollatzResearch.WordTrace tailWord_8184738 prefixEnd_8184738 466967180568789267626009 := by
  unfold tailWord_8184738
  simp only [CollatzResearch.WordTrace]
  refine ⟨74630479855524885701906717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199014612948066361871751245 74630479855524885701906717)
  ·
    refine ⟨27986429945821832138215019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74630479855524885701906717 27986429945821832138215019)
    ·
      refine ⟨41979644918732748207322529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27986429945821832138215019 41979644918732748207322529)
      ·
        refine ⟨31484733689049561155491897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41979644918732748207322529 31484733689049561155491897)
        ·
          refine ⟨23613550266787170866618923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31484733689049561155491897 23613550266787170866618923)
          ·
            refine ⟨35420325400180756299928385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23613550266787170866618923 35420325400180756299928385)
            ·
              refine ⟨26565244050135567224946289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35420325400180756299928385 26565244050135567224946289)
              ·
                refine ⟨19923933037601675418709717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26565244050135567224946289 19923933037601675418709717)
                ·
                  refine ⟨466967180568789267626009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19923933037601675418709717 466967180568789267626009)
                  ·
                    rfl

theorem cell23_8184738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_8184738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184738 prefixEnd_8184738 := by exact prefixLift 8184738
  have htrace : WordTrace (prefixWord ++ tailWord_8184738) baseStart_8184738 baseEnd_8184738 := by
    simpa [prefixWord, tailWord_8184738, baseEnd_8184738] using wordTrace_append hprefix tailTrace_8184738
  have hstable : (prefixWord ++ tailWord_8184738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184738).length < 2 ^ (prefixWord ++ tailWord_8184738).sum := by decide
  have hdescent : baseEnd_8184738 < baseStart_8184738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184768 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_8184768 : Nat := 118140960795 + 8184768 * 2 ^ 59
def prefixEnd_8184768 : Nat := 4983230072969 + 3 ^ 40 * 8184768 * 2
def baseEnd_8184768 : Nat := 1400906676512912763752981

theorem tailTrace_8184768 : CollatzResearch.WordTrace tailWord_8184768 prefixEnd_8184768 1400906676512912763752981 := by
  unfold tailWord_8184768
  simp only [CollatzResearch.WordTrace]
  refine ⟨149261506805995428965609479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199015342407993905287479305 149261506805995428965609479)
  ·
    refine ⟨223892260208993143448414219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149261506805995428965609479 223892260208993143448414219)
    ·
      refine ⟨335838390313489715172621329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223892260208993143448414219 335838390313489715172621329)
      ·
        refine ⟨251878792735117286379465997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335838390313489715172621329 251878792735117286379465997)
        ·
          refine ⟨94454547275668982392299749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251878792735117286379465997 94454547275668982392299749)
          ·
            refine ⟨17710227614187934198556203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94454547275668982392299749 17710227614187934198556203)
            ·
              refine ⟨26565341421281901297834305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17710227614187934198556203 26565341421281901297834305)
              ·
                refine ⟨19924006065961425973375729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26565341421281901297834305 19924006065961425973375729)
                ·
                  refine ⟨14943004549471069480031797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19924006065961425973375729 14943004549471069480031797)
                  ·
                    refine ⟨1400906676512912763752981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14943004549471069480031797 1400906676512912763752981)
                    ·
                      rfl

theorem cell23_8184768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_8184768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184768 prefixEnd_8184768 := by exact prefixLift 8184768
  have htrace : WordTrace (prefixWord ++ tailWord_8184768) baseStart_8184768 baseEnd_8184768 := by
    simpa [prefixWord, tailWord_8184768, baseEnd_8184768] using wordTrace_append hprefix tailTrace_8184768
  have hstable : (prefixWord ++ tailWord_8184768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184768).length < 2 ^ (prefixWord ++ tailWord_8184768).sum := by decide
  have hdescent : baseEnd_8184768 < baseStart_8184768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184772 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 7]
def baseStart_8184772 : Nat := 118140960795 + 8184772 * 2 ^ 59
def prefixEnd_8184772 : Nat := 4983230072969 + 3 ^ 40 * 8184772 * 2
def baseEnd_8184772 : Nat := 466969120384595141734325

theorem tailTrace_8184772 : CollatzResearch.WordTrace tailWord_8184772 prefixEnd_8184772 466969120384595141734325 := by
  unfold tailWord_8184772
  simp only [CollatzResearch.WordTrace]
  refine ⟨149261579751988183307182285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199015439669317577742909713 149261579751988183307182285)
  ·
    refine ⟨55973092406995568740193357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149261579751988183307182285 55973092406995568740193357)
    ·
      refine ⟨20989909652623338277572509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55973092406995568740193357 20989909652623338277572509)
      ·
        refine ⟨7871216119733751854089691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20989909652623338277572509 7871216119733751854089691)
        ·
          refine ⟨11806824179600627781134537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871216119733751854089691 11806824179600627781134537)
          ·
            refine ⟨8855118134700470835850903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11806824179600627781134537 8855118134700470835850903)
            ·
              refine ⟨13282677202050706253776355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855118134700470835850903 13282677202050706253776355)
              ·
                refine ⟨19924015803076059380664533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13282677202050706253776355 19924015803076059380664533)
                ·
                  refine ⟨466969120384595141734325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19924015803076059380664533 466969120384595141734325)
                  ·
                    rfl

theorem cell23_8184772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_8184772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184772 prefixEnd_8184772 := by exact prefixLift 8184772
  have htrace : WordTrace (prefixWord ++ tailWord_8184772) baseStart_8184772 baseEnd_8184772 := by
    simpa [prefixWord, tailWord_8184772, baseEnd_8184772] using wordTrace_append hprefix tailTrace_8184772
  have hstable : (prefixWord ++ tailWord_8184772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184772).length < 2 ^ (prefixWord ++ tailWord_8184772).sum := by decide
  have hdescent : baseEnd_8184772 < baseStart_8184772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184801 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_8184801 : Nat := 118140960795 + 8184801 * 2 ^ 59
def prefixEnd_8184801 : Nat := 4983230072969 + 3 ^ 40 * 8184801 * 2
def baseEnd_8184801 : Nat := 4202736974400336662146291

theorem tailTrace_8184801 : CollatzResearch.WordTrace tailWord_8184801 prefixEnd_8184801 4202736974400336662146291 := by
  unfold tailWord_8184801
  simp only [CollatzResearch.WordTrace]
  refine ⟨298524217220871304567170257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199016144813914203044780171 298524217220871304567170257)
  ·
    refine ⟨223893162915653478425377693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298524217220871304567170257 223893162915653478425377693)
    ·
      refine ⟨83959936093370054409516635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223893162915653478425377693 83959936093370054409516635)
      ·
        refine ⟨125939904140055081614274953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83959936093370054409516635 125939904140055081614274953)
        ·
          refine ⟨94454928105041311210706215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125939904140055081614274953 94454928105041311210706215)
          ·
            refine ⟨141682392157561966816059323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94454928105041311210706215 141682392157561966816059323)
            ·
              refine ⟨212523588236342950224088985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141682392157561966816059323 212523588236342950224088985)
              ·
                refine ⟨159392691177257212668066739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212523588236342950224088985 159392691177257212668066739)
                ·
                  refine ⟨239089036765885819002100109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159392691177257212668066739 239089036765885819002100109)
                  ·
                    refine ⟨89658388787207182125787541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239089036765885819002100109 89658388787207182125787541)
                    ·
                      refine ⟨4202736974400336662146291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89658388787207182125787541 4202736974400336662146291)
                      ·
                        rfl

theorem cell23_8184801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_8184801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184801 prefixEnd_8184801 := by exact prefixLift 8184801
  have htrace : WordTrace (prefixWord ++ tailWord_8184801) baseStart_8184801 baseEnd_8184801 := by
    simpa [prefixWord, tailWord_8184801, baseEnd_8184801] using wordTrace_append hprefix tailTrace_8184801
  have hstable : (prefixWord ++ tailWord_8184801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184801).length < 2 ^ (prefixWord ++ tailWord_8184801).sum := by decide
  have hdescent : baseEnd_8184801 < baseStart_8184801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184802 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_8184802 : Nat := 118140960795 + 8184802 * 2 ^ 59
def prefixEnd_8184802 : Nat := 4983230072969 + 3 ^ 40 * 8184802 * 2
def baseEnd_8184802 : Nat := 1400912495960330386077929

theorem tailTrace_8184802 : CollatzResearch.WordTrace tailWord_8184802 prefixEnd_8184802 1400912495960330386077929 := by
  unfold tailWord_8184802
  simp only [CollatzResearch.WordTrace]
  refine ⟨74631063423466920434489165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199016169129245121158637773 74631063423466920434489165)
  ·
    refine ⟨27986648783800095162933437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74631063423466920434489165 27986648783800095162933437)
    ·
      refine ⟨10494993293925035686100039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27986648783800095162933437 10494993293925035686100039)
      ·
        refine ⟨15742489940887553529150059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494993293925035686100039 15742489940887553529150059)
        ·
          refine ⟨23613734911331330293725089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15742489940887553529150059 23613734911331330293725089)
          ·
            refine ⟨17710301183498497720293817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23613734911331330293725089 17710301183498497720293817)
            ·
              refine ⟨13282725887623873290220363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17710301183498497720293817 13282725887623873290220363)
              ·
                refine ⟨19924088831435809935330545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13282725887623873290220363 19924088831435809935330545)
                ·
                  refine ⟨14943066623576857451497909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19924088831435809935330545 14943066623576857451497909)
                  ·
                    refine ⟨1400912495960330386077929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14943066623576857451497909 1400912495960330386077929)
                    ·
                      rfl

theorem cell23_8184802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_8184802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184802 prefixEnd_8184802 := by exact prefixLift 8184802
  have htrace : WordTrace (prefixWord ++ tailWord_8184802) baseStart_8184802 baseEnd_8184802 := by
    simpa [prefixWord, tailWord_8184802, baseEnd_8184802] using wordTrace_append hprefix tailTrace_8184802
  have hstable : (prefixWord ++ tailWord_8184802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184802).length < 2 ^ (prefixWord ++ tailWord_8184802).sum := by decide
  have hdescent : baseEnd_8184802 < baseStart_8184802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184808 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_8184808 : Nat := 118140960795 + 8184808 * 2 ^ 59
def prefixEnd_8184808 : Nat := 4983230072969 + 3 ^ 40 * 8184808 * 2
def baseEnd_8184808 : Nat := 4202740568764918134758759

theorem tailTrace_8184808 : CollatzResearch.WordTrace tailWord_8184808 prefixEnd_8184808 4202740568764918134758759 := by
  unfold tailWord_8184808
  simp only [CollatzResearch.WordTrace]
  refine ⟨149262236265922972381337539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199016315021230629841783385 149262236265922972381337539)
  ·
    refine ⟨223893354398884458572006309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149262236265922972381337539 223893354398884458572006309)
    ·
      refine ⟨41980003949790835982251183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223893354398884458572006309 41980003949790835982251183)
      ·
        refine ⟨62970005924686253973376775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41980003949790835982251183 62970005924686253973376775)
        ·
          refine ⟨94455008887029380960065163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62970005924686253973376775 94455008887029380960065163)
          ·
            refine ⟨141682513330544071440097745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94455008887029380960065163 141682513330544071440097745)
            ·
              refine ⟨106261884997908053580073309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141682513330544071440097745 106261884997908053580073309)
              ·
                refine ⟨39848206874215520092527491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106261884997908053580073309 39848206874215520092527491)
                ·
                  refine ⟨59772310311323280138791237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39848206874215520092527491 59772310311323280138791237)
                  ·
                    refine ⟨11207308183373115026023357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59772310311323280138791237 11207308183373115026023357)
                    ·
                      refine ⟨4202740568764918134758759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207308183373115026023357 4202740568764918134758759)
                      ·
                        rfl

theorem cell23_8184808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_8184808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184808 prefixEnd_8184808 := by exact prefixLift 8184808
  have htrace : WordTrace (prefixWord ++ tailWord_8184808) baseStart_8184808 baseEnd_8184808 := by
    simpa [prefixWord, tailWord_8184808, baseEnd_8184808] using wordTrace_append hprefix tailTrace_8184808
  have hstable : (prefixWord ++ tailWord_8184808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184808).length < 2 ^ (prefixWord ++ tailWord_8184808).sum := by decide
  have hdescent : baseEnd_8184808 < baseStart_8184808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184828 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 6]
def baseStart_8184828 : Nat := 118140960795 + 8184828 * 2 ^ 59
def prefixEnd_8184828 : Nat := 4983230072969 + 3 ^ 40 * 8184828 * 2
def baseEnd_8184828 : Nat := 466972315375334228500963

theorem tailTrace_8184828 : CollatzResearch.WordTrace tailWord_8184828 prefixEnd_8184828 466972315375334228500963 := by
  unfold tailWord_8184828
  simp only [CollatzResearch.WordTrace]
  refine ⟨149262600995886744089201569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199016801327848992118935425 149262600995886744089201569)
  ·
    refine ⟨111946950746915058066901177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149262600995886744089201569 111946950746915058066901177)
    ·
      refine ⟨83960213060186293550175883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111946950746915058066901177 83960213060186293550175883)
      ·
        refine ⟨125940319590279440325263825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83960213060186293550175883 125940319590279440325263825)
        ·
          refine ⟨94455239692709580243947869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125940319590279440325263825 94455239692709580243947869)
          ·
            refine ⟨35420714884766092591480451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94455239692709580243947869 35420714884766092591480451)
            ·
              refine ⟨53131072327149138887220677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35420714884766092591480451 53131072327149138887220677)
              ·
                refine ⟨9962076061340463541353877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53131072327149138887220677 9962076061340463541353877)
                ·
                  refine ⟨466972315375334228500963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9962076061340463541353877 466972315375334228500963)
                  ·
                    rfl

theorem cell23_8184828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_8184828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184828 prefixEnd_8184828 := by exact prefixLift 8184828
  have htrace : WordTrace (prefixWord ++ tailWord_8184828) baseStart_8184828 baseEnd_8184828 := by
    simpa [prefixWord, tailWord_8184828, baseEnd_8184828] using wordTrace_append hprefix tailTrace_8184828
  have hstable : (prefixWord ++ tailWord_8184828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184828).length < 2 ^ (prefixWord ++ tailWord_8184828).sum := by decide
  have hdescent : baseEnd_8184828 < baseStart_8184828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184851 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_8184851 : Nat := 118140960795 + 8184851 * 2 ^ 59
def prefixEnd_8184851 : Nat := 4983230072969 + 3 ^ 40 * 8184851 * 2
def baseEnd_8184851 : Nat := 4202762648433061466521061

theorem tailTrace_8184851 : CollatzResearch.WordTrace tailWord_8184851 prefixEnd_8184851 4202762648433061466521061 := by
  unfold tailWord_8184851
  simp only [CollatzResearch.WordTrace]
  refine ⟨298526040870690163106490407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199017360580460108737660271 298526040870690163106490407)
  ·
    refine ⟨447789061306035244659735611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298526040870690163106490407 447789061306035244659735611)
    ·
      refine ⟨671683591959052866989603417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447789061306035244659735611 671683591959052866989603417)
      ·
        refine ⟨503762693969289650242202563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671683591959052866989603417 503762693969289650242202563)
        ·
          refine ⟨755644040953934475363303845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503762693969289650242202563 755644040953934475363303845)
          ·
            refine ⟨141683257678862714130619471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 755644040953934475363303845 141683257678862714130619471)
            ·
              refine ⟨212524886518294071195929207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141683257678862714130619471 212524886518294071195929207)
              ·
                refine ⟨318787329777441106793893811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212524886518294071195929207 318787329777441106793893811)
                ·
                  refine ⟨478180994666161660190840717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318787329777441106793893811 478180994666161660190840717)
                  ·
                    refine ⟨179317872999810622571565269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 478180994666161660190840717 179317872999810622571565269)
                    ·
                      refine ⟨4202762648433061466521061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179317872999810622571565269 4202762648433061466521061)
                      ·
                        rfl

theorem cell23_8184851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_8184851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184851 prefixEnd_8184851 := by exact prefixLift 8184851
  have htrace : WordTrace (prefixWord ++ tailWord_8184851) baseStart_8184851 baseEnd_8184851 := by
    simpa [prefixWord, tailWord_8184851, baseEnd_8184851] using wordTrace_append hprefix tailTrace_8184851
  have hstable : (prefixWord ++ tailWord_8184851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184851).length < 2 ^ (prefixWord ++ tailWord_8184851).sum := by decide
  have hdescent : baseEnd_8184851 < baseStart_8184851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184858 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_8184858 : Nat := 118140960795 + 8184858 * 2 ^ 59
def prefixEnd_8184858 : Nat := 4983230072969 + 3 ^ 40 * 8184858 * 2
def baseEnd_8184858 : Nat := 1400922080932547646377843

theorem tailTrace_8184858 : CollatzResearch.WordTrace tailWord_8184858 prefixEnd_8184858 1400922080932547646377843 := by
  unfold tailWord_8184858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74631574045416200825498807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199017530787776535534663485 74631574045416200825498807)
  ·
    refine ⟨111947361068124301238248211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74631574045416200825498807 111947361068124301238248211)
    ·
      refine ⟨167921041602186451857372317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111947361068124301238248211 167921041602186451857372317)
      ·
        refine ⟨62970390600819919446514619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167921041602186451857372317 62970390600819919446514619)
        ·
          refine ⟨94455585901229879169771929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62970390600819919446514619 94455585901229879169771929)
          ·
            refine ⟨70841689425922409377328947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94455585901229879169771929 70841689425922409377328947)
            ·
              refine ⟨106262534138883614065993421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70841689425922409377328947 106262534138883614065993421)
              ·
                refine ⟨39848450302081355274747533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106262534138883614065993421 39848450302081355274747533)
                ·
                  refine ⟨14943168863280508228030325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39848450302081355274747533 14943168863280508228030325)
                  ·
                    refine ⟨1400922080932547646377843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14943168863280508228030325 1400922080932547646377843)
                    ·
                      rfl

theorem cell23_8184858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_8184858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184858 prefixEnd_8184858 := by exact prefixLift 8184858
  have htrace : WordTrace (prefixWord ++ tailWord_8184858) baseStart_8184858 baseEnd_8184858 := by
    simpa [prefixWord, tailWord_8184858, baseEnd_8184858] using wordTrace_append hprefix tailTrace_8184858
  have hstable : (prefixWord ++ tailWord_8184858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184858).length < 2 ^ (prefixWord ++ tailWord_8184858).sum := by decide
  have hdescent : baseEnd_8184858 < baseStart_8184858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184889 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 1, 1, 3]
def baseStart_8184889 : Nat := 118140960795 + 8184889 * 2 ^ 59
def prefixEnd_8184889 : Nat := 4983230072969 + 3 ^ 40 * 8184889 * 2
def baseEnd_8184889 : Nat := 4202782160697932317845887

theorem tailTrace_8184889 : CollatzResearch.WordTrace tailWord_8184889 prefixEnd_8184889 4202782160697932317845887 := by
  unfold tailWord_8184889
  simp only [CollatzResearch.WordTrace]
  refine ⟨298527426844552495596373721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199018284563034997064249147 298527426844552495596373721)
  ·
    refine ⟨223895570133414371697280291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298527426844552495596373721 223895570133414371697280291)
    ·
      refine ⟨335843355200121557545920437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223895570133414371697280291 335843355200121557545920437)
      ·
        refine ⟨31485314550011396019930041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335843355200121557545920437 31485314550011396019930041)
        ·
          refine ⟨23613985912508547014947531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31485314550011396019930041 23613985912508547014947531)
          ·
            refine ⟨35420978868762820522421297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23613985912508547014947531 35420978868762820522421297)
            ·
              refine ⟨26565734151572115391815973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35420978868762820522421297 26565734151572115391815973)
              ·
                refine ⟨4981075153419771635965495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26565734151572115391815973 4981075153419771635965495)
                ·
                  refine ⟨7471612730129657453948243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981075153419771635965495 7471612730129657453948243)
                  ·
                    refine ⟨11207419095194486180922365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471612730129657453948243 11207419095194486180922365)
                    ·
                      refine ⟨4202782160697932317845887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207419095194486180922365 4202782160697932317845887)
                      ·
                        rfl

theorem cell23_8184889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_8184889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184889 prefixEnd_8184889 := by exact prefixLift 8184889
  have htrace : WordTrace (prefixWord ++ tailWord_8184889) baseStart_8184889 baseEnd_8184889 := by
    simpa [prefixWord, tailWord_8184889, baseEnd_8184889] using wordTrace_append hprefix tailTrace_8184889
  have hstable : (prefixWord ++ tailWord_8184889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184889).length < 2 ^ (prefixWord ++ tailWord_8184889).sum := by decide
  have hdescent : baseEnd_8184889 < baseStart_8184889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8184915 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 3]
def baseStart_8184915 : Nat := 118140960795 + 8184915 * 2 ^ 59
def prefixEnd_8184915 : Nat := 4983230072969 + 3 ^ 40 * 8184915 * 2
def baseEnd_8184915 : Nat := 4202795511194949216120767

theorem tailTrace_8184915 : CollatzResearch.WordTrace tailWord_8184915 prefixEnd_8184915 4202795511194949216120767 := by
  unfold tailWord_8184915
  simp only [CollatzResearch.WordTrace]
  refine ⟨298528375142458302036820199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199018916761638868024546799 298528375142458302036820199)
  ·
    refine ⟨447792562713687453055230299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298528375142458302036820199 447792562713687453055230299)
    ·
      refine ⟨671688844070531179582845449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447792562713687453055230299 671688844070531179582845449)
      ·
        refine ⟨503766633052898384687134087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671688844070531179582845449 503766633052898384687134087)
        ·
          refine ⟨755649949579347577030701131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503766633052898384687134087 755649949579347577030701131)
          ·
            refine ⟨1133474924369021365546051697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755649949579347577030701131 1133474924369021365546051697)
            ·
              refine ⟨850106193276766024159538773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133474924369021365546051697 850106193276766024159538773)
              ·
                refine ⟨9962181952462101845619595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 850106193276766024159538773 9962181952462101845619595)
                ·
                  refine ⟨14943272928693152768429393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9962181952462101845619595 14943272928693152768429393)
                  ·
                    refine ⟨11207454696519864576322045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14943272928693152768429393 11207454696519864576322045)
                    ·
                      refine ⟨4202795511194949216120767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207454696519864576322045 4202795511194949216120767)
                      ·
                        rfl

theorem cell23_8184915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_8184915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8184915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8184915 prefixEnd_8184915 := by exact prefixLift 8184915
  have htrace : WordTrace (prefixWord ++ tailWord_8184915) baseStart_8184915 baseEnd_8184915 := by
    simpa [prefixWord, tailWord_8184915, baseEnd_8184915] using wordTrace_append hprefix tailTrace_8184915
  have hstable : (prefixWord ++ tailWord_8184915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8184915).length < 2 ^ (prefixWord ++ tailWord_8184915).sum := by decide
  have hdescent : baseEnd_8184915 < baseStart_8184915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8184915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185002 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_8185002 : Nat := 118140960795 + 8185002 * 2 ^ 59
def prefixEnd_8185002 : Nat := 4983230072969 + 3 ^ 40 * 8185002 * 2
def baseEnd_8185002 : Nat := 4202840184011890375732867

theorem tailTrace_8185002 : CollatzResearch.WordTrace tailWord_8185002 prefixEnd_8185002 4202840184011890375732867 := by
  unfold tailWord_8185002
  simp only [CollatzResearch.WordTrace]
  refine ⟨74632887073285778973809315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199021032195428743930158173 74632887073285778973809315)
  ·
    refine ⟨111949330609928668460713973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74632887073285778973809315 111949330609928668460713973)
    ·
      refine ⟨10495249744680812668191935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111949330609928668460713973 10495249744680812668191935)
      ·
        refine ⟨15742874617021219002287903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495249744680812668191935 15742874617021219002287903)
        ·
          refine ⟨23614311925531828503431855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15742874617021219002287903 23614311925531828503431855)
          ·
            refine ⟨35421467888297742755147783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23614311925531828503431855 35421467888297742755147783)
            ·
              refine ⟨53132201832446614132721675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35421467888297742755147783 53132201832446614132721675)
              ·
                refine ⟨79698302748669921199082513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53132201832446614132721675 79698302748669921199082513)
                ·
                  refine ⟨59773727061502440899311885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79698302748669921199082513 59773727061502440899311885)
                  ·
                    refine ⟨22415147648063415337241957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59773727061502440899311885 22415147648063415337241957)
                    ·
                      refine ⟨4202840184011890375732867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22415147648063415337241957 4202840184011890375732867)
                      ·
                        rfl

theorem cell23_8185002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_8185002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185002 prefixEnd_8185002 := by exact prefixLift 8185002
  have htrace : WordTrace (prefixWord ++ tailWord_8185002) baseStart_8185002 baseEnd_8185002 := by
    simpa [prefixWord, tailWord_8185002, baseEnd_8185002] using wordTrace_append hprefix tailTrace_8185002
  have hstable : (prefixWord ++ tailWord_8185002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185002).length < 2 ^ (prefixWord ++ tailWord_8185002).sum := by decide
  have hdescent : baseEnd_8185002 < baseStart_8185002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185015 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_8185015 : Nat := 118140960795 + 8185015 * 2 ^ 59
def prefixEnd_8185015 : Nat := 4983230072969 + 3 ^ 40 * 8185015 * 2
def baseEnd_8185015 : Nat := 4202846859260398824870307

theorem tailTrace_8185015 : CollatzResearch.WordTrace tailWord_8185015 prefixEnd_8185015 4202846859260398824870307 := by
  unfold tailWord_8185015
  simp only [CollatzResearch.WordTrace]
  refine ⟨298532022442096019115460499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199021348294730679410306999 298532022442096019115460499)
  ·
    refine ⟨447798033663144028673190749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298532022442096019115460499 447798033663144028673190749)
    ·
      refine ⟨167924262623679010752446531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447798033663144028673190749 167924262623679010752446531)
      ·
        refine ⟨251886393935518516128669797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167924262623679010752446531 251886393935518516128669797)
        ·
          refine ⟨47228698862909721774125587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251886393935518516128669797 47228698862909721774125587)
          ·
            refine ⟨70843048294364582661188381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47228698862909721774125587 70843048294364582661188381)
            ·
              refine ⟨26566143110386718497945643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70843048294364582661188381 26566143110386718497945643)
              ·
                refine ⟨39849214665580077746918465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26566143110386718497945643 39849214665580077746918465)
                ·
                  refine ⟨29886910999185058310188849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39849214665580077746918465 29886910999185058310188849)
                  ·
                    refine ⟨22415183249388793732641637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29886910999185058310188849 22415183249388793732641637)
                    ·
                      refine ⟨4202846859260398824870307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22415183249388793732641637 4202846859260398824870307)
                      ·
                        rfl

theorem cell23_8185015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_8185015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185015 prefixEnd_8185015 := by exact prefixLift 8185015
  have htrace : WordTrace (prefixWord ++ tailWord_8185015) baseStart_8185015 baseEnd_8185015 := by
    simpa [prefixWord, tailWord_8185015, baseEnd_8185015] using wordTrace_append hprefix tailTrace_8185015
  have hstable : (prefixWord ++ tailWord_8185015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185015).length < 2 ^ (prefixWord ++ tailWord_8185015).sum := by decide
  have hdescent : baseEnd_8185015 < baseStart_8185015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185055 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 2, 5]
def baseStart_8185055 : Nat := 118140960795 + 8185055 * 2 ^ 59
def prefixEnd_8185055 : Nat := 4983230072969 + 3 ^ 40 * 8185055 * 2
def baseEnd_8185055 : Nat := 1400955799495526222790041

theorem tailTrace_8185055 : CollatzResearch.WordTrace tailWord_8185055 prefixEnd_8185055 1400955799495526222790041 := by
  unfold tailWord_8185055
  simp only [CollatzResearch.WordTrace]
  refine ⟨298533481361951105946916619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199022320907967403964611079 298533481361951105946916619)
  ·
    refine ⟨447800222042926658920374929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298533481361951105946916619 447800222042926658920374929)
    ·
      refine ⟨335850166532194994190281197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447800222042926658920374929 335850166532194994190281197)
      ·
        refine ⟨125943812449573122821355449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335850166532194994190281197 125943812449573122821355449)
        ·
          refine ⟨94457859337179842116016587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125943812449573122821355449 94457859337179842116016587)
          ·
            refine ⟨141686789005769763174024881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94457859337179842116016587 141686789005769763174024881)
            ·
              refine ⟨106265091754327322380518661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141686789005769763174024881 106265091754327322380518661)
              ·
                refine ⟨19924704703936372946347249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106265091754327322380518661 19924704703936372946347249)
                ·
                  refine ⟨14943528527952279709760437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19924704703936372946347249 14943528527952279709760437)
                  ·
                    refine ⟨1400955799495526222790041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14943528527952279709760437 1400955799495526222790041)
                    ·
                      rfl

theorem cell23_8185055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_8185055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185055 prefixEnd_8185055 := by exact prefixLift 8185055
  have htrace : WordTrace (prefixWord ++ tailWord_8185055) baseStart_8185055 baseEnd_8185055 := by
    simpa [prefixWord, tailWord_8185055, baseEnd_8185055] using wordTrace_append hprefix tailTrace_8185055
  have hstable : (prefixWord ++ tailWord_8185055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185055).length < 2 ^ (prefixWord ++ tailWord_8185055).sum := by decide
  have hdescent : baseEnd_8185055 < baseStart_8185055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185075 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4]
def baseStart_8185075 : Nat := 118140960795 + 8185075 * 2 ^ 59
def prefixEnd_8185075 : Nat := 4983230072969 + 3 ^ 40 * 8185075 * 2
def baseEnd_8185075 : Nat := 4202877668099668590120031

theorem tailTrace_8185075 : CollatzResearch.WordTrace tailWord_8185075 prefixEnd_8185075 4202877668099668590120031 := by
  unfold tailWord_8185075
  simp only [CollatzResearch.WordTrace]
  refine ⟨298534210821878649362644679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199022807214585766241763119 298534210821878649362644679)
  ·
    refine ⟨447801316232817974043967019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298534210821878649362644679 447801316232817974043967019)
    ·
      refine ⟨671701974349226961065950529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447801316232817974043967019 671701974349226961065950529)
      ·
        refine ⟨503776480761920220799462897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671701974349226961065950529 503776480761920220799462897)
        ·
          refine ⟨377832360571440165599597173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503776480761920220799462897 377832360571440165599597173)
          ·
            refine ⟨35421783803572515524962235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377832360571440165599597173 35421783803572515524962235)
            ·
              refine ⟨53132675705358773287443353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35421783803572515524962235 53132675705358773287443353)
              ·
                refine ⟨39849506779019079965582515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53132675705358773287443353 39849506779019079965582515)
                ·
                  refine ⟨59774260168528619948373773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39849506779019079965582515 59774260168528619948373773)
                  ·
                    refine ⟨22415347563198232480640165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59774260168528619948373773 22415347563198232480640165)
                    ·
                      refine ⟨4202877668099668590120031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22415347563198232480640165 4202877668099668590120031)
                      ·
                        rfl

theorem cell23_8185075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_8185075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185075 prefixEnd_8185075 := by exact prefixLift 8185075
  have htrace : WordTrace (prefixWord ++ tailWord_8185075) baseStart_8185075 baseEnd_8185075 := by
    simpa [prefixWord, tailWord_8185075, baseEnd_8185075] using wordTrace_append hprefix tailTrace_8185075
  have hstable : (prefixWord ++ tailWord_8185075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185075).length < 2 ^ (prefixWord ++ tailWord_8185075).sum := by decide
  have hdescent : baseEnd_8185075 < baseStart_8185075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185092 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_8185092 : Nat := 118140960795 + 8185092 * 2 ^ 59
def prefixEnd_8185092 : Nat := 4983230072969 + 3 ^ 40 * 8185092 * 2
def baseEnd_8185092 : Nat := 4202886397270795023607453

theorem tailTrace_8185092 : CollatzResearch.WordTrace tailWord_8185092 prefixEnd_8185092 4202886397270795023607453 := by
  unfold tailWord_8185092
  simp only [CollatzResearch.WordTrace]
  refine ⟨149267415431408530633006765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199023220575211374177342353 149267415431408530633006765)
  ·
    refine ⟨55975280786778198987377537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149267415431408530633006765 55975280786778198987377537)
    ·
      refine ⟨41981460590083649240533153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55975280786778198987377537 41981460590083649240533153)
      ·
        refine ⟨31486095442562736930399865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41981460590083649240533153 31486095442562736930399865)
        ·
          refine ⟨23614571581922052697799899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31486095442562736930399865 23614571581922052697799899)
          ·
            refine ⟨35421857372883079046699849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23614571581922052697799899 35421857372883079046699849)
            ·
              refine ⟨26566393029662309285024887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35421857372883079046699849 26566393029662309285024887)
              ·
                refine ⟨39849589544493463927537331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26566393029662309285024887 39849589544493463927537331)
                ·
                  refine ⟨59774384316740195891305997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39849589544493463927537331 59774384316740195891305997)
                  ·
                    refine ⟨22415394118777573459239749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59774384316740195891305997 22415394118777573459239749)
                    ·
                      refine ⟨4202886397270795023607453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22415394118777573459239749 4202886397270795023607453)
                      ·
                        rfl

theorem cell23_8185092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_8185092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185092 prefixEnd_8185092 := by exact prefixLift 8185092
  have htrace : WordTrace (prefixWord ++ tailWord_8185092) baseStart_8185092 baseEnd_8185092 := by
    simpa [prefixWord, tailWord_8185092, baseEnd_8185092] using wordTrace_append hprefix tailTrace_8185092
  have hstable : (prefixWord ++ tailWord_8185092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185092).length < 2 ^ (prefixWord ++ tailWord_8185092).sum := by decide
  have hdescent : baseEnd_8185092 < baseStart_8185092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185106 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_8185106 : Nat := 118140960795 + 8185106 * 2 ^ 59
def prefixEnd_8185106 : Nat := 4983230072969 + 3 ^ 40 * 8185106 * 2
def baseEnd_8185106 : Nat := 1400964528666652656277463

theorem tailTrace_8185106 : CollatzResearch.WordTrace tailWord_8185106 prefixEnd_8185106 1400964528666652656277463 := by
  unfold tailWord_8185106
  simp only [CollatzResearch.WordTrace]
  refine ⟨74633835371191585414255793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199023560989844227771348781 74633835371191585414255793)
  ·
    refine ⟨55975376528393689060691845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74633835371191585414255793 55975376528393689060691845)
    ·
      refine ⟨10495383099073816698879721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55975376528393689060691845 10495383099073816698879721)
      ·
        refine ⟨7871537324305362524159791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10495383099073816698879721 7871537324305362524159791)
        ·
          refine ⟨11807305986458043786239687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871537324305362524159791 11807305986458043786239687)
          ·
            refine ⟨17710958979687065679359531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807305986458043786239687 17710958979687065679359531)
            ·
              refine ⟨26566438469530598519039297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17710958979687065679359531 26566438469530598519039297)
              ·
                refine ⟨19924828852147948889279473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26566438469530598519039297 19924828852147948889279473)
                ·
                  refine ⟨14943621639110961666959605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19924828852147948889279473 14943621639110961666959605)
                  ·
                    refine ⟨1400964528666652656277463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14943621639110961666959605 1400964528666652656277463)
                    ·
                      rfl

theorem cell23_8185106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_8185106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185106 prefixEnd_8185106 := by exact prefixLift 8185106
  have htrace : WordTrace (prefixWord ++ tailWord_8185106) baseStart_8185106 baseEnd_8185106 := by
    simpa [prefixWord, tailWord_8185106, baseEnd_8185106] using wordTrace_append hprefix tailTrace_8185106
  have hstable : (prefixWord ++ tailWord_8185106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185106).length < 2 ^ (prefixWord ++ tailWord_8185106).sum := by decide
  have hdescent : baseEnd_8185106 < baseStart_8185106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185112 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_8185112 : Nat := 118140960795 + 8185112 * 2 ^ 59
def prefixEnd_8185112 : Nat := 4983230072969 + 3 ^ 40 * 8185112 * 2
def baseEnd_8185112 : Nat := 4202896666883884945357361

theorem tailTrace_8185112 : CollatzResearch.WordTrace tailWord_8185112 prefixEnd_8185112 4202896666883884945357361 := by
  unfold tailWord_8185112
  simp only [CollatzResearch.WordTrace]
  refine ⟨149267780161372302340870795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199023706881829736454494393 149267780161372302340870795)
  ·
    refine ⟨223901670242058453511306193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149267780161372302340870795 223901670242058453511306193)
    ·
      refine ⟨167926252681543840133479645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223901670242058453511306193 167926252681543840133479645)
      ·
        refine ⟨62972344755578940050054867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167926252681543840133479645 62972344755578940050054867)
        ·
          refine ⟨94458517133368410075082301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62972344755578940050054867 94458517133368410075082301)
          ·
            refine ⟨35421943925013153778155863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94458517133368410075082301 35421943925013153778155863)
            ·
              refine ⟨53132915887519730667233795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35421943925013153778155863 53132915887519730667233795)
              ·
                refine ⟨79699373831279596000850693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53132915887519730667233795 79699373831279596000850693)
                ·
                  refine ⟨14943632593364924250159505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79699373831279596000850693 14943632593364924250159505)
                  ·
                    refine ⟨11207724445023693187619629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14943632593364924250159505 11207724445023693187619629)
                    ·
                      refine ⟨4202896666883884945357361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207724445023693187619629 4202896666883884945357361)
                      ·
                        rfl

theorem cell23_8185112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_8185112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185112 prefixEnd_8185112 := by exact prefixLift 8185112
  have htrace : WordTrace (prefixWord ++ tailWord_8185112) baseStart_8185112 baseEnd_8185112 := by
    simpa [prefixWord, tailWord_8185112, baseEnd_8185112] using wordTrace_append hprefix tailTrace_8185112
  have hstable : (prefixWord ++ tailWord_8185112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185112).length < 2 ^ (prefixWord ++ tailWord_8185112).sum := by decide
  have hdescent : baseEnd_8185112 < baseStart_8185112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185115 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 6]
def baseStart_8185115 : Nat := 118140960795 + 8185115 * 2 ^ 59
def prefixEnd_8185115 : Nat := 4983230072969 + 3 ^ 40 * 8185115 * 2
def baseEnd_8185115 : Nat := 466988689702872048179983

theorem tailTrace_8185115 : CollatzResearch.WordTrace tailWord_8185115 prefixEnd_8185115 466988689702872048179983 := by
  unfold tailWord_8185115
  simp only [CollatzResearch.WordTrace]
  refine ⟨298535669741733736194100799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199023779827822490796067199 298535669741733736194100799)
  ·
    refine ⟨447803504612600604291151199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298535669741733736194100799 447803504612600604291151199)
    ·
      refine ⟨671705256918900906436726799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447803504612600604291151199 671705256918900906436726799)
      ·
        refine ⟨1007557885378351359655090199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671705256918900906436726799 1007557885378351359655090199)
        ·
          refine ⟨1511336828067527039482635299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007557885378351359655090199 1511336828067527039482635299)
          ·
            refine ⟨2267005242101290559223952949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511336828067527039482635299 2267005242101290559223952949)
            ·
              refine ⟨212531741446995989927245589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2267005242101290559223952949 212531741446995989927245589)
              ·
                refine ⟨9962425380327937027839637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212531741446995989927245589 9962425380327937027839637)
                ·
                  refine ⟨466988689702872048179983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9962425380327937027839637 466988689702872048179983)
                  ·
                    rfl

theorem cell23_8185115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 6].length) (baseStart_8185115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185115 prefixEnd_8185115 := by exact prefixLift 8185115
  have htrace : WordTrace (prefixWord ++ tailWord_8185115) baseStart_8185115 baseEnd_8185115 := by
    simpa [prefixWord, tailWord_8185115, baseEnd_8185115] using wordTrace_append hprefix tailTrace_8185115
  have hstable : (prefixWord ++ tailWord_8185115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185115).length < 2 ^ (prefixWord ++ tailWord_8185115).sum := by decide
  have hdescent : baseEnd_8185115 < baseStart_8185115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185162 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_8185162 : Nat := 118140960795 + 8185162 * 2 ^ 59
def prefixEnd_8185162 : Nat := 4983230072969 + 3 ^ 40 * 8185162 * 2
def baseEnd_8185162 : Nat := 1400974113638869916577377

theorem tailTrace_8185162 : CollatzResearch.WordTrace tailWord_8185162 prefixEnd_8185162 1400974113638869916577377 := by
  unfold tailWord_8185162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74634345993140865805265435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199024922648375642147374493 74634345993140865805265435)
  ·
    refine ⟨111951518989711298707898153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74634345993140865805265435 111951518989711298707898153)
    ·
      refine ⟨83963639242283474030923615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111951518989711298707898153 83963639242283474030923615)
      ·
        refine ⟨125945458863425211046385423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83963639242283474030923615 125945458863425211046385423)
        ·
          refine ⟨188918188295137816569578135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125945458863425211046385423 188918188295137816569578135)
          ·
            refine ⟨283377282442706724854367203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188918188295137816569578135 283377282442706724854367203)
            ·
              refine ⟨425065923664060087281550805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283377282442706724854367203 425065923664060087281550805)
              ·
                refine ⟨9962482585876408295661347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 425065923664060087281550805 9962482585876408295661347)
                ·
                  refine ⟨14943723878814612443492021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9962482585876408295661347 14943723878814612443492021)
                  ·
                    refine ⟨1400974113638869916577377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14943723878814612443492021 1400974113638869916577377)
                    ·
                      rfl

theorem cell23_8185162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_8185162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185162 prefixEnd_8185162 := by exact prefixLift 8185162
  have htrace : WordTrace (prefixWord ++ tailWord_8185162) baseStart_8185162 baseEnd_8185162 := by
    simpa [prefixWord, tailWord_8185162, baseEnd_8185162] using wordTrace_append hprefix tailTrace_8185162
  have hstable : (prefixWord ++ tailWord_8185162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185162).length < 2 ^ (prefixWord ++ tailWord_8185162).sum := by decide
  have hdescent : baseEnd_8185162 < baseStart_8185162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185169 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 2, 3, 2]
def baseStart_8185169 : Nat := 118140960795 + 8185169 * 2 ^ 59
def prefixEnd_8185169 : Nat := 4983230072969 + 3 ^ 40 * 8185169 * 2
def baseEnd_8185169 : Nat := 4202925935281191222344599

theorem tailTrace_8185169 : CollatzResearch.WordTrace tailWord_8185169 prefixEnd_8185169 4202925935281191222344599 := by
  unfold tailWord_8185169
  simp only [CollatzResearch.WordTrace]
  refine ⟨298537639283538103416566561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199025092855692068944377707 298537639283538103416566561)
  ·
    refine ⟨223903229462653577562424921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298537639283538103416566561 223903229462653577562424921)
    ·
      refine ⟨167927422096990183171818691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223903229462653577562424921 167927422096990183171818691)
      ·
        refine ⟨251891133145485274757728037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167927422096990183171818691 251891133145485274757728037)
        ·
          refine ⟨47229587464778489017074007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251891133145485274757728037 47229587464778489017074007)
          ·
            refine ⟨70844381197167733525611011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47229587464778489017074007 70844381197167733525611011)
            ·
              refine ⟨106266571795751600288416517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70844381197167733525611011 106266571795751600288416517)
              ·
                refine ⟨19924982211703425054078097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106266571795751600288416517 19924982211703425054078097)
                ·
                  refine ⟨14943736658777568790558573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19924982211703425054078097 14943736658777568790558573)
                  ·
                    refine ⟨5603901247041588296459465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14943736658777568790558573 5603901247041588296459465)
                    ·
                      refine ⟨4202925935281191222344599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5603901247041588296459465 4202925935281191222344599)
                      ·
                        rfl

theorem cell23_8185169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_8185169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185169 prefixEnd_8185169 := by exact prefixLift 8185169
  have htrace : WordTrace (prefixWord ++ tailWord_8185169) baseStart_8185169 baseEnd_8185169 := by
    simpa [prefixWord, tailWord_8185169, baseEnd_8185169] using wordTrace_append hprefix tailTrace_8185169
  have hstable : (prefixWord ++ tailWord_8185169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185169).length < 2 ^ (prefixWord ++ tailWord_8185169).sum := by decide
  have hdescent : baseEnd_8185169 < baseStart_8185169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185176 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 1, 1, 3]
def baseStart_8185176 : Nat := 118140960795 + 8185176 * 2 ^ 59
def prefixEnd_8185176 : Nat := 4983230072969 + 3 ^ 40 * 8185176 * 2
def baseEnd_8185176 : Nat := 4202929529645772694957067

theorem tailTrace_8185176 : CollatzResearch.WordTrace tailWord_8185176 prefixEnd_8185176 4202929529645772694957067 := by
  unfold tailWord_8185176
  simp only [CollatzResearch.WordTrace]
  refine ⟨149268947297256371806035691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199025263063008495741380921 149268947297256371806035691)
  ·
    refine ⟨223903420945884557709053537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149268947297256371806035691 223903420945884557709053537)
    ·
      refine ⟨167927565709413418281790153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223903420945884557709053537 167927565709413418281790153)
      ·
        refine ⟨125945674282060063711342615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167927565709413418281790153 125945674282060063711342615)
        ·
          refine ⟨188918511423090095567013923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125945674282060063711342615 188918511423090095567013923)
          ·
            refine ⟨283377767134635143350520885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188918511423090095567013923 283377767134635143350520885)
            ·
              refine ⟨26566665668872044689111333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283377767134635143350520885 26566665668872044689111333)
              ·
                refine ⟨4981249812913508379208375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26566665668872044689111333 4981249812913508379208375)
                ·
                  refine ⟨7471874719370262568812563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981249812913508379208375 7471874719370262568812563)
                  ·
                    refine ⟨11207812079055393853218845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471874719370262568812563 11207812079055393853218845)
                    ·
                      refine ⟨4202929529645772694957067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11207812079055393853218845 4202929529645772694957067)
                      ·
                        rfl

theorem cell23_8185176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_8185176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185176 prefixEnd_8185176 := by exact prefixLift 8185176
  have htrace : WordTrace (prefixWord ++ tailWord_8185176) baseStart_8185176 baseEnd_8185176 := by
    simpa [prefixWord, tailWord_8185176, baseEnd_8185176] using wordTrace_append hprefix tailTrace_8185176
  have hstable : (prefixWord ++ tailWord_8185176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185176).length < 2 ^ (prefixWord ++ tailWord_8185176).sum := by decide
  have hdescent : baseEnd_8185176 < baseStart_8185176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185212 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_8185212 : Nat := 118140960795 + 8185212 * 2 ^ 59
def prefixEnd_8185212 : Nat := 4983230072969 + 3 ^ 40 * 8185212 * 2
def baseEnd_8185212 : Nat := 4202948014949334554106901

theorem tailTrace_8185212 : CollatzResearch.WordTrace tailWord_8185212 prefixEnd_8185212 4202948014949334554106901 := by
  unfold tailWord_8185212
  simp only [CollatzResearch.WordTrace]
  refine ⟨149269603811191160880190945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199026138414921547840254593 149269603811191160880190945)
  ·
    refine ⟨111952202858393370660143209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149269603811191160880190945 111952202858393370660143209)
    ·
      refine ⟨83964152143795027995107407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111952202858393370660143209 83964152143795027995107407)
      ·
        refine ⟨125946228215692541992661111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83964152143795027995107407 125946228215692541992661111)
        ·
          refine ⟨188919342323538812988991667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125946228215692541992661111 188919342323538812988991667)
          ·
            refine ⟨283379013485308219483487501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188919342323538812988991667 283379013485308219483487501)
            ·
              refine ⟨106267130056990582306307813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283379013485308219483487501 106267130056990582306307813)
              ·
                refine ⟨19925086885685734182432715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106267130056990582306307813 19925086885685734182432715)
                ·
                  refine ⟨29887630328528601273649073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19925086885685734182432715 29887630328528601273649073)
                  ·
                    refine ⟨22415722746396450955236805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29887630328528601273649073 22415722746396450955236805)
                    ·
                      refine ⟨4202948014949334554106901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22415722746396450955236805 4202948014949334554106901)
                      ·
                        rfl

theorem cell23_8185212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_8185212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185212 prefixEnd_8185212 := by exact prefixLift 8185212
  have htrace : WordTrace (prefixWord ++ tailWord_8185212) baseStart_8185212 baseEnd_8185212 := by
    simpa [prefixWord, tailWord_8185212, baseEnd_8185212] using wordTrace_append hprefix tailTrace_8185212
  have hstable : (prefixWord ++ tailWord_8185212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185212).length < 2 ^ (prefixWord ++ tailWord_8185212).sum := by decide
  have hdescent : baseEnd_8185212 < baseStart_8185212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185246 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_8185246 : Nat := 118140960795 + 8185246 * 2 ^ 59
def prefixEnd_8185246 : Nat := 4983230072969 + 3 ^ 40 * 8185246 * 2
def baseEnd_8185246 : Nat := 4202965473291587421081745

theorem tailTrace_8185246 : CollatzResearch.WordTrace tailWord_8185246 prefixEnd_8185246 4202965473291587421081745 := by
  unfold tailWord_8185246
  simp only [CollatzResearch.WordTrace]
  refine ⟨37317555963032393195889949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199026965136172763711413061 37317555963032393195889949)
  ·
    refine ⟨13994083486137147448458731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37317555963032393195889949 13994083486137147448458731)
    ·
      refine ⟨20991125229205721172688097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13994083486137147448458731 20991125229205721172688097)
      ·
        refine ⟨15743343921904290879516073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20991125229205721172688097 15743343921904290879516073)
        ·
          refine ⟨11807507941428218159637055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15743343921904290879516073 11807507941428218159637055)
          ·
            refine ⟨17711261912142327239455583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807507941428218159637055 17711261912142327239455583)
            ·
              refine ⟨26566892868213490859183375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711261912142327239455583 26566892868213490859183375)
              ·
                refine ⟨39850339302320236288775063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26566892868213490859183375 39850339302320236288775063)
                ·
                  refine ⟨59775508953480354433162595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39850339302320236288775063 59775508953480354433162595)
                  ·
                    refine ⟨89663263430220531649743893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59775508953480354433162595 89663263430220531649743893)
                    ·
                      refine ⟨4202965473291587421081745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89663263430220531649743893 4202965473291587421081745)
                      ·
                        rfl

theorem cell23_8185246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_8185246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185246 prefixEnd_8185246 := by exact prefixLift 8185246
  have htrace : WordTrace (prefixWord ++ tailWord_8185246) baseStart_8185246 baseEnd_8185246 := by
    simpa [prefixWord, tailWord_8185246, baseEnd_8185246] using wordTrace_append hprefix tailTrace_8185246
  have hstable : (prefixWord ++ tailWord_8185246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185246).length < 2 ^ (prefixWord ++ tailWord_8185246).sum := by decide
  have hdescent : baseEnd_8185246 < baseStart_8185246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185309 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_8185309 : Nat := 118140960795 + 8185309 * 2 ^ 59
def prefixEnd_8185309 : Nat := 4983230072969 + 3 ^ 40 * 8185309 * 2
def baseEnd_8185309 : Nat := 4202997822572820674593955

theorem tailTrace_8185309 : CollatzResearch.WordTrace tailWord_8185309 prefixEnd_8185309 4202997822572820674593955 := by
  unfold tailWord_8185309
  simp only [CollatzResearch.WordTrace]
  refine ⟨298542745503030907326662981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199028497002020604884441987 298542745503030907326662981)
  ·
    refine ⟨55976764781818295123749309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298542745503030907326662981 55976764781818295123749309)
    ·
      refine ⟨20991286793181860671405991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55976764781818295123749309 20991286793181860671405991)
      ·
        refine ⟨31486930189772791007108987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20991286793181860671405991 31486930189772791007108987)
        ·
          refine ⟨47230395284659186510663481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31486930189772791007108987 47230395284659186510663481)
          ·
            refine ⟨35422796463494389882997611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47230395284659186510663481 35422796463494389882997611)
            ·
              refine ⟨53134194695241584824496417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35422796463494389882997611 53134194695241584824496417)
              ·
                refine ⟨39850646021431188618372313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53134194695241584824496417 39850646021431188618372313)
                ·
                  refine ⟨29887984516073391463779235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39850646021431188618372313 29887984516073391463779235)
                  ·
                    refine ⟨44831976774110087195668853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29887984516073391463779235 44831976774110087195668853)
                    ·
                      refine ⟨4202997822572820674593955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44831976774110087195668853 4202997822572820674593955)
                      ·
                        rfl

theorem cell23_8185309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_8185309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185309 prefixEnd_8185309 := by exact prefixLift 8185309
  have htrace : WordTrace (prefixWord ++ tailWord_8185309) baseStart_8185309 baseEnd_8185309 := by
    simpa [prefixWord, tailWord_8185309, baseEnd_8185309] using wordTrace_append hprefix tailTrace_8185309
  have hstable : (prefixWord ++ tailWord_8185309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185309).length < 2 ^ (prefixWord ++ tailWord_8185309).sum := by decide
  have hdescent : baseEnd_8185309 < baseStart_8185309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185350 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_8185350 : Nat := 118140960795 + 8185350 * 2 ^ 59
def prefixEnd_8185350 : Nat := 4983230072969 + 3 ^ 40 * 8185350 * 2
def baseEnd_8185350 : Nat := 1401006291759885004727089

theorem tailTrace_8185350 : CollatzResearch.WordTrace tailWord_8185350 prefixEnd_8185350 1401006291759885004727089 := by
  unfold tailWord_8185350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329507527996324104028297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199029493930588247552603669 9329507527996324104028297)
  ·
    refine ⟨6997130645997243078021223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9329507527996324104028297 6997130645997243078021223)
    ·
      refine ⟨10495695968995864617031835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997130645997243078021223 10495695968995864617031835)
      ·
        refine ⟨15743543953493796925547753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495695968995864617031835 15743543953493796925547753)
        ·
          refine ⟨11807657965120347694160815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15743543953493796925547753 11807657965120347694160815)
          ·
            refine ⟨17711486947680521541241223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807657965120347694160815 17711486947680521541241223)
            ·
              refine ⟨26567230421520782311861835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711486947680521541241223 26567230421520782311861835)
              ·
                refine ⟨39850845632281173467792753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26567230421520782311861835 39850845632281173467792753)
                ·
                  refine ⟨29888134224210880100844565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39850845632281173467792753 29888134224210880100844565)
                  ·
                    refine ⟨1401006291759885004727089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29888134224210880100844565 1401006291759885004727089)
                    ·
                      rfl

theorem cell23_8185350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_8185350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185350 prefixEnd_8185350 := by exact prefixLift 8185350
  have htrace : WordTrace (prefixWord ++ tailWord_8185350) baseStart_8185350 baseEnd_8185350 := by
    simpa [prefixWord, tailWord_8185350, baseEnd_8185350] using wordTrace_append hprefix tailTrace_8185350
  have hstable : (prefixWord ++ tailWord_8185350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185350).length < 2 ^ (prefixWord ++ tailWord_8185350).sum := by decide
  have hdescent : baseEnd_8185350 < baseStart_8185350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185356 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_8185356 : Nat := 118140960795 + 8185356 * 2 ^ 59
def prefixEnd_8185356 : Nat := 4983230072969 + 3 ^ 40 * 8185356 * 2
def baseEnd_8185356 : Nat := 4203021956163581990706239

theorem tailTrace_8185356 : CollatzResearch.WordTrace tailWord_8185356 prefixEnd_8185356 4203021956163581990706239 := by
  unfold tailWord_8185356
  simp only [CollatzResearch.WordTrace]
  refine ⟨149272229866930317176811961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199029639822573756235749281 149272229866930317176811961)
  ·
    refine ⟨111954172400197737882608971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149272229866930317176811961 111954172400197737882608971)
    ·
      refine ⟨167931258600296606823913457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111954172400197737882608971 167931258600296606823913457)
      ·
        refine ⟨125948443950222455117935093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167931258600296606823913457 125948443950222455117935093)
        ·
          refine ⟨11807666620333355167306415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125948443950222455117935093 11807666620333355167306415)
          ·
            refine ⟨17711499930500032750959623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807666620333355167306415 17711499930500032750959623)
            ·
              refine ⟨26567249895750049126439435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711499930500032750959623 26567249895750049126439435)
              ·
                refine ⟨39850874843625073689659153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26567249895750049126439435 39850874843625073689659153)
                ·
                  refine ⟨29888156132718805267244365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39850874843625073689659153 29888156132718805267244365)
                  ·
                    refine ⟨11208058549769551975216637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29888156132718805267244365 11208058549769551975216637)
                    ·
                      refine ⟨4203021956163581990706239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11208058549769551975216637 4203021956163581990706239)
                      ·
                        rfl

theorem cell23_8185356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_8185356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185356 prefixEnd_8185356 := by exact prefixLift 8185356
  have htrace : WordTrace (prefixWord ++ tailWord_8185356) baseStart_8185356 baseEnd_8185356 := by
    simpa [prefixWord, tailWord_8185356, baseEnd_8185356] using wordTrace_append hprefix tailTrace_8185356
  have hstable : (prefixWord ++ tailWord_8185356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185356).length < 2 ^ (prefixWord ++ tailWord_8185356).sum := by decide
  have hdescent : baseEnd_8185356 < baseStart_8185356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185357 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_8185357 : Nat := 118140960795 + 8185357 * 2 ^ 59
def prefixEnd_8185357 : Nat := 4983230072969 + 3 ^ 40 * 8185357 * 2
def baseEnd_8185357 : Nat := 4203022469644236486793735

theorem tailTrace_8185357 : CollatzResearch.WordTrace tailWord_8185357 prefixEnd_8185357 4203022469644236486793735 := by
  unfold tailWord_8185357
  simp only [CollatzResearch.WordTrace]
  refine ⟨298544496206857011524410325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199029664137904674349606883 298544496206857011524410325)
  ·
    refine ⟨6997136629848211207603367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 298544496206857011524410325 6997136629848211207603367)
    ·
      refine ⟨10495704944772316811405051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997136629848211207603367 10495704944772316811405051)
      ·
        refine ⟨15743557417158475217107577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495704944772316811405051 15743557417158475217107577)
        ·
          refine ⟨11807668062868856412830683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15743557417158475217107577 11807668062868856412830683)
          ·
            refine ⟨17711502094303284619246025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807668062868856412830683 17711502094303284619246025)
            ·
              refine ⟨13283626570727463464434519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17711502094303284619246025 13283626570727463464434519)
              ·
                refine ⟨19925439856091195196651779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13283626570727463464434519 19925439856091195196651779)
                ·
                  refine ⟨29888159784136792794977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19925439856091195196651779 29888159784136792794977669)
                  ·
                    refine ⟨5604029959525648649058313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29888159784136792794977669 5604029959525648649058313)
                    ·
                      refine ⟨4203022469644236486793735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604029959525648649058313 4203022469644236486793735)
                      ·
                        rfl

theorem cell23_8185357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_8185357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185357 prefixEnd_8185357 := by exact prefixLift 8185357
  have htrace : WordTrace (prefixWord ++ tailWord_8185357) baseStart_8185357 baseEnd_8185357 := by
    simpa [prefixWord, tailWord_8185357, baseEnd_8185357] using wordTrace_append hprefix tailTrace_8185357
  have hstable : (prefixWord ++ tailWord_8185357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185357).length < 2 ^ (prefixWord ++ tailWord_8185357).sum := by decide
  have hdescent : baseEnd_8185357 < baseStart_8185357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185376 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 2, 5]
def baseStart_8185376 : Nat := 118140960795 + 8185376 * 2 ^ 59
def prefixEnd_8185376 : Nat := 4983230072969 + 3 ^ 40 * 8185376 * 2
def baseEnd_8185376 : Nat := 1401010741925557304152049

theorem tailTrace_8185376 : CollatzResearch.WordTrace tailWord_8185376 prefixEnd_8185376 1401010741925557304152049 := by
  unfold tailWord_8185376
  simp only [CollatzResearch.WordTrace]
  refine ⟨149272594596894088884675991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199030126129192118512901321 149272594596894088884675991)
  ·
    refine ⟨223908891895341133327013987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149272594596894088884675991 223908891895341133327013987)
    ·
      refine ⟨335863337843011699990520981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223908891895341133327013987 335863337843011699990520981)
      ·
        refine ⟨15743593961391173437055671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335863337843011699990520981 15743593961391173437055671)
        ·
          refine ⟨23615390942086760155583507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15743593961391173437055671 23615390942086760155583507)
          ·
            refine ⟨35423086413130140233375261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23615390942086760155583507 35423086413130140233375261)
            ·
              refine ⟨13283657404923802587515723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35423086413130140233375261 13283657404923802587515723)
              ·
                refine ⟨19925486107385703881273585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13283657404923802587515723 19925486107385703881273585)
                ·
                  refine ⟨14944114580539277910955189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19925486107385703881273585 14944114580539277910955189)
                  ·
                    refine ⟨1401010741925557304152049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14944114580539277910955189 1401010741925557304152049)
                    ·
                      rfl

theorem cell23_8185376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_8185376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185376 prefixEnd_8185376 := by exact prefixLift 8185376
  have htrace : WordTrace (prefixWord ++ tailWord_8185376) baseStart_8185376 baseEnd_8185376 := by
    simpa [prefixWord, tailWord_8185376, baseEnd_8185376] using wordTrace_append hprefix tailTrace_8185376
  have hstable : (prefixWord ++ tailWord_8185376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185376).length < 2 ^ (prefixWord ++ tailWord_8185376).sum := by decide
  have hdescent : baseEnd_8185376 < baseStart_8185376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185409 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_8185409 : Nat := 118140960795 + 8185409 * 2 ^ 59
def prefixEnd_8185409 : Nat := 4983230072969 + 3 ^ 40 * 8185409 * 2
def baseEnd_8185409 : Nat := 4203049170638270283343495

theorem tailTrace_8185409 : CollatzResearch.WordTrace tailWord_8185409 prefixEnd_8185409 4203049170638270283343495 := by
  unfold tailWord_8185409
  simp only [CollatzResearch.WordTrace]
  refine ⟨298546392802668624405303281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199030928535112416270202187 298546392802668624405303281)
  ·
    refine ⟨223909794602001468303977461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298546392802668624405303281 223909794602001468303977461)
    ·
      refine ⟨20991543243937637653497887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223909794602001468303977461 20991543243937637653497887)
      ·
        refine ⟨31487314865906456480246831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20991543243937637653497887 31487314865906456480246831)
        ·
          refine ⟨47230972298859684720370247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31487314865906456480246831 47230972298859684720370247)
          ·
            refine ⟨70846458448289527080555371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47230972298859684720370247 70846458448289527080555371)
            ·
              refine ⟨106269687672434290620833057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70846458448289527080555371 106269687672434290620833057)
              ·
                refine ⟨79702265754325717965624793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106269687672434290620833057 79702265754325717965624793)
                ·
                  refine ⟨59776699315744288474218595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79702265754325717965624793 59776699315744288474218595)
                  ·
                    refine ⟨89665048973616432711327893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59776699315744288474218595 89665048973616432711327893)
                    ·
                      refine ⟨4203049170638270283343495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89665048973616432711327893 4203049170638270283343495)
                      ·
                        rfl

theorem cell23_8185409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_8185409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185409 prefixEnd_8185409 := by exact prefixLift 8185409
  have htrace : WordTrace (prefixWord ++ tailWord_8185409) baseStart_8185409 baseEnd_8185409 := by
    simpa [prefixWord, tailWord_8185409, baseEnd_8185409] using wordTrace_append hprefix tailTrace_8185409
  have hstable : (prefixWord ++ tailWord_8185409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185409).length < 2 ^ (prefixWord ++ tailWord_8185409).sum := by decide
  have hdescent : baseEnd_8185409 < baseStart_8185409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185429 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_8185429 : Nat := 118140960795 + 8185429 * 2 ^ 59
def prefixEnd_8185429 : Nat := 4983230072969 + 3 ^ 40 * 8185429 * 2
def baseEnd_8185429 : Nat := 4203059440251360205093403

theorem tailTrace_8185429 : CollatzResearch.WordTrace tailWord_8185429 prefixEnd_8185429 4203059440251360205093403 := by
  unfold tailWord_8185429
  simp only [CollatzResearch.WordTrace]
  refine ⟨298547122262596167821031341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199031414841730778547354227 298547122262596167821031341)
  ·
    refine ⟨111955170848473562932886753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298547122262596167821031341 111955170848473562932886753)
    ·
      refine ⟨83966378136355172199665065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111955170848473562932886753 83966378136355172199665065)
      ·
        refine ⟨62974783602266379149748799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83966378136355172199665065 62974783602266379149748799)
        ·
          refine ⟨94462175403399568724623199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62974783602266379149748799 94462175403399568724623199)
          ·
            refine ⟨141693263105099353086934799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94462175403399568724623199 141693263105099353086934799)
            ·
              refine ⟨212539894657649029630402199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141693263105099353086934799 212539894657649029630402199)
              ·
                refine ⟨318809841986473544445603299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212539894657649029630402199 318809841986473544445603299)
                ·
                  refine ⟨478214762979710316668404949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318809841986473544445603299 478214762979710316668404949)
                  ·
                    refine ⟨11208158507336960546915741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 478214762979710316668404949 11208158507336960546915741)
                    ·
                      refine ⟨4203059440251360205093403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11208158507336960546915741 4203059440251360205093403)
                      ·
                        rfl

theorem cell23_8185429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_8185429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185429 prefixEnd_8185429 := by exact prefixLift 8185429
  have htrace : WordTrace (prefixWord ++ tailWord_8185429) baseStart_8185429 baseEnd_8185429 := by
    simpa [prefixWord, tailWord_8185429, baseEnd_8185429] using wordTrace_append hprefix tailTrace_8185429
  have hstable : (prefixWord ++ tailWord_8185429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185429).length < 2 ^ (prefixWord ++ tailWord_8185429).sum := by decide
  have hdescent : baseEnd_8185429 < baseStart_8185429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185496 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_8185496 : Nat := 118140960795 + 8185496 * 2 ^ 59
def prefixEnd_8185496 : Nat := 4983230072969 + 3 ^ 40 * 8185496 * 2
def baseEnd_8185496 : Nat := 1401031281151737147651865

theorem tailTrace_8185496 : CollatzResearch.WordTrace tailWord_8185496 prefixEnd_8185496 1401031281151737147651865 := by
  unfold tailWord_8185496
  simp only [CollatzResearch.WordTrace]
  refine ⟨149274782976676719131860171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199033043968902292175813561 149274782976676719131860171)
  ·
    refine ⟨223912174465015078697790257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149274782976676719131860171 223912174465015078697790257)
    ·
      refine ⟨167934130848761309023342693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223912174465015078697790257 167934130848761309023342693)
      ·
        refine ⟨31487649534142745441876755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167934130848761309023342693 31487649534142745441876755)
        ·
          refine ⟨47231474301214118162815133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31487649534142745441876755 47231474301214118162815133)
          ·
            refine ⟨17711802862955294311055675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47231474301214118162815133 17711802862955294311055675)
            ·
              refine ⟨26567704294432941466583513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711802862955294311055675 26567704294432941466583513)
              ·
                refine ⟨19925778220824706099937635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26567704294432941466583513 19925778220824706099937635)
                ·
                  refine ⟨29888667331237059149906453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19925778220824706099937635 29888667331237059149906453)
                  ·
                    refine ⟨1401031281151737147651865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29888667331237059149906453 1401031281151737147651865)
                    ·
                      rfl

theorem cell23_8185496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_8185496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185496 prefixEnd_8185496 := by exact prefixLift 8185496
  have htrace : WordTrace (prefixWord ++ tailWord_8185496) baseStart_8185496 baseEnd_8185496 := by
    simpa [prefixWord, tailWord_8185496, baseEnd_8185496] using wordTrace_append hprefix tailTrace_8185496
  have hstable : (prefixWord ++ tailWord_8185496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185496).length < 2 ^ (prefixWord ++ tailWord_8185496).sum := by decide
  have hdescent : baseEnd_8185496 < baseStart_8185496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185500 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_8185500 : Nat := 118140960795 + 8185500 * 2 ^ 59
def prefixEnd_8185500 : Nat := 4983230072969 + 3 ^ 40 * 8185500 * 2
def baseEnd_8185500 : Nat := 1401031965792609809101859

theorem tailTrace_8185500 : CollatzResearch.WordTrace tailWord_8185500 prefixEnd_8185500 1401031965792609809101859 := by
  unfold tailWord_8185500
  simp only [CollatzResearch.WordTrace]
  refine ⟨149274855922669473473432977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199033141230225964631243969 149274855922669473473432977)
  ·
    refine ⟨111956141942002105105074733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149274855922669473473432977 111956141942002105105074733)
    ·
      refine ⟨41983553228250789414403025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111956141942002105105074733 41983553228250789414403025)
      ·
        refine ⟨31487664921188092060802269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41983553228250789414403025 31487664921188092060802269)
        ·
          refine ⟨11807874345445534522800851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31487664921188092060802269 11807874345445534522800851)
          ·
            refine ⟨17711811518168301784201277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807874345445534522800851 17711811518168301784201277)
            ·
              refine ⟨6641929319313113169075479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17711811518168301784201277 6641929319313113169075479)
              ·
                refine ⟨9962893978969669753613219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641929319313113169075479 9962893978969669753613219)
                ·
                  refine ⟨14944340968454504630419829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9962893978969669753613219 14944340968454504630419829)
                  ·
                    refine ⟨1401031965792609809101859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14944340968454504630419829 1401031965792609809101859)
                    ·
                      rfl

theorem cell23_8185500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_8185500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185500 prefixEnd_8185500 := by exact prefixLift 8185500
  have htrace : WordTrace (prefixWord ++ tailWord_8185500) baseStart_8185500 baseEnd_8185500 := by
    simpa [prefixWord, tailWord_8185500, baseEnd_8185500] using wordTrace_append hprefix tailTrace_8185500
  have hstable : (prefixWord ++ tailWord_8185500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185500).length < 2 ^ (prefixWord ++ tailWord_8185500).sum := by decide
  have hdescent : baseEnd_8185500 < baseStart_8185500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185529 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_8185529 : Nat := 118140960795 + 8185529 * 2 ^ 59
def prefixEnd_8185529 : Nat := 4983230072969 + 3 ^ 40 * 8185529 * 2
def baseEnd_8185529 : Nat := 4203110788316809813842943

theorem tailTrace_8185529 : CollatzResearch.WordTrace tailWord_8185529 prefixEnd_8185529 4203110788316809813842943 := by
  unfold tailWord_8185529
  simp only [CollatzResearch.WordTrace]
  refine ⟨298550769562233884899671641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199033846374822589933114427 298550769562233884899671641)
  ·
    refine ⟨223913077171675413674753731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298550769562233884899671641 223913077171675413674753731)
    ·
      refine ⟨335869615757513120512130597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223913077171675413674753731 335869615757513120512130597)
      ·
        refine ⟨62975552954533710096024487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335869615757513120512130597 62975552954533710096024487)
        ·
          refine ⟨94463329431800565144036731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62975552954533710096024487 94463329431800565144036731)
          ·
            refine ⟨141694994147700847716055097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94463329431800565144036731 141694994147700847716055097)
            ·
              refine ⟨106271245610775635787041323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141694994147700847716055097 106271245610775635787041323)
              ·
                refine ⟨159406868416163453680561985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106271245610775635787041323 159406868416163453680561985)
                ·
                  refine ⟨119555151312122590260421489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159406868416163453680561985 119555151312122590260421489)
                  ·
                    refine ⟨89666363484091942695316117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119555151312122590260421489 89666363484091942695316117)
                    ·
                      refine ⟨4203110788316809813842943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89666363484091942695316117 4203110788316809813842943)
                      ·
                        rfl

theorem cell23_8185529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_8185529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185529 prefixEnd_8185529 := by exact prefixLift 8185529
  have htrace : WordTrace (prefixWord ++ tailWord_8185529) baseStart_8185529 baseEnd_8185529 := by
    simpa [prefixWord, tailWord_8185529, baseEnd_8185529] using wordTrace_append hprefix tailTrace_8185529
  have hstable : (prefixWord ++ tailWord_8185529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185529).length < 2 ^ (prefixWord ++ tailWord_8185529).sum := by decide
  have hdescent : baseEnd_8185529 < baseStart_8185529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185554 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_8185554 : Nat := 118140960795 + 8185554 * 2 ^ 59
def prefixEnd_8185554 : Nat := 4983230072969 + 3 ^ 40 * 8185554 * 2
def baseEnd_8185554 : Nat := 4203123625333172216030329

theorem tailTrace_8185554 : CollatzResearch.WordTrace tailWord_8185554 prefixEnd_8185554 4203123625333172216030329 := by
  unfold tailWord_8185554
  simp only [CollatzResearch.WordTrace]
  refine ⟨74637920346785828542332929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199034454258095542779554477 74637920346785828542332929)
  ·
    refine ⟨55978440260089371406749697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74637920346785828542332929 55978440260089371406749697)
    ·
      refine ⟨41983830195067028555062273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55978440260089371406749697 41983830195067028555062273)
      ·
        refine ⟨31487872646300271416296705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41983830195067028555062273 31487872646300271416296705)
        ·
          refine ⟨23615904484725203562222529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31487872646300271416296705 23615904484725203562222529)
          ·
            refine ⟨17711928363543902671666897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23615904484725203562222529 17711928363543902671666897)
            ·
              refine ⟨13283946272657927003750173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17711928363543902671666897 13283946272657927003750173)
              ·
                refine ⟨4981479852246722626406315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13283946272657927003750173 4981479852246722626406315)
                ·
                  refine ⟨7472219778370083939609473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981479852246722626406315 7472219778370083939609473)
                  ·
                    refine ⟨5604164833777562954707105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7472219778370083939609473 5604164833777562954707105)
                    ·
                      refine ⟨4203123625333172216030329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604164833777562954707105 4203123625333172216030329)
                      ·
                        rfl

theorem cell23_8185554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_8185554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185554 prefixEnd_8185554 := by exact prefixLift 8185554
  have htrace : WordTrace (prefixWord ++ tailWord_8185554) baseStart_8185554 baseEnd_8185554 := by
    simpa [prefixWord, tailWord_8185554, baseEnd_8185554] using wordTrace_append hprefix tailTrace_8185554
  have hstable : (prefixWord ++ tailWord_8185554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185554).length < 2 ^ (prefixWord ++ tailWord_8185554).sum := by decide
  have hdescent : baseEnd_8185554 < baseStart_8185554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185564 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_8185564 : Nat := 118140960795 + 8185564 * 2 ^ 59
def prefixEnd_8185564 : Nat := 4983230072969 + 3 ^ 40 * 8185564 * 2
def baseEnd_8185564 : Nat := 1401042920046572392301761

theorem tailTrace_8185564 : CollatzResearch.WordTrace tailWord_8185564 prefixEnd_8185564 1401042920046572392301761 := by
  unfold tailWord_8185564
  simp only [CollatzResearch.WordTrace]
  refine ⟨149276023058553542938597873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199034697411404723918130497 149276023058553542938597873)
  ·
    refine ⟨111957017293915157203948405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149276023058553542938597873 111957017293915157203948405)
    ·
      refine ⟨10495970371304545987870163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111957017293915157203948405 10495970371304545987870163)
      ·
        refine ⟨15743955556956818981805245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495970371304545987870163 15743955556956818981805245)
        ·
          refine ⟨5903983333858807118176967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15743955556956818981805245 5903983333858807118176967)
          ·
            refine ⟨8855975000788210677265451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903983333858807118176967 8855975000788210677265451)
            ·
              refine ⟨13283962501182316015898177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855975000788210677265451 13283962501182316015898177)
              ·
                refine ⟨9962971875886737011923633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13283962501182316015898177 9962971875886737011923633)
                ·
                  refine ⟨7472228906915052758942725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9962971875886737011923633 7472228906915052758942725)
                  ·
                    refine ⟨1401042920046572392301761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472228906915052758942725 1401042920046572392301761)
                    ·
                      rfl

theorem cell23_8185564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_8185564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185564 prefixEnd_8185564 := by exact prefixLift 8185564
  have htrace : WordTrace (prefixWord ++ tailWord_8185564) baseStart_8185564 baseEnd_8185564 := by
    simpa [prefixWord, tailWord_8185564, baseEnd_8185564] using wordTrace_append hprefix tailTrace_8185564
  have hstable : (prefixWord ++ tailWord_8185564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185564).length < 2 ^ (prefixWord ++ tailWord_8185564).sum := by decide
  have hdescent : baseEnd_8185564 < baseStart_8185564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185586 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_8185586 : Nat := 118140960795 + 8185586 * 2 ^ 59
def prefixEnd_8185586 : Nat := 4983230072969 + 3 ^ 40 * 8185586 * 2
def baseEnd_8185586 : Nat := 1401046685571372030276727

theorem tailTrace_8185586 : CollatzResearch.WordTrace tailWord_8185586 prefixEnd_8185586 1401046685571372030276727 := by
  unfold tailWord_8185586
  simp only [CollatzResearch.WordTrace]
  refine ⟨74638212130756845908624153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199035232348684922422997741 74638212130756845908624153)
  ·
    refine ⟨55978659098067634431468115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74638212130756845908624153 55978659098067634431468115)
    ·
      refine ⟨83967988647101451647202173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55978659098067634431468115 83967988647101451647202173)
      ·
        refine ⟨31487995742663044367700815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83967988647101451647202173 31487995742663044367700815)
        ·
          refine ⟨47231993613994566551551223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31487995742663044367700815 47231993613994566551551223)
          ·
            refine ⟨70847990420991849827326835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47231993613994566551551223 70847990420991849827326835)
            ·
              refine ⟨106271985631487774740990253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70847990420991849827326835 106271985631487774740990253)
              ·
                refine ⟨39851994611807915527871345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106271985631487774740990253 39851994611807915527871345)
                ·
                  refine ⟨29888995958855936645903509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39851994611807915527871345 29888995958855936645903509)
                  ·
                    refine ⟨1401046685571372030276727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29888995958855936645903509 1401046685571372030276727)
                    ·
                      rfl

theorem cell23_8185586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_8185586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185586 prefixEnd_8185586 := by exact prefixLift 8185586
  have htrace : WordTrace (prefixWord ++ tailWord_8185586) baseStart_8185586 baseEnd_8185586 := by
    simpa [prefixWord, tailWord_8185586, baseEnd_8185586] using wordTrace_append hprefix tailTrace_8185586
  have hstable : (prefixWord ++ tailWord_8185586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185586).length < 2 ^ (prefixWord ++ tailWord_8185586).sum := by decide
  have hdescent : baseEnd_8185586 < baseStart_8185586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185596 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_8185596 : Nat := 118140960795 + 8185596 * 2 ^ 59
def prefixEnd_8185596 : Nat := 4983230072969 + 3 ^ 40 * 8185596 * 2
def baseEnd_8185596 : Nat := 4203145191520661051705135

theorem tailTrace_8185596 : CollatzResearch.WordTrace tailWord_8185596 prefixEnd_8185596 4203145191520661051705135 := by
  unfold tailWord_8185596
  simp only [CollatzResearch.WordTrace]
  refine ⟨149276606626495577671180321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199035475501994103561573761 149276606626495577671180321)
  ·
    refine ⟨111957454969871683253385241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149276606626495577671180321 111957454969871683253385241)
    ·
      refine ⟨83968091227403762440038931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111957454969871683253385241 83968091227403762440038931)
      ·
        refine ⟨125952136841105643660058397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83968091227403762440038931 125952136841105643660058397)
        ·
          refine ⟨47232051315414616372521899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125952136841105643660058397 47232051315414616372521899)
          ·
            refine ⟨70848076973121924558782849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47232051315414616372521899 70848076973121924558782849)
            ·
              refine ⟨53136057729841443419087137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70848076973121924558782849 53136057729841443419087137)
              ·
                refine ⟨39852043297381082564315353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53136057729841443419087137 39852043297381082564315353)
                ·
                  refine ⟨29889032473035811923236515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39852043297381082564315353 29889032473035811923236515)
                  ·
                    refine ⟨44833548709553717884854773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29889032473035811923236515 44833548709553717884854773)
                    ·
                      refine ⟨4203145191520661051705135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44833548709553717884854773 4203145191520661051705135)
                      ·
                        rfl

theorem cell23_8185596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_8185596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185596 prefixEnd_8185596 := by exact prefixLift 8185596
  have htrace : WordTrace (prefixWord ++ tailWord_8185596) baseStart_8185596 baseEnd_8185596 := by
    simpa [prefixWord, tailWord_8185596, baseEnd_8185596] using wordTrace_append hprefix tailTrace_8185596
  have hstable : (prefixWord ++ tailWord_8185596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185596).length < 2 ^ (prefixWord ++ tailWord_8185596).sum := by decide
  have hdescent : baseEnd_8185596 < baseStart_8185596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185610 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_8185610 : Nat := 118140960795 + 8185610 * 2 ^ 59
def prefixEnd_8185610 : Nat := 4983230072969 + 3 ^ 40 * 8185610 * 2
def baseEnd_8185610 : Nat := 4203152380249823996930071

theorem tailTrace_8185610 : CollatzResearch.WordTrace tailWord_8185610 prefixEnd_8185610 4203152380249823996930071 := by
  unfold tailWord_8185610
  simp only [CollatzResearch.WordTrace]
  refine ⟨74638430968735108933342571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199035815916626957155580189 74638430968735108933342571)
  ·
    refine ⟨111957646453102663400013857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74638430968735108933342571 111957646453102663400013857)
    ·
      refine ⟨83968234839826997550010393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111957646453102663400013857 83968234839826997550010393)
      ·
        refine ⟨62976176129870248162507795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83968234839826997550010393 62976176129870248162507795)
        ·
          refine ⟨94464264194805372243761693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62976176129870248162507795 94464264194805372243761693)
          ·
            refine ⟨35424099073052014591410635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94464264194805372243761693 35424099073052014591410635)
            ·
              refine ⟨53136148609578021887115953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35424099073052014591410635 53136148609578021887115953)
              ·
                refine ⟨39852111457183516415336965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53136148609578021887115953 39852111457183516415336965)
                ·
                  refine ⟨7472270898221909327875681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39852111457183516415336965 7472270898221909327875681)
                  ·
                    refine ⟨5604203173666431995906761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7472270898221909327875681 5604203173666431995906761)
                    ·
                      refine ⟨4203152380249823996930071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604203173666431995906761 4203152380249823996930071)
                      ·
                        rfl

theorem cell23_8185610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_8185610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185610 prefixEnd_8185610 := by exact prefixLift 8185610
  have htrace : WordTrace (prefixWord ++ tailWord_8185610) baseStart_8185610 baseEnd_8185610 := by
    simpa [prefixWord, tailWord_8185610, baseEnd_8185610] using wordTrace_append hprefix tailTrace_8185610
  have hstable : (prefixWord ++ tailWord_8185610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185610).length < 2 ^ (prefixWord ++ tailWord_8185610).sum := by decide
  have hdescent : baseEnd_8185610 < baseStart_8185610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
